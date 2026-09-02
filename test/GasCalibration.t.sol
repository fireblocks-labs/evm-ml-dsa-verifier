// SPDX-License-Identifier: MIT
// FILE: test/GasCalibration.t.sol
//
// OPCODE / PRECOMPILE COST SWEEP for the ML-DSA-44 EVM verifier.
//
// Every measurement here answers one question: "could this opcode or
// precompile do work the verifier currently does, more cheaply?".
// Methodology follows test/ZZZ_calib.t.sol: gasleft() brackets around an
// isolated block, a warm-up call first where account/precompile warmth
// matters, and the memory high-water mark reported so quadratic expansion is
// visible.
//
// Verifier stage profile the numbers below are compared against. These are
// MEASURED, not typed: they are the gasleft() brackets that
// test/PROFILE_E2E.t.sol::test_profile_10_stages prints on every run, and
// `forge test --match-contract PROFILE_E2ETest -vv` reprints them. Re-read
// them there before quoting anything here: a stale figure in this header turns
// every "cheaper than the verifier's own X" sentence below into an argument
// against a verifier this tree does not contain.
//
//   verify(), end to end                   1,231,163
//   SHAKE total  ~400k                     mu 48,152 + sampleInBall 59,629
//                                          + finalHash (7 perms) 291,649,
//                                          i.e. 9 x Keccak-f[1600] @ ~41.6k
//                                          (the helper's own warm staticcall
//                                          measures 41,573 in
//                                          test/ZZZ_fastkeccak170.t.sol)
//   polynomial arithmetic ~661k            nttFw(c) 44,924 + nttFw(z) x4
//                                          180,745 + matvec 4 rows 220,915
//                                          + nttInv x4 214,448
//   unpackZ + norm check                   77,364
//   UseHint + w1Encode                     72,048
//   decode h (84 B)                        8,147
//   pk size check                          4,784
//   glue + memory (residual)               1,563
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";

contract GasCalibrationTest is Test {
    // scratch sinks so nothing is optimised away
    uint256 sink;
    bytes32 hsink;

    function _log(string memory k, uint256 v) internal pure {
        console.log(k, v);
    }

    // =======================================================================
    // 1. ARITHMETIC / BITWISE BASELINE — the ops the SWAR kernels are made of
    // =======================================================================
    function test_cal_01_alu_baseline() public {
        uint256 g0;
        uint256 acc = 7;

        // straight-line 64x of each op, harness-subtracted against an empty
        // bracket, so the per-op cost is (measured - empty) / 64.
        g0 = gasleft();
        assembly ("memory-safe") {
            acc := acc
        }
        uint256 empty = g0 - gasleft();
        _log("empty_bracket:", empty);

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 64) { i := add(i, 1) } { x := add(x, 1) }
            acc := x
        }
        _log("loop64_add(loop tax visible):", g0 - gasleft());

        // MULMOD at 256-bit width vs MUL: the "8 gas at any width" claim
        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            let m := sub(shl(192, 1), 237) // P = 2^192 - 237
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := mulmod(x, 3, m) }
            acc := x
        }
        _log("loop256_mulmod_2^192:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := mul(x, 3) }
            acc := x
        }
        _log("loop256_mul:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := addmod(x, 3, 8380417) }
            acc := x
        }
        _log("loop256_addmod:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := div(x, 3) }
            acc := x
        }
        _log("loop256_div:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := mod(add(x, 1), 8380417) }
            acc := x
        }
        _log("loop256_mod:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := byte(0, x) }
            acc := x
        }
        _log("loop256_byte:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := signextend(2, x) }
            acc := x
        }
        _log("loop256_signextend:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := shr(1, shl(1, x)) }
            acc := x
        }
        _log("loop256_shl_shr_pair:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := exp(x, 2) }
            acc := x
        }
        _log("loop256_exp2:", g0 - gasleft());

        sink = acc;
    }

    // =======================================================================
    // 2. MEMORY: MLOAD/MSTORE, MCOPY (EIP-5656), MSIZE, quadratic expansion
    // =======================================================================
    function test_cal_02_memory() public {
        uint256 g0;
        bytes memory a = new bytes(16384);
        bytes memory b = new bytes(16384);
        uint256 acc;

        // hand loop of MLOAD/MSTORE over 16 KiB (512 words)
        g0 = gasleft();
        assembly ("memory-safe") {
            let s := add(a, 32)
            let d := add(b, 32)
            for { let i := 0 } lt(i, 16384) { i := add(i, 32) } { mstore(add(d, i), mload(add(s, i))) }
        }
        _log("copy16KB_mload_mstore_loop:", g0 - gasleft());

        // MCOPY, one instruction
        g0 = gasleft();
        assembly ("memory-safe") {
            mcopy(add(b, 32), add(a, 32), 16384)
        }
        _log("copy16KB_mcopy:", g0 - gasleft());

        // IDENTITY precompile (0x04), 15 + 3/word — warm it first
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x04, add(a, 32), 32, add(b, 32), 32))
        }
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x04, add(a, 32), 16384, add(b, 32), 16384))
        }
        _log("copy16KB_identity_precompile_warm:", g0 - gasleft());

        // quadratic expansion probe: cost of touching the 1 MiB mark
        g0 = gasleft();
        assembly ("memory-safe") {
            mstore(1000000, 1)
        }
        _log("expand_to_1MB_single_mstore:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            mstore(1000032, 1)
        }
        _log("expand_1MB_plus_one_word:", g0 - gasleft());

        // (MSIZE is unusable under the Yul optimizer — solc error 6553 — so the
        //  high-water mark is read from the free-memory pointer instead.)
        assembly ("memory-safe") {
            acc := mload(0x40)
        }
        _log("free_mem_ptr_after:", acc);
        sink = acc;
    }

    // =======================================================================
    // 3. STORAGE-CLASS: TSTORE/TLOAD (EIP-1153) vs memory, SLOAD
    //    NOTE: TSTORE/TLOAD are unavailable to the verifier itself (verify()
    //    is a view function and must stay state-free), so this measurement is
    //    for comparison only.
    // =======================================================================
    function test_cal_03_transient_vs_memory() public {
        uint256 g0;
        uint256 acc;
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { tstore(i, i) }
        }
        _log("tstore_x256:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { acc := add(acc, tload(i)) }
        }
        _log("tload_x256:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { mstore(add(0x8000, shl(5, i)), i) }
        }
        _log("mstore_x256_at_32KB:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { acc := add(acc, mload(add(0x8000, shl(5, i)))) }
        }
        _log("mload_x256_at_32KB:", g0 - gasleft());
        sink = acc;
    }

    // =======================================================================
    // 4. LOG0-4 as a "cheap write channel"
    //    NOTE: also unavailable to the verifier (LOG is not allowed in view
    //    context); measured for comparison only.
    // =======================================================================
    function test_cal_04_log_as_write_channel() public {
        uint256 g0;
        bytes memory a = new bytes(768); // one w1Encode blob
        g0 = gasleft();
        assembly {
            log0(add(a, 32), 768)
        }
        _log("log0_768B:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            mcopy(add(a, 32), add(a, 32), 768)
        }
        _log("mcopy_768B_for_comparison:", g0 - gasleft());
    }

    // =======================================================================
    // 5. CODE AS DATA: EXTCODECOPY / CODECOPY / EXTCODESIZE / EXTCODEHASH
    //    vs recomputation and vs memory tables (zeta tables, decode LUTs).
    // =======================================================================
    function test_cal_05_code_as_table() public {
        uint256 g0;
        // deploy a 8 KiB data contract
        bytes memory data = new bytes(8192);
        for (uint256 i = 0; i < 8192; ++i) {
            data[i] = bytes1(uint8(i));
        }
        address tbl = _deployData(data);

        // COLD extcodecopy of the whole table
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := mload(0x40)
            extcodecopy(tbl, p, 0, 8192)
        }
        _log("extcodecopy_8KB_COLD:", g0 - gasleft());
        // WARM
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := mload(0x40)
            extcodecopy(tbl, p, 0, 8192)
        }
        _log("extcodecopy_8KB_WARM:", g0 - gasleft());

        // 256 individual 32-byte extcodecopies (random-access table lookup)
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := mload(0x40)
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { extcodecopy(tbl, p, shl(5, i), 32) }
        }
        _log("extcodecopy_256x32B_WARM:", g0 - gasleft());

        // same 256 lookups from memory (the table already resident)
        uint256 acc;
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := mload(0x40)
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { acc := add(acc, mload(add(p, shl(5, i)))) }
        }
        _log("mload_256x32B_from_memory:", g0 - gasleft());

        // 256 PUSH32 immediates (an unrolled constant table) — the alternative
        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                x := add(x, 0x4f066b004fe0330053df73004f062b003965690039756700495e0200000001)
            }
            acc := x
        }
        _log("push32_immediate_x256(in loop):", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            acc := add(acc, extcodesize(tbl))
        }
        _log("extcodesize_WARM:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            acc := add(acc, extcodehash(tbl))
        }
        _log("extcodehash_WARM:", g0 - gasleft());

        // CODECOPY of own code (always warm, no account access)
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := mload(0x40)
            codecopy(p, 0, 8192)
        }
        _log("codecopy_own_8KB:", g0 - gasleft());
        sink = acc;
    }

    // =======================================================================
    // 6. CALLDATA: CALLDATALOAD / CALLDATACOPY vs memory, and the EIP-7623 math
    // =======================================================================
    function test_cal_06_calldata(bytes calldata blob) external {
        uint256 g0;
        uint256 acc;
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                acc := add(acc, calldataload(add(blob.offset, shl(5, i))))
            }
        }
        _log("calldataload_x256:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := mload(0x40)
            calldatacopy(p, blob.offset, 8192)
        }
        _log("calldatacopy_8KB:", g0 - gasleft());
        // unaligned (3-byte-stride) calldataload: same 3 gas as aligned?
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 768) { i := add(i, 3) } {
                acc := add(acc, shr(232, calldataload(add(blob.offset, i))))
            }
        }
        _log("calldataload_3B_stride_x256:", g0 - gasleft());
        sink = acc;
    }

    function test_cal_06_driver() public {
        bytes memory blob = new bytes(8192);
        (bool ok,) = address(this).call(abi.encodeWithSelector(this.test_cal_06_calldata.selector, blob));
        require(ok, "calldata probe failed");
    }

    // =======================================================================
    // 7. PRECOMPILES — full sweep at current mainnet (Prague/Osaka) pricing
    // =======================================================================
    function test_cal_07_precompiles() public {
        uint256 g0;
        bytes memory inp = new bytes(1024);
        bytes memory outb = new bytes(1024);

        // ---- 0x02 SHA256 (60 + 12/word)
        _warm(0x02);
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x02, add(inp, 32), 1024, add(outb, 32), 32))
        }
        _log("sha256_1024B:", g0 - gasleft());
        _warm(0x03);
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x03, add(inp, 32), 1024, add(outb, 32), 32))
        }
        _log("ripemd160_1024B:", g0 - gasleft());

        // ---- keccak256 OPCODE for comparison (30 + 6/word)
        g0 = gasleft();
        assembly ("memory-safe") {
            sstore(0, keccak256(add(inp, 32), 1024))
        }
        // subtract the sstore by measuring it separately below; report raw
        _log("keccak256_opcode_1024B_plus_sstore:", g0 - gasleft());
        bytes32 h;
        g0 = gasleft();
        assembly ("memory-safe") {
            h := keccak256(add(inp, 32), 1024)
        }
        _log("keccak256_opcode_1024B:", g0 - gasleft());
        hsink = h;

        // ---- 0x01 ECRECOVER (3000)
        _warm(0x01);
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x01, add(inp, 32), 128, add(outb, 32), 32))
        }
        _log("ecrecover:", g0 - gasleft());

        // ---- 0x09 BLAKE2F, 12 rounds and 1 round (1 gas/round)
        bytes memory b2 = new bytes(213);
        assembly ("memory-safe") {
            let p := add(b2, 32)
            mstore(p, shl(224, 12)) // rounds = 12 (big-endian uint32)
            mstore8(add(p, 212), 1) // final block flag
        }
        _warm(0x09);
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x09, add(b2, 32), 213, add(outb, 32), 64))
        }
        _log("blake2f_12rounds:", g0 - gasleft());
        assembly ("memory-safe") {
            mstore(add(b2, 32), shl(224, 24))
        }
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x09, add(b2, 32), 213, add(outb, 32), 64))
        }
        _log("blake2f_24rounds:", g0 - gasleft());
    }

    // =======================================================================
    // 8. MODEXP (0x05) as a batched modular-arithmetic engine
    //    EIP-2565 + EIP-7883 (live on osaka): min 500 gas.
    // =======================================================================
    function test_cal_08_modexp() public {
        uint256 g0;
        _warm(0x05);

        // (a) 32-byte base, 1-byte exp, 32-byte mod: the cheapest useful shape
        //     = "x mod q" for one 256-bit x. Compare against MOD (5 gas).
        bytes memory in1 = abi.encodePacked(uint256(32), uint256(1), uint256(32), uint256(12345678901234567890), uint8(1), uint256(8380417));
        bytes memory o = new bytes(32);
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x05, add(in1, 32), mload(in1), add(o, 32), 32))
        }
        _log("modexp_32B_exp1_mod32B:", g0 - gasleft());

        // (b) 256-byte base (a whole packed vector), exp 1, 32-byte modulus:
        //     "reduce a 2048-bit integer mod q" in one precompile call.
        bytes memory big = new bytes(256);
        bytes memory in2 = abi.encodePacked(uint256(256), uint256(1), uint256(32), big, uint8(1), uint256(8380417));
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x05, add(in2, 32), mload(in2), add(o, 32), 32))
        }
        _log("modexp_256Bbase_exp1_mod32B:", g0 - gasleft());

        // (c) inversion shape: x^(P-2) mod P for a 192-bit prime — the cost of
        //     a full modular inversion via Fermat's little theorem
        uint256 P = (uint256(1) << 192) - 237;
        bytes memory in3 = abi.encodePacked(uint256(32), uint256(32), uint256(32), uint256(3), P - 2, P);
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x05, add(in3, 32), mload(in3), add(o, 32), 32))
        }
        _log("modexp_inverse_mod_2^192-237:", g0 - gasleft());

        // (d) full 256-bit exponent, 256-bit modulus (worst realistic shape)
        bytes memory in4 = abi.encodePacked(
            uint256(32), uint256(32), uint256(32), type(uint256).max - 1, type(uint256).max - 2, type(uint256).max - 4
        );
        g0 = gasleft();
        assembly ("memory-safe") {
            pop(staticcall(gas(), 0x05, add(in4, 32), mload(in4), add(o, 32), 32))
        }
        _log("modexp_32/32/32_full:", g0 - gasleft());
    }

    // =======================================================================
    // 9. BN254 (0x06/0x07/0x08) and BLS12-381 (EIP-2537, 0x0b..0x11)
    //    Can any of them serve as a field-arithmetic / NTT / MSM engine?
    // =======================================================================
    /// @dev one isolated precompile probe. `gas` is measured with NOTHING else
    ///      inside the bracket (console.log itself costs ~600-2600, enough to
    ///      contaminate the measurement).
    function _probe(uint256 addr, bytes memory inp, uint256 outLen)
        internal
        view
        returns (bool ok, uint256 gasUsed)
    {
        bytes memory o = new bytes(outLen == 0 ? 32 : outLen);
        uint256 g0;
        assembly ("memory-safe") {
            g0 := gas()
            ok := staticcall(1000000, addr, add(inp, 32), mload(inp), add(o, 32), outLen)
        }
        gasUsed = g0 - gasleft();
    }

    function test_cal_09_curves() public {
        bool ok;
        uint256 g;

        // BN254 G1ADD (0x06, EIP-1108: 150) with the generator + generator
        bytes memory g1bn = abi.encodePacked(uint256(1), uint256(2));
        _warm(0x06);
        (ok, g) = _probe(0x06, bytes.concat(g1bn, g1bn), 64);
        _log("bn254_g1add ok:", ok ? 1 : 0);
        _log("bn254_g1add:", g);

        // BN254 G1MUL (0x07, 6000)
        _warm(0x07);
        (ok, g) = _probe(0x07, bytes.concat(g1bn, bytes32(uint256(12345))), 64);
        _log("bn254_g1mul ok:", ok ? 1 : 0);
        _log("bn254_g1mul:", g);

        // BN254 PAIRING (0x08, 45000 + 34000/pair), one pair: e(G1,G2)
        _warm(0x08);
        (ok, g) = _probe(0x08, new bytes(192), 32);
        _log("bn254_pairing_1pair_zeros ok:", ok ? 1 : 0);
        _log("bn254_pairing_1pair_zeros:", g);

        // BLS12-381 G1ADD (0x0b, EIP-2537: 375)
        bytes memory g1 = _blsG1Gen();
        _warm(0x0b);
        (ok, g) = _probe(0x0b, bytes.concat(g1, g1), 128);
        _log("bls12381_g1add ok:", ok ? 1 : 0);
        _log("bls12381_g1add:", g);

        // BLS12-381 G1MSM (0x0c) with 1 pair
        (ok, g) = _probe(0x0c, bytes.concat(g1, bytes32(uint256(7))), 128);
        _log("bls12381_g1msm_k1 ok:", ok ? 1 : 0);
        _log("bls12381_g1msm_k1:", g);

        // BLS12-381 MAP_FP_TO_G1 (0x10, 5500)
        bytes memory fp = new bytes(64);
        assembly ("memory-safe") {
            mstore(add(fp, 64), 5)
        }
        (ok, g) = _probe(0x10, fp, 128);
        _log("bls12381_map_fp_to_g1 ok:", ok ? 1 : 0);
        _log("bls12381_map_fp_to_g1:", g);

        // BLS12-381 G2ADD (0x0d, 600)
        bytes memory g2 = _blsG2Gen();
        (ok, g) = _probe(0x0d, bytes.concat(g2, g2), 256);
        _log("bls12381_g2add ok:", ok ? 1 : 0);
        _log("bls12381_g2add:", g);
    }

    // =======================================================================
    // 10. CALL FAMILY: overhead of the Keccak-helper indirection
    // =======================================================================
    function test_cal_10_call_overhead() public {
        uint256 g0;
        address nul = _deployData(hex"5f5ff3"); // PUSH0 PUSH0 RETURN  (returns nothing)
        bool ok;
        // cold
        g0 = gasleft();
        assembly ("memory-safe") {
            ok := staticcall(gas(), nul, 0, 0, 0, 0)
        }
        _log("staticcall_empty_COLD:", g0 - gasleft());
        g0 = gasleft();
        assembly ("memory-safe") {
            ok := staticcall(gas(), nul, 0, 0, 0, 0)
        }
        _log("staticcall_empty_WARM:", g0 - gasleft());
        // with an 800-byte argument + 800-byte return buffer (the f1600 shape)
        bytes memory st = new bytes(800);
        g0 = gasleft();
        assembly ("memory-safe") {
            ok := staticcall(gas(), nul, add(st, 32), 800, add(st, 32), 800)
        }
        _log("staticcall_800in_800out_WARM:", g0 - gasleft());
        require(ok || !ok);
    }

    // =======================================================================
    // helpers
    // =======================================================================
    function _warm(uint256 a) internal view {
        assembly ("memory-safe") {
            // bounded gas: EIP-2537/1108 precompiles consume ALL forwarded gas
            // on malformed input, which would otherwise abort the probe.
            pop(staticcall(100000, a, 0, 0, 0, 0))
        }
    }

    function _deployData(bytes memory data) internal returns (address ptr) {
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "deploy failed");
    }

    /// BLS12-381 G1 generator in EIP-2537 encoding (two 64-byte big-endian Fp
    /// limbs, each 16 zero pad bytes + 48 bytes).
    function _blsG1Gen() internal pure returns (bytes memory) {
        return abi.encodePacked(
            bytes16(0),
            hex"17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
            bytes16(0),
            hex"08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"
        );
    }

    /// BLS12-381 G2 generator in EIP-2537 encoding (four padded 64-byte limbs).
    function _blsG2Gen() internal pure returns (bytes memory) {
        return abi.encodePacked(
            bytes16(0),
            hex"024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8",
            bytes16(0),
            hex"13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e",
            bytes16(0),
            hex"0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801",
            bytes16(0),
            hex"0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be"
        );
    }
}
