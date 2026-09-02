// SPDX-License-Identifier: MIT
// FILE: test/PROFILE_E2E.t.sol
//
// GAS-PROFILING HARNESS for the shipped verifier (src/MLDSA44Verifier.sol).
// Not a correctness test — correctness lives in E2E.t.sol / Kernels.t.sol.
// Driven by tools/profile.sh; see that script for the full workflow.
//
// Three views of the same 1.24M-gas verification (same fixture as
// test_e2e_10_seed_vector_accepts_and_gas: e2e_pk.py `seed` blob + NIST-mode
// pythonref signature under Constants.SEED_POSTQUANTUM_STR):
//
//   test_profile_00_verify  — ONE external verify() call and nothing else.
//       The `forge test --flamegraph` target: the flame graph decodes the
//       verifier's contract-internal frames (_verify/_computeMu/_wPrimeRows/
//       _finalHash) and shows every STATICCALL to the Keccak-f[1600] helper.
//       Free-function kernels (nttFwV3, matvecRow, unpackZPacked, ...) do NOT
//       get frames of their own — foundry's internal decoder only labels
//       contract member functions — which is what the staged view below fixes.
//
//   test_profile_10_stages  — the exact _verify() pipeline re-run stage by
//       stage THROUGH THE SHIPPED src KERNELS, each stage inside a named
//       internal member function (so it gets its own flame-graph frame) and
//       inside a gasleft() bracket (so it gets an exact number). The staged
//       result is pinned to the real pipeline: cPrime must equal cTilde and
//       the external verify() on the same fixture must return true.
//
//   test_profile_20_ntt_layers — per-PASS gas inside the shipped nttFwV3 /
//       nttInvV3 via their `prof` gas()-snapshot arrays (the plumbing already
//       present in src/Ntt.sol and src/InvNtt.sol), on REAL signature data.
//       The forward runs its eight layers as THREE fused passes (radix-8
//       L1+L2+L3, radix-8 L4+L5+L6, in-word L7+L8) and so writes 4 snapshots
//       delimiting 3 blocks; the inverse runs FOUR and writes 5.
//
// The staged sum reconciles with the external call to within the harness
// residual (calldata-vs-memory argument passing, function-call glue); the
// residual is printed rather than hidden.
pragma solidity ^0.8.25;

import {Test, console2} from "forge-std/Test.sol";
import {Constants} from "./seed.sol";
import {PythonSigner} from "./vendor/ZKNOX_PythonSigner.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {MLDSA44Verifier, PK_SIZE, PK_T1_OFF, PK_A_OFF} from "../src/MLDSA44Verifier.sol";
import {shake256Fast170, shake256Batch170} from "../src/FastKeccak170.sol";
import {
    unpackHFast,
    unpackZPacked,
    useHintSwar,
    sampleInBallPacked,
    matvecRow
} from "../src/Decode.sol";
import {nttFwV3, nttFwTable} from "../src/Ntt.sol";
import {nttInvV3, nttInvTable} from "../src/InvNtt.sol";

contract PROFILE_E2ETest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant PKGEN = "tools/fixtures/e2e_pk.py";
    string constant FFI_MSG_STR = "0x1111222233334444111122223333444411112222333344441111222233334444";
    bytes constant FFI_MSG = hex"1111222233334444111122223333444411112222333344441111222233334444";

    MLDSA44Verifier opt;
    address optPk;
    address f1600;
    bytes sig;

    function setUp() public {
        f1600 = deployF1600_170();
        vm.label(f1600, "F1600_keccak_helper");
        opt = new MLDSA44Verifier(f1600);

        // pk blob (FFI, same generator and seed as test_e2e_10)
        string[] memory cmds = new string[](4);
        cmds[0] = PY;
        cmds[1] = PKGEN;
        cmds[2] = "seed";
        cmds[3] = Constants.SEED_POSTQUANTUM_STR;
        bytes memory blob = vm.ffi(cmds);
        assertEq(blob.length, PK_SIZE, "pk blob size");

        // deterministic NIST-mode signature over FFI_MSG (FFI, pythonref)
        PythonSigner signer = new PythonSigner();
        (bytes memory cT, bytes memory z, bytes memory hh) =
            signer.sign("pythonref", FFI_MSG_STR, "NIST", Constants.SEED_POSTQUANTUM_STR);
        sig = abi.encodePacked(cT, z, hh);
        assertEq(sig.length, 2420, "sig length");

        // pk data contract: 0x00 (EIP-3541) || payload, deployed by real CREATE
        bytes memory data = bytes.concat(hex"00", blob);
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        address ptr;
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "pk data contract deploy failed");
        optPk = ptr;
    }

    // ================================================= 00: flamegraph target

    /// One external verify() call and nothing else, so the flame graph's
    /// non-test frames are ~pure verifier. Prints the same external-call
    /// bracket as test_e2e_10 (expected: 1,226,311).
    function test_profile_00_verify() public {
        bytes memory s = sig;
        uint256 g0 = gasleft();
        bool ok = opt.verify(optPk, FFI_MSG, s);
        uint256 g = g0 - gasleft();
        assertTrue(ok, "fixture must verify TRUE");
        console2.log("verify() external-call gas:", g);
    }

    // ==================================================== 10: staged pipeline

    // Each stage is a named MEMBER function so foundry's --decode-internal
    // gives it a flame-graph frame; the free-function kernels inside would
    // otherwise be invisible. Brackets in the test body give exact numbers.

    /// mirrors _pkSizeOk + the lazy tr/A/t1 consumption of the shipped
    /// verifier: only the exact-size check happens up front
    function _stage_pkGate() internal view returns (bool pkOk) {
        address p = optPk;
        assembly ("memory-safe") {
            if eq(extcodesize(p), add(PK_SIZE, 1)) { pkOk := 1 }
        }
    }

    function _stage_unpackH(bytes memory hB) internal pure returns (uint256[4] memory hMasks) {
        (bool hOk, uint256[4] memory m, uint256 w) = unpackHFast(hB);
        require(hOk && w <= 80, "unpackH failed on a valid signature");
        hMasks = m;
    }

    function _stage_unpackZ(bytes memory zB) internal pure returns (uint256[][] memory zp) {
        bool normOk;
        (zp, normOk) = unpackZPacked(zB);
        require(normOk, "z norm failed on a valid signature");
    }

    function _stage_computeMu(bytes memory message) internal view returns (bytes memory mu) {
        address p = optPk;
        bytes memory muIn = new bytes(66 + message.length);
        assembly ("memory-safe") {
            let d := add(muIn, 32)
            extcodecopy(p, d, 1, 64)
            mcopy(add(d, 66), add(message, 32), mload(message))
        }
        // same dispatch as the shipped _computeMu: batched one-call SHAKE256,
        // lane-level fallback only for the 800-byte preimage (|M| == 734)
        mu = muIn.length == 800
            ? shake256Fast170(muIn, 64, f1600)
            : shake256Batch170(muIn, 64, f1600);
    }

    function _stage_sampleInBall(bytes32 cTilde) internal view returns (uint256[] memory c) {
        c = sampleInBallPacked(cTilde, f1600);
    }

    function _stage_nttC(uint256[] memory c, uint256[] memory prof, uint256 fwT)
        internal
        view
        returns (uint256[] memory)
    {
        return nttFwV3(c, prof, fwT);
    }

    function _stage_nttZ(uint256[][] memory zp, uint256[] memory prof, uint256 fwT) internal view {
        for (uint256 j = 0; j < 4; ++j) {
            zp[j] = nttFwV3(zp[j], prof, fwT);
        }
    }

    /// lazy per-row pk consumption + matvec, exactly as _wPrimeRows does it
    function _stage_matvecRow(uint256 scratch, uint256 i, uint256[][] memory zp, uint256[] memory cHat)
        internal
        view
        returns (uint256[] memory acc)
    {
        address p = optPk;
        assembly ("memory-safe") {
            extcodecopy(p, scratch, add(1, add(PK_A_OFF, shl(12, i))), 0x1000)
            extcodecopy(p, add(scratch, 0x1000), add(1, add(PK_T1_OFF, shl(10, i))), 0x400)
        }
        acc = matvecRow(scratch, zp, cHat, scratch + 0x1000);
    }

    function _stage_invNtt(uint256[] memory acc, uint256[] memory prof, uint256 invT) internal view {
        nttInvV3(acc, prof, invT);
    }

    function _stage_useHint(uint256[4] memory hMasks, uint256[][] memory r)
        internal
        pure
        returns (bytes memory w1)
    {
        w1 = useHintSwar(hMasks, r);
    }

    function _stage_finalHash(bytes memory mu, bytes memory w1) internal view returns (bytes32 cPrime) {
        bytes memory fin = new bytes(832);
        assembly ("memory-safe") {
            mcopy(add(fin, 32), add(mu, 32), 64)
            mcopy(add(fin, 96), add(w1, 32), 768)
        }
        bytes memory ct2 = shake256Batch170(fin, 32, f1600);
        assembly ("memory-safe") {
            cPrime := mload(add(ct2, 32))
        }
    }

    function _slice(bytes memory b, uint256 start, uint256 len) internal pure returns (bytes memory out) {
        out = new bytes(len);
        assembly ("memory-safe") {
            mcopy(add(out, 32), add(add(b, 32), start), len)
        }
    }

    /// pipeline values kept in one memory struct so the staged test stays
    /// under the stack limit without --via-ir
    struct Pipe {
        bytes s;
        bytes zB;
        bytes hB;
        bytes mu;
        bytes w1;
        bytes32 cTilde;
        bytes32 cPrime;
        uint256[4] hMasks;
        uint256[][] zp;
        uint256[] cHat;
        uint256[][] r;
        uint256[] c;
        uint256[] ntProf;
    }

    /// The shipped pipeline, stage by stage, through the SAME src kernels
    /// _verify() calls, on the SAME fixture, with a gasleft() bracket per
    /// stage (brackets stored in G; ~15 gas of mstore noise per bracket).
    /// Faithfulness checks: staged cPrime == cTilde AND the real external
    /// verify() returns true.
    function test_profile_10_stages() public {
        Pipe memory p;
        uint256[16] memory G; // per-stage gas
        uint256 t;

        p.s = sig;
        {
            bytes memory s_ = p.s;
            bytes32 ct;
            assembly ("memory-safe") {
                ct := mload(add(s_, 32))
            }
            p.cTilde = ct;
        }

        // harness-only: materialise the sig[32:2336] / sig[2336:2420] slices
        // that _verify() takes as calldata slices (their copy-to-memory at the
        // kernel call sites is paid inside _verify; here it is paid up front)
        t = gasleft();
        p.zB = _slice(p.s, 32, 2304);
        p.hB = _slice(p.s, 2336, 84);
        G[0] = t - gasleft();

        t = gasleft();
        bool pkOk = _stage_pkGate();
        G[1] = t - gasleft();
        require(pkOk, "pk blob missing");

        t = gasleft();
        p.hMasks = _stage_unpackH(p.hB);
        G[2] = t - gasleft();

        t = gasleft();
        p.zp = _stage_unpackZ(p.zB);
        G[3] = t - gasleft();

        t = gasleft();
        p.mu = _stage_computeMu(FFI_MSG);
        G[4] = t - gasleft();

        t = gasleft();
        p.c = _stage_sampleInBall(p.cTilde);
        G[5] = t - gasleft();

        p.ntProf = new uint256[](10);
        // built ONCE, exactly as _wPrimeRows does it
        uint256 fwT = nttFwTable();
        uint256 invT = nttInvTable();
        t = gasleft();
        p.cHat = _stage_nttC(p.c, p.ntProf, fwT);
        G[6] = t - gasleft();

        t = gasleft();
        _stage_nttZ(p.zp, p.ntProf, fwT);
        G[7] = t - gasleft();

        p.r = new uint256[][](4);
        uint256 scratch;
        assembly ("memory-safe") {
            scratch := mload(0x40)
            mstore(0x40, add(scratch, 0x1400))
        }
        for (uint256 i = 0; i < 4; ++i) {
            t = gasleft();
            uint256[] memory acc = _stage_matvecRow(scratch, i, p.zp, p.cHat);
            G[8] += t - gasleft();

            // the raw accumulator feeds nttInvV3 directly: the inverse NTT
            // folds the former reducePacked pass into its first layer
            t = gasleft();
            _stage_invNtt(acc, p.ntProf, invT);
            G[10] += t - gasleft();
            p.r[i] = acc;
        }

        t = gasleft();
        p.w1 = _stage_useHint(p.hMasks, p.r);
        G[11] = t - gasleft();

        t = gasleft();
        p.cPrime = _stage_finalHash(p.mu, p.w1);
        G[12] = t - gasleft();

        // faithfulness checks
        assertEq(p.cPrime, p.cTilde, "staged pipeline diverged from the signature");
        t = gasleft();
        bool ok = opt.verify(optPk, FFI_MSG, p.s);
        G[13] = t - gasleft();
        assertTrue(ok, "external verify() must accept the fixture");

        _report(G);
    }

    /// Stage table printer, split out of test_profile_10_stages so the staged
    /// pipeline's live locals stay inside the via-IR stack scheduler's reach
    /// (no memoryguard is emitted: the Keccak glue's byte-reversal blocks are
    /// not memory-safe, so the scheduler cannot spill).
    function _report(uint256[16] memory G) internal pure {
        uint256 gSum;
        for (uint256 k = 1; k <= 12; ++k) {
            gSum += G[k];
        }
        console2.log("stage pk size check (lazy blob)    :", G[1]);
        console2.log("stage unpackH (84B)                :", G[2]);
        console2.log("stage unpackZ+norm (2304B)         :", G[3]);
        console2.log("stage mu (batched SHAKE, 1 call)   :", G[4]);
        console2.log("stage sampleInBall (1 perm)        :", G[5]);
        console2.log("stage nttFw(c)  (1 transform)      :", G[6]);
        console2.log("stage nttFw(z)  (4 transforms)     :", G[7]);
        console2.log("stage matvec 4 rows (+pk row copy) :", G[8]);
        console2.log("stage nttInv x4 (reduce folded in) :", G[10]);
        console2.log("stage useHint+w1Encode             :", G[11]);
        console2.log("stage finalHash (batched, 7 perms) :", G[12]);
        console2.log("harness slice copies (see header)  :", G[0]);
        console2.log("staged kernel sum                  :", gSum);
        console2.log("external verify() on same fixture  :", G[13]);
        // glue = call overhead + calldata copies + arg passing the staged view
        // does not replicate exactly; can be negative when the harness pays
        // memory expansion the in-place pipeline avoids
        if (G[13] >= gSum) {
            console2.log("residual (verify - stagedSum), glue:", G[13] - gSum);
        } else {
            console2.log("residual NEGATIVE (stagedSum-verify):", gSum - G[13]);
        }
    }

    // =================================================== 20: NTT pass profile

    /// Per-PASS gas of the SHIPPED forward and inverse NTTs on real signature
    /// data, via the prof gas()-snapshot plumbing. The forward writes 4
    /// snapshots (prof[0] before the first pass, then one after each of its
    /// THREE fused passes: radix-8 L1+L2+L3, radix-8 L4+L5+L6, in-word L7+L8);
    /// the inverse writes 5 (entry-fold+L1+L2, L3+L4, L5+L6, L7+L8+scale).
    function test_profile_20_ntt_layers() public {
        bytes memory zB = _slice(sig, 32, 2304);
        (uint256[][] memory zp, bool normOk) = unpackZPacked(zB);
        require(normOk, "z norm failed on a valid signature");

        // warm the code path so the profile is steady-state. The twiddle
        // tables are built ONCE, outside the bracket, exactly as _wPrimeRows
        // does it -- the bracket measures the transform, not the table (§5.4).
        uint256[] memory prof = new uint256[](10);
        uint256 fwT = nttFwTable();
        uint256 invT = nttInvTable();
        nttFwV3(zp[1], prof, fwT);

        uint256 g0 = gasleft();
        uint256[] memory zHat = nttFwV3(zp[0], prof, fwT);
        uint256 total = g0 - gasleft();
        console2.log("nttFwV3 total (shipped, real z)    :", total);
        for (uint256 k = 1; k < 4; ++k) {
            // pass 3 is the fused in-word layers 7+8 (LAZY exit)
            console2.log("  fwd pass", k, ":", prof[k - 1] - prof[k]);
        }

        uint256[] memory iprof = new uint256[](7);
        g0 = gasleft();
        nttInvV3(zHat, iprof, invT);
        total = g0 - gasleft();
        console2.log("nttInvV3 total (shipped)           :", total);
        for (uint256 k = 1; k < 5; ++k) {
            console2.log("  inv pass", k, ":", iprof[k - 1] - iprof[k]);
        }
    }
}
