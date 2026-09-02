// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC_purity.t.sol
//
// Purity / statelessness / environment-independence of both verifier subjects:
// the shipped MLDSA44Verifier (src) and the reference verifier
// (test/ZZZ_E2ERef.sol).
//
// The IMLDSAVerifier contract states that the verdict is a deterministic
// function of (pkBlob code, message, signature) alone — independent of block
// context, caller and gas — and that verify() is safe to STATICCALL (no state
// writes, no logs, no creation, no self-destruct, no delegatecall). This file
// pins those properties three ways:
//   1. a bytecode opcode census of the DEPLOYED code (the shipped verifier's
//      permutation lives in a separate helper, so its runtime contains no
//      state, creation, log or block-environment opcodes at all);
//   2. a differential run under a mutated block/tx environment and caller,
//      asserting identical verdicts and (shipped) identical gas;
//   3. vm.record, proving no storage slot is read or written.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {IMLDSAVerifier} from "../src/IMLDSAVerifier.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {ZZZ_E2ERef} from "./ZZZ_E2ERef.sol";

contract SECPurityTest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant SEED = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";

    address f1600;
    MLDSA44Verifier shipped;
    ZZZ_E2ERef refv;

    bytes sig;
    bytes badSig;
    bytes msg_;
    address shipPk;
    address refPk;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        f1600 = deployF1600_170();
        shipped = new MLDSA44Verifier(f1600);
        refv = new ZZZ_E2ERef();

        bytes memory pkBlob;
        (sig, pkBlob, msg_) = _vec(SEED, MSG1_HEX);
        badSig = bytes.concat(sig);
        badSig[0] = bytes1(uint8(badSig[0]) ^ 0x01); // FIPS-invalid c~
        shipPk = _deployData(bytes.concat(hex"00", pkBlob));
        refPk = _deployData(pkBlob);
    }

    // --------------------------------------------------------------- fixtures

    function _vec(string memory seedHex, string memory msgHex)
        internal
        returns (bytes memory s, bytes memory pkBlob, bytes memory m)
    {
        string[] memory cmds = new string[](5);
        cmds[0] = PY;
        cmds[1] = VECGEN;
        cmds[2] = "seed";
        cmds[3] = seedHex;
        cmds[4] = msgHex;
        (s, pkBlob, m) = abi.decode(vm.ffi(cmds), (bytes, bytes, bytes));
    }

    function _deployData(bytes memory data) internal returns (address ptr) {
        require(data.length < 24576, "EIP-170");
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "deploy failed");
    }

    // ------------------------------------------------------- bytecode scanner

    /// first index at which `needle` occurs in `hay` (or type(uint256).max).
    function _find(bytes memory hay, bytes memory needle) internal pure returns (uint256 at) {
        at = type(uint256).max;
        if (needle.length == 0 || hay.length < needle.length) return at;
        bytes32 h0;
        assembly ("memory-safe") {
            h0 := mload(add(needle, 32))
        }
        uint256 lim = hay.length - needle.length;
        uint256 pre = needle.length < 32 ? (32 - needle.length) * 8 : 0;
        for (uint256 i = 0; i <= lim; ++i) {
            bytes32 w;
            assembly ("memory-safe") {
                w := mload(add(add(hay, 32), i))
            }
            if ((uint256(w) >> pre) == (uint256(h0) >> pre)) {
                bool eq = true;
                uint256 n = needle.length;
                for (uint256 j = 32; j < n && eq; j += 32) {
                    uint256 take = n - j >= 32 ? 32 : n - j;
                    bytes32 a;
                    bytes32 b;
                    assembly ("memory-safe") {
                        a := mload(add(add(hay, 32), add(i, j)))
                        b := mload(add(add(needle, 32), j))
                    }
                    uint256 shiftBits = (32 - take) * 8;
                    if ((uint256(a) >> shiftBits) != (uint256(b) >> shiftBits)) eq = false;
                }
                if (eq) return i;
            }
        }
    }

    /// opcode census over `code`, skipping [skipAt, skipAt+skipLen) and the
    /// trailing solc metadata; PUSH immediates are stepped over so data bytes
    /// are never miscounted as opcodes.
    function _census(bytes memory code, uint256 skipAt, uint256 skipLen)
        internal
        pure
        returns (uint256[256] memory counts)
    {
        uint256 metaLen = 2 + (uint256(uint8(code[code.length - 2])) << 8) + uint256(uint8(code[code.length - 1]));
        uint256 end = code.length - metaLen;
        uint256 pc = 0;
        while (pc < end) {
            if (skipLen != 0 && pc == skipAt) {
                pc = skipAt + skipLen;
                continue;
            }
            uint8 op = uint8(code[pc]);
            counts[op] += 1;
            if (op >= 0x60 && op <= 0x7f) {
                pc += 2 + (op - 0x60);
            } else {
                pc += 1;
            }
        }
    }

    function _assertNoStateOrCreationOpcodes(uint256[256] memory c, string memory what) internal pure {
        uint8[16] memory forbidden = [
            0x54, // SLOAD
            0x55, // SSTORE
            0x5c, // TLOAD
            0x5d, // TSTORE
            0xf0, // CREATE
            0xf1, // CALL
            0xf2, // CALLCODE
            0xf4, // DELEGATECALL
            0xf5, // CREATE2
            0xff, // SELFDESTRUCT
            0xa0,
            0xa1,
            0xa2,
            0xa3,
            0xa4, // LOG0..LOG4
            0x31 // BALANCE
        ];
        for (uint256 i = 0; i < 16; ++i) {
            assertEq(c[forbidden[i]], 0, string.concat(what, ": forbidden state/creation opcode present"));
        }
    }

    function _assertNoEnvironmentOpcodes(uint256[256] memory c, string memory what) internal pure {
        uint8[14] memory envOps = [
            0x32, // ORIGIN
            0x33, // CALLER
            0x3a, // GASPRICE
            0x40, // BLOCKHASH
            0x41, // COINBASE
            0x42, // TIMESTAMP
            0x43, // NUMBER
            0x44, // PREVRANDAO
            0x45, // GASLIMIT
            0x46, // CHAINID
            0x47, // SELFBALANCE
            0x48, // BASEFEE
            0x49, // BLOBHASH
            0x4a // BLOBBASEFEE
        ];
        for (uint256 i = 0; i < 14; ++i) {
            assertEq(c[envOps[i]], 0, string.concat(what, ": block-environment opcode present"));
        }
    }

    /// The shipped verifier's runtime references the Keccak helper only by an
    /// external STATICCALL, so its whole runtime is free of state, creation, log
    /// AND block-environment opcodes.
    function test_shipped_bytecode_is_stateless_and_environment_free() public view {
        uint256[256] memory c = _census(address(shipped).code, 0, 0);
        _assertNoStateOrCreationOpcodes(c, "shipped");
        _assertNoEnvironmentOpcodes(c, "shipped");
        console.log("shipped STATICCALL / EXTCODECOPY:", c[0xfa], c[0x3c]);
        console.log("   EXTCODEHASH / EXTCODESIZE:", c[0x3f], c[0x3b]);
    }

    /// The reference verifier embeds a Keccak-f[1600] data blob; its instruction
    /// stream contains no state-mutation, creation or log opcodes.
    ///
    /// The two code generators lay that blob out differently and the census has
    /// to be told which one it is looking at:
    ///   * legacy codegen appends it as ONE contiguous data region that is not
    ///     instructions at all, so the census must be told to SKIP it — a linear
    ///     sweep would decode data bytes as opcodes;
    ///   * via-IR materialises the same constant as a run of PUSH32 immediates,
    ///     so every byte of it already sits inside an instruction whose length
    ///     the census steps over, and censusing the WHOLE runtime with nothing
    ///     skipped is then the strictly STRONGER statement.
    /// Either way the blob must still be locatable — contiguously, or as every
    /// one of its 32-byte words — so a vanished permutation is still a failure.
    function test_reference_bytecode_has_no_state_or_creation_opcodes() public view {
        bytes memory code = address(refv).code;
        uint256 at = _find(code, _F1600_CODE);
        uint256[256] memory c;
        if (at != type(uint256).max) {
            c = _census(code, at, _F1600_CODE.length);
        } else {
            bytes memory blob = _F1600_CODE; // one copy; indexing the constant re-copies it
            uint256 n = blob.length / 32;
            bytes memory chunk = new bytes(32);
            // eight evenly spaced 32-byte words, first and last included
            for (uint256 s = 0; s < 8; ++s) {
                uint256 k = (s * (n - 1)) / 7;
                for (uint256 j = 0; j < 32; ++j) {
                    chunk[j] = blob[k * 32 + j];
                }
                assertTrue(_find(code, chunk) != type(uint256).max, "embedded permutation data must be located");
            }
            c = _census(code, 0, 0);
        }
        _assertNoStateOrCreationOpcodes(c, "reference");
    }

    // ------------------------------------------- environment independence + gas

    function test_shipped_verdict_and_gas_independent_of_environment() public {
        bytes memory cdGood = abi.encodeCall(IMLDSAVerifier.verify, (shipPk, msg_, sig));
        bytes memory cdBad = abi.encodeCall(IMLDSAVerifier.verify, (shipPk, msg_, badSig));

        // warm the accounts and the measurement buffer
        for (uint256 i = 0; i < 2; ++i) {
            _gasRaw(address(shipped), cdGood);
            _gasRaw(address(shipped), cdBad);
        }
        (uint256 gTrue0, bool rT0) = _gasRaw(address(shipped), cdGood);
        (uint256 gFalse0, bool rF0) = _gasRaw(address(shipped), cdBad);

        vm.roll(block.number + 123456);
        vm.warp(block.timestamp + 987654321);
        vm.chainId(31337 + 7);
        vm.fee(1234567890);
        vm.coinbase(address(0xc01ba5e));
        vm.txGasPrice(999999999);
        vm.prevrandao(bytes32(uint256(0xdeadbeef)));

        (uint256 gTrue1, bool rT1) = _gasRaw(address(shipped), cdGood);
        (uint256 gFalse1, bool rF1) = _gasRaw(address(shipped), cdBad);
        vm.prank(address(0xA11CE), address(0xB0B));
        (, bool rT2) = _gasRaw(address(shipped), cdGood);
        vm.prank(address(0xA11CE), address(0xB0B));
        (, bool rF2) = _gasRaw(address(shipped), cdBad);

        assertTrue(rT0 && rT1 && rT2, "TRUE verdict must be environment independent");
        assertTrue(!rF0 && !rF1 && !rF2, "FALSE verdict must be environment independent");
        assertEq(gTrue1, gTrue0, "TRUE-case gas must not depend on the environment");
        assertEq(gFalse1, gFalse0, "FALSE-case gas must not depend on the environment");
        console.log("shipped env-independent gas (TRUE / FALSE):", gTrue0, gFalse0);
    }

    function test_reference_verdict_independent_of_environment() public {
        bool a = refv.verify(refPk, msg_, sig);
        bool aBad = refv.verify(refPk, msg_, badSig);
        vm.roll(block.number + 999);
        vm.warp(block.timestamp + 999);
        vm.chainId(4242);
        vm.fee(7);
        vm.prevrandao(bytes32(uint256(12345)));
        vm.prank(address(0xA11CE), address(0xB0B));
        bool b = refv.verify(refPk, msg_, sig);
        vm.prank(address(0xA11CE), address(0xB0B));
        bool bBad = refv.verify(refPk, msg_, badSig);
        assertTrue(a && b, "reference TRUE verdict must be environment independent");
        assertTrue(!aBad && !bBad, "reference FALSE verdict must be environment independent");
    }

    // ------------------------------------------------------ caller independence

    function test_verdict_independent_of_caller() public {
        address[4] memory callers =
            [address(0), address(1), address(0xdeadbeef), address(uint160(uint256(keccak256("caller"))))];
        for (uint256 i = 0; i < 4; ++i) {
            vm.prank(callers[i], callers[i]);
            (bool ok, bytes memory ret) =
                address(shipped).staticcall(abi.encodeCall(IMLDSAVerifier.verify, (shipPk, msg_, sig)));
            assertTrue(ok && abi.decode(ret, (bool)), "shipped verdict must not depend on the caller");

            vm.prank(callers[i], callers[i]);
            (ok, ret) = address(refv).staticcall(abi.encodeCall(ZZZ_E2ERef.verify, (refPk, msg_, sig)));
            assertTrue(ok && abi.decode(ret, (bool)), "reference verdict must not depend on the caller");
        }
    }

    // ------------------------------------------------------- no storage access

    function test_shipped_touches_no_storage() public {
        vm.record();
        bool ok = shipped.verify(shipPk, msg_, sig);
        assertTrue(ok, "sanity");
        _assertNoStorage(address(shipped), "verifier");
        _assertNoStorage(f1600, "helper");
        _assertNoStorage(shipPk, "pk data contract");
    }

    function test_reference_touches_no_storage() public {
        vm.record();
        bool ok = refv.verify(refPk, msg_, sig);
        assertTrue(ok, "sanity");
        _assertNoStorage(address(refv), "reference verifier");
        _assertNoStorage(refPk, "pk data contract");
    }

    function _assertNoStorage(address who, string memory what) internal {
        (bytes32[] memory reads, bytes32[] memory writes) = vm.accesses(who);
        assertEq(reads.length, 0, string.concat(what, ": must not read storage"));
        assertEq(writes.length, 0, string.concat(what, ": must not write storage"));
    }

    // -------------------------------------- gas starvation cannot flip a verdict

    /// The only gas-sensitive construct is the helper STATICCALL. Starving the
    /// call can produce a revert (out of gas), never a wrong verdict: whenever
    /// the call completes, the verdict equals the reference one.
    function test_low_gas_never_flips_the_verdict() public view {
        bytes memory cdGood = abi.encodeCall(IMLDSAVerifier.verify, (shipPk, msg_, sig));
        bytes memory cdBad = abi.encodeCall(IMLDSAVerifier.verify, (shipPk, msg_, badSig));
        uint256[8] memory budgets =
            [uint256(50_000), 200_000, 800_000, 2_000_000, 4_000_000, 8_000_000, 16_000_000, 32_000_000];
        uint256 completed = 0;
        for (uint256 i = 0; i < 8; ++i) {
            (bool ok1, bool r1) = _callWithGas(address(shipped), cdGood, budgets[i]);
            if (ok1) {
                assertTrue(r1, "a completed low-gas call must still return TRUE");
                ++completed;
            }
            (bool ok2, bool r2) = _callWithGas(address(shipped), cdBad, budgets[i]);
            if (ok2) assertFalse(r2, "a completed low-gas call must still return FALSE");
        }
        console.log("shipped low-gas calls that completed:", completed);
    }

    // ----------------------------------------------------------- raw call utils

    function _gasRaw(address target, bytes memory cd) internal view returns (uint256 used, bool res) {
        assembly ("memory-safe") {
            let outPtr := mload(0x40)
            let g0 := gas()
            let ok := staticcall(gas(), target, add(cd, 32), mload(cd), outPtr, 32)
            used := sub(g0, gas())
            res := and(ok, eq(mload(outPtr), 1))
        }
    }

    function _callWithGas(address target, bytes memory cd, uint256 g) internal view returns (bool ok, bool res) {
        assembly ("memory-safe") {
            let outPtr := mload(0x40)
            mstore(outPtr, 0)
            ok := staticcall(g, target, add(cd, 32), mload(cd), outPtr, 32)
            res := and(ok, eq(mload(outPtr), 1))
        }
    }
}
