// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC_memsafety.t.sol
//
// Memory safety of the assembly kernels of both verifier subjects under
// attacker-controlled message lengths and at every sponge boundary.
//
// Method: a probe paints the free memory above the free-memory pointer (FMP)
// with a sentinel, runs one kernel, then reports (a) how far past the post-call
// FMP the sentinel was destroyed and (b) whether the FMP itself stayed 32-byte
// aligned and monotone. Two invariants are asserted per kernel:
//   * FMP integrity — no kernel moves or corrupts the free-memory pointer;
//   * write footprint — the decode / matvec / UseHint kernels write only inside
//     their own allocations (spill == 0). The SHIPPED SHAKE256 squeeze
//     (src/FastKeccak170.sol) now also spills NOTHING: its fifth store is placed
//     at outPtr+104 and carries lanes 13..16, so it lands flush with the end of
//     the 136-byte rate block instead of overhanging it by 24 bytes, and the
//     absorb's lane-16 load reads ptr+104 rather than ptr+128 for the same
//     reason. That is asserted EXACTLY (spill == 0), not as a bound, so a
//     regression to the old overhanging form fails this test rather than
//     shrinking a margin. The reference twin in test/ZZZ_FastKeccak170.sol keeps
//     the 160-byte form on purpose — it is the differential oracle — and stays
//     bounded rather than exact.
//
// Also asserted: the variable-length SHAKE256 absorb matches the repo's
// reference sponge for every length in 0..300 and at every rate boundary, and
// both verifiers stay fail-closed (no revert, no false accept) across message
// lengths straddling the mu-absorb rate boundary — after which the genuine
// tuple still verifies TRUE (whole-run memory sanity).
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {IMLDSAVerifier} from "../src/IMLDSAVerifier.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {shakeInit, shakeUpdate, shakeDigest} from "./vendor/ZKNOX_shake.sol";
import {_F1600_AT, _F1600_CODE, shake256Fast} from "./ZZZ_FastKeccak.sol";
import {shake256Fast170} from "../src/FastKeccak170.sol";
import {unpackHFast} from "./ZZZ_decode.t.sol";
import {unpackZFast2, useHintFast2} from "./ZZZ_decode2.t.sol";
import {ZZZ_E2ERef, unpackZStrict, packFromFlat, sampleInBallE2E} from "./ZZZ_E2ERef.sol";
import {
    unpackHFast as unpackHFastSrc,
    unpackZPacked,
    useHintSwar,
    sampleInBallPacked,
    matvecRow
} from "../src/Decode.sol";

/// @dev paints the free memory above the FMP with a sentinel, runs a kernel,
///      then reports how far past the post-call FMP the sentinel was destroyed
///      and whether the FMP itself stayed sane.
contract SECMemProbe {
    uint256 constant PAT = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5;
    uint256 constant WINDOW = 8192;

    function _paint() private pure returns (uint256 f0) {
        assembly ("memory-safe") {
            f0 := mload(0x40)
            for { let p := f0 } lt(p, add(f0, WINDOW)) { p := add(p, 32) } { mstore(p, PAT) }
        }
    }

    function _scan(uint256 f0) private pure returns (uint256 fmpAfter, uint256 spillBytes) {
        assembly ("memory-safe") {
            fmpAfter := mload(0x40)
            let last := 0
            for { let p := fmpAfter } lt(p, add(f0, WINDOW)) { p := add(p, 32) } {
                if iszero(eq(mload(p), PAT)) { last := add(sub(p, fmpAfter), 32) }
            }
            spillBytes := last
        }
    }

    // ---- shared / reference sponge ---------------------------------------

    function probeShakeRef(uint256 inLen, uint256 outLen) external pure returns (uint256 spill, bool fmpOk) {
        bytes memory input = new bytes(inLen);
        uint256 f0 = _paint();
        bytes memory out = shake256Fast(input, outLen);
        (uint256 f1, uint256 s) = _scan(f0);
        require(out.length == outLen, "outLen");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeShake170(uint256 inLen, uint256 outLen, address helper)
        external
        view
        returns (uint256 spill, bool fmpOk)
    {
        bytes memory input = new bytes(inLen);
        uint256 f0 = _paint();
        bytes memory out = shake256Fast170(input, outLen, helper);
        (uint256 f1, uint256 s) = _scan(f0);
        require(out.length == outLen, "outLen");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    // ---- reference kernels ------------------------------------------------

    function probeUnpackZFast2(bytes memory zb) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        (uint256[] memory z,) = unpackZFast2(zb);
        (uint256 f1, uint256 s) = _scan(f0);
        require(z.length == 1024, "z");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeUnpackZStrict(bytes memory zb) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        (uint256[] memory z,) = unpackZStrict(zb);
        (uint256 f1, uint256 s) = _scan(f0);
        require(z.length == 1024, "z");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeUnpackHTest(bytes memory hb) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        unpackHFast(hb);
        (uint256 f1, uint256 s) = _scan(f0);
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeUseHintFast2(uint256[4] memory masks, uint256[][] memory r)
        external
        pure
        returns (uint256 spill, bool fmpOk)
    {
        uint256 f0 = _paint();
        bytes memory w1 = useHintFast2(masks, r);
        (uint256 f1, uint256 s) = _scan(f0);
        require(w1.length == 768, "w1");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeSampleInBallE2E(bytes32 ct) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        uint256[] memory c = sampleInBallE2E(ct);
        (uint256 f1, uint256 s) = _scan(f0);
        require(c.length == 256, "c");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probePackFromFlat(uint256[] memory flat) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        uint256[] memory w = packFromFlat(flat, 0);
        (uint256 f1, uint256 s) = _scan(f0);
        require(w.length == 64, "w");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    // ---- shipped kernels (src/Decode.sol) --------------------------------

    function probeUnpackZPacked(bytes memory zb) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        (uint256[][] memory zp,) = unpackZPacked(zb);
        (uint256 f1, uint256 s) = _scan(f0);
        require(zp.length == 4 && zp[3].length == 64, "zp");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeUnpackHSrc(bytes memory hb) external pure returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        unpackHFastSrc(hb);
        (uint256 f1, uint256 s) = _scan(f0);
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeUseHintSwar(uint256[4] memory masks, uint256[][] memory r)
        external
        pure
        returns (uint256 spill, bool fmpOk)
    {
        uint256 f0 = _paint();
        bytes memory w1 = useHintSwar(masks, r);
        (uint256 f1, uint256 s) = _scan(f0);
        require(w1.length == 768, "w1");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeSampleInBallPacked(bytes32 ct, address helper) external view returns (uint256 spill, bool fmpOk) {
        uint256 f0 = _paint();
        uint256[] memory c = sampleInBallPacked(ct, helper);
        (uint256 f1, uint256 s) = _scan(f0);
        require(c.length == 64, "c");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }

    function probeMatvecRow() external pure returns (uint256 spill, bool fmpOk) {
        uint256[][] memory z = new uint256[][](4);
        for (uint256 j = 0; j < 4; ++j) {
            z[j] = new uint256[](64);
        }
        uint256[] memory c = new uint256[](64);
        uint256[] memory abuf = new uint256[](128); // 4096-byte A region (4 polys)
        uint256[] memory tbuf = new uint256[](32); // 1024-byte t1 region
        uint256 aPtr;
        uint256 tPtr;
        assembly ("memory-safe") {
            aPtr := add(abuf, 0x20)
            tPtr := add(tbuf, 0x20)
        }
        uint256 f0 = _paint();
        uint256[] memory acc = matvecRow(aPtr, z, c, tPtr);
        (uint256 f1, uint256 s) = _scan(f0);
        require(acc.length == 64, "acc");
        spill = s;
        fmpOk = (f1 >= f0) && (f1 % 32 == 0);
    }
}

contract SECMemSafetyTest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant SEED = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";

    address f1600;
    MLDSA44Verifier shipped;
    ZZZ_E2ERef refv;
    SECMemProbe probe;

    bytes sig;
    bytes msg_;
    address shipPk;
    address refPk;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        f1600 = deployF1600_170();
        shipped = new MLDSA44Verifier(f1600);
        refv = new ZZZ_E2ERef();
        probe = new SECMemProbe();

        bytes memory pkBlob;
        (sig, pkBlob, msg_) = _vec(SEED, MSG1_HEX);
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

    // ============================================ variable-length absorb ====

    function test_shake_variable_length_matches_reference() public view {
        for (uint256 len = 0; len <= 300; ++len) {
            bytes memory input = new bytes(len);
            for (uint256 i = 0; i < len; ++i) {
                input[i] = bytes1(uint8((i * 31 + len) & 0xff));
            }
            bytes memory want = shakeDigest(shakeUpdate(shakeInit(), input), 64);
            assertEq(shake256Fast(input, 64), want, "reference sponge mismatch");
            assertEq(shake256Fast170(input, 64, f1600), want, "shipped sponge mismatch");
        }
    }

    function test_shake_rate_boundaries() public view {
        uint256[12] memory lens = [uint256(0), 1, 135, 136, 137, 271, 272, 273, 407, 408, 409, 1088];
        uint256[4] memory outs = [uint256(32), 64, 136, 272];
        for (uint256 a = 0; a < 12; ++a) {
            bytes memory input = new bytes(lens[a]);
            for (uint256 i = 0; i < lens[a]; ++i) {
                input[i] = bytes1(uint8((i * 7 + 1) & 0xff));
            }
            for (uint256 b = 0; b < 4; ++b) {
                bytes memory want = shakeDigest(shakeUpdate(shakeInit(), input), outs[b]);
                assertEq(shake256Fast(input, outs[b]), want, "reference rate-boundary mismatch");
                assertEq(shake256Fast170(input, outs[b], f1600), want, "shipped rate-boundary mismatch");
            }
        }
    }

    // ================================================ SHAKE squeeze footprint

    function test_shake_squeeze_write_footprint_is_bounded() public view {
        uint16[4] memory ins = [uint16(98), 98, 832, 832];
        uint16[4] memory outs = [uint16(32), 64, 136, 272];
        for (uint256 i = 0; i < 4; ++i) {
            (uint256 sRef, bool okRef) = probe.probeShakeRef(ins[i], outs[i]);
            (uint256 s170, bool ok170) = probe.probeShake170(ins[i], outs[i], f1600);
            assertTrue(okRef && ok170, "FMP must stay sane (32-byte aligned, monotone)");
            assertLe(sRef, 160, "reference squeeze footprint bounded by 160 bytes/block");
            // EXACT, not bounded: _squeezeBlockFast170's fifth store lands flush
            // with the end of the 136-byte rate block, so the shipped squeeze
            // writes nothing past the caller's buffer at any outLen. This is the
            // pin that keeps docs/SAFETY.md 4.1's correction from regressing.
            assertEq(s170, 0, "shipped squeeze must write NOTHING past its buffer");
            console.log("squeeze spill ref / shipped:", sRef, s170);
        }
    }

    // ==================================== every decode/matvec kernel in bounds

    function test_reference_kernels_do_not_write_past_their_allocation() public view {
        bytes memory zb = new bytes(2304);
        for (uint256 i = 0; i < 2304; ++i) {
            zb[i] = bytes1(uint8(uint256(keccak256(abi.encode("zb", i))) & 0xff));
        }
        (uint256 s1, bool k1) = probe.probeUnpackZFast2(zb);
        assertTrue(k1 && s1 == 0, "unpackZFast2");
        (uint256 s2, bool k2) = probe.probeUnpackZStrict(zb);
        assertTrue(k2 && s2 == 0, "unpackZStrict");
        (uint256 s3, bool k3) = probe.probeUnpackHTest(new bytes(84));
        assertTrue(k3 && s3 == 0, "unpackHFast (test)");

        uint256[4] memory masks = [type(uint256).max, 0, 12345, type(uint256).max];
        uint256[][] memory r = _canonicalRows();
        (uint256 s4, bool k4) = probe.probeUseHintFast2(masks, r);
        assertTrue(k4 && s4 == 0, "useHintFast2 (768-byte output)");

        (uint256 s5, bool k5) = probe.probeSampleInBallE2E(keccak256("ct"));
        assertTrue(k5 && s5 == 0, "sampleInBallE2E (168-byte block buffer)");

        uint256[] memory flat = new uint256[](1024);
        (uint256 s6, bool k6) = probe.probePackFromFlat(flat);
        assertTrue(k6 && s6 == 0, "packFromFlat");
    }

    function test_shipped_kernels_do_not_write_past_their_allocation() public view {
        bytes memory zb = new bytes(2304);
        for (uint256 i = 0; i < 2304; ++i) {
            zb[i] = bytes1(uint8(uint256(keccak256(abi.encode("zb", i))) & 0xff));
        }
        (uint256 s1, bool k1) = probe.probeUnpackZPacked(zb);
        assertTrue(k1 && s1 == 0, "unpackZPacked");
        (uint256 s2, bool k2) = probe.probeUnpackHSrc(new bytes(84));
        assertTrue(k2 && s2 == 0, "unpackHFast (src)");

        uint256[4] memory masks = [type(uint256).max, 0, 12345, type(uint256).max];
        uint256[][] memory r = _canonicalRows();
        (uint256 s3, bool k3) = probe.probeUseHintSwar(masks, r);
        assertTrue(k3 && s3 == 0, "useHintSwar (768-byte output)");

        (uint256 s4, bool k4) = probe.probeSampleInBallPacked(keccak256("ct"), f1600);
        assertTrue(k4 && s4 == 0, "sampleInBallPacked (168-byte block buffer)");

        (uint256 s5, bool k5) = probe.probeMatvecRow();
        assertTrue(k5 && s5 == 0, "matvecRow (raw-allocated accumulator)");
    }

    function _canonicalRows() internal pure returns (uint256[][] memory r) {
        r = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            r[i] = new uint256[](64);
            for (uint256 w = 0; w < 64; ++w) {
                uint256 word;
                for (uint256 lane = 0; lane < 4; ++lane) {
                    uint256 v = uint256(keccak256(abi.encode("r", i, w, lane))) % 8380417; // canonical < q
                    word |= v << (64 * lane);
                }
                r[i][w] = word;
            }
        }
    }

    // ================================== attacker-controlled message lengths ==

    function test_verifiers_stay_fail_closed_across_message_lengths() public {
        assertTrue(shipped.verify(shipPk, msg_, sig), "shipped sanity");
        assertTrue(refv.verify(refPk, msg_, sig), "reference sanity");

        // lengths straddling the mu-absorb rate boundary (muIn = 66 + |M|, rate 136),
        // plus 734 — the length at which muIn is exactly 800 bytes and therefore
        // collides with the helper's raw-permutation dispatch, so `_computeMu`
        // falls back to the lane-level sponge. That branch had no execution
        // evidence anywhere in the corpus before this.
        uint256[11] memory lens = [uint256(0), 1, 69, 70, 71, 135, 136, 137, 271, 272, 734];
        for (uint256 k = 0; k < 11; ++k) {
            bytes memory m = new bytes(lens[k]);
            for (uint256 i = 0; i < lens[k]; ++i) {
                m[i] = bytes1(uint8((i + k) & 0xff));
            }
            _assertFailClosed(address(shipped), shipPk, m, string.concat("shipped |M| = ", vm.toString(lens[k])));
            _assertFailClosed(address(refv), refPk, m, string.concat("reference |M| = ", vm.toString(lens[k])));
        }
        // whole-run memory sanity: the genuine tuple still verifies
        assertTrue(shipped.verify(shipPk, msg_, sig), "shipped post-sweep sanity");
        assertTrue(refv.verify(refPk, msg_, sig), "reference post-sweep sanity");
    }

    function _assertFailClosed(address v, address pkc, bytes memory m, string memory why) internal view {
        (bool ok, bytes memory ret) = v.staticcall(abi.encodeCall(IMLDSAVerifier.verify, (pkc, m, sig)));
        assertTrue(ok, string.concat(why, ": must not revert"));
        assertFalse(abi.decode(ret, (bool)), string.concat(why, ": wrong message must not verify"));
    }
}
