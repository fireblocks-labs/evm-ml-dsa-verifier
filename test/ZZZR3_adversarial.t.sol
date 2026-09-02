// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/ZZZR3_adversarial.t.sol
//
// Adversarial cases against both verifier subjects — the shipped MLDSA44Verifier
// and the reference ZZZ_E2ERef — beyond the happy-path e2e suites:
//   * message lengths straddling the mu-absorb rate boundary verify TRUE, and a
//     truncated message with the same signature does not;
//   * cross-key splice: a signature valid under key A must not verify under key B;
//   * cross-message splice: a signature over M1 must not verify M2 under the same
//     key;
//   * universal-forgery attempts (all-zero / all-0xff / structurally-random
//     signatures) against a genuine key are never accepted and never revert;
//   * wrong signature length and malformed / wrong-size public-key contracts
//     are rejected without reverting;
//   * zeroing the signature's hint region (a valid weight-0 HintBitUnpack
//     encoding, but not this signature's) is rejected;
//   * verify() is stateless: a warm repeat call costs no more than the cold one.
//
// This file carries the cross-key and cross-message splice coverage for the
// suite (there is no separate corpus generator).
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {IMLDSAVerifier} from "../src/IMLDSAVerifier.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {ZZZ_E2ERef, E2E_PK_SIZE} from "./ZZZ_E2ERef.sol";

contract ZZZR3AdversarialTest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant SEED_A = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    string constant SEED_B = "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20";
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";

    address f1600;
    MLDSA44Verifier shipped;
    ZZZ_E2ERef refv;

    bytes sigA;
    bytes msgA;
    address shipPkA;
    address refPkA;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        f1600 = deployF1600_170();
        shipped = new MLDSA44Verifier(f1600);
        refv = new ZZZ_E2ERef();

        bytes memory pkBlob;
        (sigA, pkBlob, msgA) = _vec(SEED_A, MSG1_HEX);
        shipPkA = _deployData(bytes.concat(hex"00", pkBlob));
        refPkA = _deployData(pkBlob);
    }

    // --------------------------------------------------------------- fixtures

    function _vec(string memory seedHex, string memory msgHex)
        internal
        returns (bytes memory sig, bytes memory pkBlob, bytes memory m)
    {
        string[] memory cmds = new string[](5);
        cmds[0] = PY;
        cmds[1] = VECGEN;
        cmds[2] = "seed";
        cmds[3] = seedHex;
        cmds[4] = msgHex;
        (sig, pkBlob, m) = abi.decode(vm.ffi(cmds), (bytes, bytes, bytes));
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

    /// verify on both subjects; assert no revert and return the common verdict.
    function _bothVerdict(address shipPk, address refPk, bytes memory m, bytes memory sig)
        internal
        view
        returns (bool shipRes, bool refRes)
    {
        (bool okS, bytes memory rs) = address(shipped).staticcall(abi.encodeCall(IMLDSAVerifier.verify, (shipPk, m, sig)));
        (bool okR, bytes memory rr) = address(refv).staticcall(abi.encodeCall(ZZZ_E2ERef.verify, (refPk, m, sig)));
        assertTrue(okS, "shipped must not revert");
        assertTrue(okR, "reference must not revert");
        shipRes = abi.decode(rs, (bool));
        refRes = abi.decode(rr, (bool));
    }

    function _slice(bytes memory b, uint256 start, uint256 len) internal pure returns (bytes memory o) {
        o = new bytes(len);
        for (uint256 i = 0; i < len; ++i) {
            o[i] = b[start + i];
        }
    }

    // ================================= message length boundaries ============

    function test_message_length_boundaries_both_subjects() public {
        // muIn = 66 + |M|; these lengths cross the SHAKE256 rate boundary (136).
        //
        // |M| = 734 is the ONE length that takes a different code path: the mu
        // preimage is then exactly 800 bytes, which the helper's batched entry
        // point dispatches as a RAW Keccak-f[1600] permutation, so
        // `_computeMu` falls back to the lane-level sponge `shake256Fast170`.
        // It was the only branch in the contract with no execution evidence
        // anywhere in the corpus; a genuine signature must still verify through
        // it, and a truncated message must still fail.
        uint256[6] memory lens = [uint256(0), 69, 70, 100, 206, 734];
        for (uint256 k = 0; k < 6; ++k) {
            bytes memory m = new bytes(lens[k]);
            for (uint256 i = 0; i < lens[k]; ++i) {
                m[i] = bytes1(uint8((i * 7 + k + 1) & 0xff));
            }
            (bytes memory sig, bytes memory pkBlob, bytes memory mm) = _vec(SEED_A, vm.toString(m));
            assertEq(keccak256(mm), keccak256(m), "fixture message round-trips");
            address shipPk = _deployData(bytes.concat(hex"00", pkBlob));
            address refPk = _deployData(pkBlob);

            (bool s, bool r) = _bothVerdict(shipPk, refPk, m, sig);
            assertTrue(s, string.concat("shipped must verify |M| = ", vm.toString(lens[k])));
            assertTrue(r, string.concat("reference must verify |M| = ", vm.toString(lens[k])));

            if (lens[k] > 0) {
                bytes memory mShort = _slice(m, 0, lens[k] - 1);
                (bool s2, bool r2) = _bothVerdict(shipPk, refPk, mShort, sig);
                assertFalse(s2, "shipped: truncated message must fail");
                assertFalse(r2, "reference: truncated message must fail");
            }
        }
    }

    // ================================= cross-key splice =====================

    function test_cross_key_splice_rejected() public {
        bytes memory sigB;
        bytes memory msgB;
        address shipPkB;
        address refPkB;
        {
            bytes memory pkBlobB;
            (sigB, pkBlobB, msgB) = _vec(SEED_B, MSG1_HEX);
            shipPkB = _deployData(bytes.concat(hex"00", pkBlobB));
            refPkB = _deployData(pkBlobB);
        }

        // sanity: each signature verifies under its OWN key
        {
            (bool sA, bool rA) = _bothVerdict(shipPkA, refPkA, msgA, sigA);
            assertTrue(sA && rA, "A verifies under key A");
            (bool sB, bool rB) = _bothVerdict(shipPkB, refPkB, msgB, sigB);
            assertTrue(sB && rB, "B verifies under key B");
        }
        // splice: A's signature under key B, and B's under key A -> rejected
        {
            (bool s1, bool r1) = _bothVerdict(shipPkB, refPkB, msgA, sigA);
            assertFalse(s1 || r1, "A's signature must not verify under key B");
            (bool s2, bool r2) = _bothVerdict(shipPkA, refPkA, msgB, sigB);
            assertFalse(s2 || r2, "B's signature must not verify under key A");
        }
    }

    // ================================= cross-message splice =================

    function test_cross_message_splice_rejected() public {
        string memory msg2Hex = "0x2222333344445555222233334444555522223333444455552222333344445555";
        (bytes memory sig2, bytes memory pkBlob, bytes memory msg2) = _vec(SEED_A, msg2Hex);
        // same key as A
        address shipPk = _deployData(bytes.concat(hex"00", pkBlob));
        address refPk = _deployData(pkBlob);

        // each verifies its own message
        {
            (bool s1, bool r1) = _bothVerdict(shipPk, refPk, msg2, sig2);
            assertTrue(s1 && r1, "sig2 verifies msg2");
        }
        // splice: sig over msg2 does not verify msgA, and sigA does not verify msg2
        {
            (bool s2, bool r2) = _bothVerdict(shipPk, refPk, msgA, sig2);
            assertFalse(s2 || r2, "sig2 must not verify msgA");
            (bool s3, bool r3) = _bothVerdict(shipPk, refPk, msg2, sigA);
            assertFalse(s3 || r3, "sigA must not verify msg2");
        }
    }

    // ================================= universal-forgery attempts ===========

    function test_universal_forgery_attempts_rejected() public {
        bytes[3] memory forgeries;
        forgeries[0] = new bytes(2420); // all-zero
        forgeries[1] = _fill(2420, 0xff); // all-0xff
        {
            bytes memory rnd = new bytes(2420);
            for (uint256 i = 0; i < 2420; ++i) {
                rnd[i] = bytes1(uint8(uint256(keccak256(abi.encode("forge", i))) & 0xff));
            }
            forgeries[2] = rnd;
        }
        for (uint256 i = 0; i < 3; ++i) {
            (bool s, bool r) = _bothVerdict(shipPkA, refPkA, msgA, forgeries[i]);
            assertFalse(s, "shipped: forged signature must not be accepted");
            assertFalse(r, "reference: forged signature must not be accepted");
        }
    }

    function _fill(uint256 n, uint8 v) internal pure returns (bytes memory b) {
        b = new bytes(n);
        for (uint256 i = 0; i < n; ++i) {
            b[i] = bytes1(v);
        }
    }

    // ================================= wrong lengths / bad pk contracts ======

    function test_wrong_signature_length_and_bad_pk_are_fail_closed() public {
        // sanity
        (bool s0, bool r0) = _bothVerdict(shipPkA, refPkA, msgA, sigA);
        assertTrue(s0 && r0, "sanity");

        // wrong signature length -> false, no revert
        (bool s1, bool r1) = _bothVerdict(shipPkA, refPkA, msgA, _slice(sigA, 0, 2419));
        assertFalse(s1 || r1, "2419-byte sig");
        (bool s2, bool r2) = _bothVerdict(shipPkA, refPkA, msgA, bytes.concat(sigA, hex"00"));
        assertFalse(s2 || r2, "2421-byte sig");

        // codeless / wrong-size pk contracts -> false, no revert
        (s1, r1) = _bothVerdict(address(0xdead), address(0xdead), msgA, sigA);
        assertFalse(s1 || r1, "codeless pk");
        address shortShip = _deployData(new bytes(E2E_PK_SIZE)); // shipped wants 20545
        address shortRef = _deployData(new bytes(E2E_PK_SIZE - 1)); // reference wants 20544
        assertFalse(shipped.verify(shortShip, msgA, sigA), "shipped: missing-prefix pk");
        assertFalse(refv.verify(shortRef, msgA, sigA), "reference: short pk");
    }

    // ================================= tampered hint region ==================

    function test_zeroed_hint_region_rejected() public {
        // a genuine signature carries a non-zero hint region [2336:2420]
        bool hasHint = false;
        for (uint256 i = 2336; i < 2420; ++i) {
            if (sigA[i] != 0) hasHint = true;
        }
        assertTrue(hasHint, "fixture signature has a non-zero hint region");

        // zeroing it is a VALID weight-0 HintBitUnpack encoding, but not this
        // signature's hints -> both subjects reject.
        bytes memory s = bytes.concat(sigA);
        for (uint256 i = 2336; i < 2420; ++i) {
            s[i] = 0;
        }
        (bool sr, bool rr) = _bothVerdict(shipPkA, refPkA, msgA, s);
        assertFalse(sr || rr, "weight-0 hint region must be rejected");
    }

    // ================================= statelessness (cold vs warm) ==========

    function test_repeat_call_is_not_more_expensive() public view {
        uint256 g0 = gasleft();
        bool ok1 = shipped.verify(shipPkA, msgA, sigA);
        uint256 cold = g0 - gasleft();
        g0 = gasleft();
        bool ok2 = shipped.verify(shipPkA, msgA, sigA);
        uint256 warm = g0 - gasleft();
        assertTrue(ok1 && ok2, "both calls TRUE");
        assertLe(warm, cold, "a warm repeat must not cost more than the cold call");
        console.log("shipped verify gas cold / warm:", cold, warm);
    }
}
