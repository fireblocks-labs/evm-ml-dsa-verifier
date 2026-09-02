// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC2_Fips204Gates.t.sol
//
// FIPS 204 validity checks that implementations are known to get wrong, tested on
// the components both verifier subjects use: the HintBitUnpack decoder
// (unpackHFast, identical in src/Decode.sol and test/ZZZ_decode.t.sol), the
// strict z-norm decoders (unpackZPacked / unpackZStrict), the fused
// UseHint+w1Encode kernels (useHintSwar / useHintFast2), and the assembled
// verifiers themselves (MLDSA44Verifier and the reference ZZZ_E2ERef).
//
// Provenance of the checked properties: FIPS 204 final (Aug 2024) Algorithms 3
// (Verify), 21 (HintBitUnpack), 27 (sigDecode), 28 (w1Encode), 40 (UseHint) and
// §3.6.2; the NIST pqc-forum "Dilithium hint unpacking" thread (2024) and FIPS
// 204 Appendix D; the RustCrypto ml-dsa "repeated hint" advisory (CVE-2026-24850);
// libcrux PR #1347 (the ‖z‖∞ bound 2γ1−β) and PR #1348 (the final-row ω check
// that never fired).
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {IMLDSAVerifier} from "../src/IMLDSAVerifier.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {ZZZ_E2ERef, unpackZStrict} from "./ZZZ_E2ERef.sol";
import {unpackHFast} from "./ZZZ_decode.t.sol";
import {useHintFast2} from "./ZZZ_decode2.t.sol";
import {packCoeffs} from "./ZZZ_NttVariants.sol";
import {unpackHFast as unpackHFastSrc, unpackZPacked, useHintSwar} from "../src/Decode.sol";

contract SEC2Fips204GatesTest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant SEED = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";

    uint256 constant OMEGA = 80;
    uint256 constant KDIM = 4;
    uint256 constant Q = 8380417;
    uint256 constant GAMMA1 = 131072;
    uint256 constant GAMMA2 = 95232;
    uint256 constant ALPHA = 190464;
    uint256 constant MHI = 44;

    address f1600;
    MLDSA44Verifier shipped;
    ZZZ_E2ERef refv;

    bytes sig;
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

    function _shipVerify(bytes memory m, bytes memory s) internal view returns (bool ok, bool res) {
        bytes memory ret;
        (ok, ret) = address(shipped).staticcall(abi.encodeCall(IMLDSAVerifier.verify, (shipPk, m, s)));
        res = ok && ret.length == 32 && abi.decode(ret, (bool));
    }

    function _refVerify(bytes memory m, bytes memory s) internal view returns (bool ok, bool res) {
        bytes memory ret;
        (ok, ret) = address(refv).staticcall(abi.encodeCall(ZZZ_E2ERef.verify, (refPk, m, s)));
        res = ok && ret.length == 32 && abi.decode(ret, (bool));
    }

    // ------------------------------------------- HintBitUnpack encoding helpers

    /// canonical 84-byte hint encoding for the given per-row index lists.
    function _encodeH(uint8[][] memory rows) internal pure returns (bytes memory y) {
        y = new bytes(84);
        uint256 idx = 0;
        for (uint256 i = 0; i < KDIM; ++i) {
            for (uint256 j = 0; j < rows[i].length; ++j) {
                y[idx++] = bytes1(rows[i][j]);
            }
            y[OMEGA + i] = bytes1(uint8(idx));
        }
    }

    function _rows(uint8[] memory a, uint8[] memory b, uint8[] memory c, uint8[] memory d)
        internal
        pure
        returns (uint8[][] memory r)
    {
        r = new uint8[][](4);
        r[0] = a;
        r[1] = b;
        r[2] = c;
        r[3] = d;
    }

    function _u8(uint8 a) internal pure returns (uint8[] memory r) {
        r = new uint8[](1);
        r[0] = a;
    }

    function _u8(uint8 a, uint8 b) internal pure returns (uint8[] memory r) {
        r = new uint8[](2);
        r[0] = a;
        r[1] = b;
    }

    function _u8(uint8 a, uint8 b, uint8 c) internal pure returns (uint8[] memory r) {
        r = new uint8[](3);
        r[0] = a;
        r[1] = b;
        r[2] = c;
    }

    function _empty() internal pure returns (uint8[] memory r) {
        r = new uint8[](0);
    }

    // ============================ HintBitUnpack cut-counter checks (Alg. 21) ==

    /// The cumulative cut counters are only NON-strictly monotone: a polynomial
    /// with zero hints is legal and must be accepted; a counter that runs
    /// backwards (FIPS 204 Alg. 21 line 4) must be rejected.
    function test_empty_rows_legal_and_decreasing_counter_rejected() public pure {
        bytes memory ok_ = _encodeH(_rows(_u8(3, 9), _empty(), _u8(1), _empty()));
        (bool okv, uint256[4] memory masks, uint256 weight) = unpackHFastSrc(ok_);
        assertTrue(okv, "empty rows must be accepted (y[w+i] == y[w+i-1])");
        assertEq(masks[0], (uint256(1) << 3) | (uint256(1) << 9), "row 0 mask");
        assertEq(masks[1], 0, "row 1 empty");
        assertEq(masks[2], uint256(1) << 1, "row 2 mask");
        assertEq(weight, 3, "weight");

        // indices chosen globally increasing so only the counter rule can fire
        bytes memory y = _encodeH(_rows(_u8(1, 2), _u8(3), _empty(), _empty()));
        (bool ok0,,) = unpackHFastSrc(y);
        assertTrue(ok0, "baseline valid");
        y[OMEGA] = bytes1(uint8(3));
        y[OMEGA + 1] = bytes1(uint8(2)); // y[81] < y[80]
        (bool bad,,) = unpackHFastSrc(y);
        assertFalse(bad, "decreasing cut counter must be rejected");
    }

    /// `y[ω+i] > ω` must be rejected for EVERY row, including the LAST
    /// (libcrux PR #1348: the final row's overflow must still fire).
    function test_omega_overflow_rejected_in_every_row_including_last() public pure {
        for (uint256 i = 0; i < KDIM; ++i) {
            bytes memory y = _encodeH(_rows(_u8(1), _u8(2), _u8(3), _u8(4)));
            (bool ok0,,) = unpackHFastSrc(y);
            assertTrue(ok0, "baseline valid");
            for (uint256 j = i; j < KDIM; ++j) {
                y[OMEGA + j] = bytes1(uint8(OMEGA + 1)); // keep later counters >= this one
            }
            (bool bad,,) = unpackHFastSrc(y);
            assertFalse(bad, "y[omega+i] > omega must be rejected");
        }
    }

    /// The total weight can never exceed ω, and ω itself is reachable.
    function test_weight_bounded_by_omega_and_omega_reachable() public pure {
        uint8[] memory full = new uint8[](OMEGA);
        for (uint256 j = 0; j < OMEGA; ++j) {
            full[j] = uint8(j);
        }
        bytes memory y = _encodeH(_rows(full, _empty(), _empty(), _empty()));
        (bool okv,, uint256 weight) = unpackHFastSrc(y);
        assertTrue(okv, "a full-weight signature is legal");
        assertEq(weight, OMEGA, "weight == omega");
    }

    // =========================== HintBitUnpack index-ordering checks (Alg. 21) =

    /// Indices inside one polynomial must be STRICTLY increasing: a repeated
    /// index is CVE-2026-24850 (`<=` where FIPS requires `<`); a descending pair
    /// is the original 2024 finding.
    function test_repeated_and_unsorted_indices_rejected() public pure {
        (bool okA,,) = unpackHFastSrc(_encodeH(_rows(_u8(5, 5), _empty(), _empty(), _empty())));
        assertFalse(okA, "repeated index must be rejected (CVE-2026-24850)");
        (bool okB,,) = unpackHFastSrc(_encodeH(_rows(_u8(9, 3), _empty(), _empty(), _empty())));
        assertFalse(okB, "descending indices must be rejected");
        (bool okC,,) = unpackHFastSrc(_encodeH(_rows(_u8(3, 9), _empty(), _empty(), _empty())));
        assertTrue(okC, "ascending indices are the canonical form");
    }

    /// The strict-increase check must RESET at each polynomial boundary
    /// (`First <- Index`): a verifier that compares across rows false-rejects
    /// valid signatures.
    function test_strict_increase_resets_per_polynomial() public pure {
        bytes memory y = _encodeH(_rows(_u8(7, 200), _u8(1, 2), _u8(0), _u8(255)));
        (bool okv, uint256[4] memory masks, uint256 weight) = unpackHFastSrc(y);
        assertTrue(okv, "descending ACROSS a row boundary is legal");
        assertEq(masks[0], (uint256(1) << 7) | (uint256(1) << 200), "row 0");
        assertEq(masks[1], (uint256(1) << 1) | (uint256(1) << 2), "row 1");
        assertEq(masks[2], uint256(1) << 0, "row 2 (index 0 is legal)");
        assertEq(masks[3], uint256(1) << 255, "row 3 (index 255 is legal)");
        assertEq(weight, 6, "weight");
    }

    /// Every unused index byte must be zero (FIPS 204 Alg. 21 lines 16-18);
    /// otherwise each unused slot multiplies the number of accepted encodings.
    function test_nonzero_padding_rejected_at_every_position() public pure {
        bytes memory base = _encodeH(_rows(_u8(3, 9), _u8(1), _empty(), _empty()));
        (bool ok0,,) = unpackHFastSrc(base);
        assertTrue(ok0, "baseline valid");
        uint256 used = 3;
        for (uint256 p = used; p < OMEGA; ++p) {
            bytes memory y = bytes.concat(base);
            y[p] = bytes1(uint8(0xAB));
            (bool bad,,) = unpackHFastSrc(y);
            assertFalse(bad, "nonzero padding byte must be rejected");
        }
    }

    /// Canonicality / no malleability: the accepted encoding is UNIQUE per hint
    /// set. Every single-byte mutation of a canonical encoding is either rejected
    /// or decodes to a DIFFERENT hint set.
    function test_no_single_byte_reencoding_of_the_same_hint_set() public pure {
        bytes memory base = _encodeH(_rows(_u8(3, 9, 40), _u8(1), _empty(), _u8(200)));
        (bool ok0, uint256[4] memory m0,) = unpackHFastSrc(base);
        assertTrue(ok0, "baseline valid");

        uint256 collisions;
        for (uint256 p = 0; p < 84; ++p) {
            for (uint256 vv = 0; vv < 256; vv += 7) {
                if (uint8(base[p]) == uint8(vv)) continue;
                bytes memory y = bytes.concat(base);
                y[p] = bytes1(uint8(vv));
                (bool okv, uint256[4] memory m,) = unpackHFastSrc(y);
                if (!okv) continue;
                if (m[0] == m0[0] && m[1] == m0[1] && m[2] == m0[2] && m[3] == m0[3]) ++collisions;
            }
        }
        assertEq(collisions, 0, "no distinct encoding decodes to the same hint set");
    }

    /// The HintBitUnpack decoder is identical across the two deployable builds:
    /// src/Decode.sol and test/ZZZ_decode.t.sol must agree on every witness, in
    /// both directions.
    function test_hint_decoder_is_identical_across_builds() public pure {
        bytes[6] memory cases;
        cases[0] = _encodeH(_rows(_u8(3, 9, 40), _u8(1), _empty(), _u8(200))); // valid
        cases[1] = _encodeH(_rows(_u8(5, 5), _empty(), _empty(), _empty())); // repeated
        cases[2] = _encodeH(_rows(_u8(9, 3), _empty(), _empty(), _empty())); // descending
        cases[3] = _encodeH(_rows(_u8(1), _u8(2), _u8(3), _u8(4))); // valid
        {
            bytes memory pad = _encodeH(_rows(_u8(3, 9), _u8(1), _empty(), _empty()));
            pad[40] = bytes1(uint8(1)); // nonzero padding
            cases[4] = pad;
        }
        {
            bytes memory ov = _encodeH(_rows(_u8(1), _u8(2), _u8(3), _u8(4)));
            ov[83] = bytes1(uint8(OMEGA + 1)); // cut above omega
            cases[5] = ov;
        }
        for (uint256 i = 0; i < 6; ++i) {
            (bool okSrc, uint256[4] memory ms,) = unpackHFastSrc(cases[i]);
            (bool okTest, uint256[4] memory mt,) = unpackHFast(cases[i]);
            assertEq(okSrc, okTest, "decoders must agree on validity");
            if (okSrc) {
                for (uint256 k = 0; k < 4; ++k) {
                    assertEq(ms[k], mt[k], "decoders must agree on masks");
                }
            }
        }
    }

    // ============================== strict z-norm boundary (both decoders) =====

    /// ||z||inf < gamma1 - beta is a STRICT bound (FIPS 204 Alg. 3). In the
    /// packed 18-bit encoding this is exactly v in [79, 262065]: v = 78
    /// (|z| = gamma1 - beta) and v = 262066 must be rejected, v = 79 and
    /// v = 262065 accepted. Pinned on both the shipped and reference decoders.
    function test_strict_z_norm_boundary_both_decoders() public pure {
        uint256[8] memory positions = [uint256(0), 1, 2, 3, 31, 32, 255, 1023];
        for (uint256 p = 0; p < 8; ++p) {
            uint256 j = positions[p];
            _assertZNorm(j, 78, false);
            _assertZNorm(j, 79, true);
            _assertZNorm(j, 262065, true);
            _assertZNorm(j, 262066, false);
        }
    }

    function _assertZNorm(uint256 j, uint256 v, bool expect) internal pure {
        bytes memory zb = _zBlobOne(j, v);
        (, bool a) = unpackZPacked(zb);
        (, bool b) = unpackZStrict(zb);
        assertEq(a, expect, "shipped z decoder strict-norm boundary");
        assertEq(b, expect, "reference z decoder strict-norm boundary");
    }

    /// 2304-byte z blob: field j = v, every other field = gamma1 (z = 0, in range).
    function _zBlobOne(uint256 j, uint256 v) internal pure returns (bytes memory zB) {
        zB = new bytes(2304);
        for (uint256 c = 0; c < 1024; ++c) {
            uint256 val = (c == j ? v : GAMMA1) & 0x3ffff;
            uint256 bit = 18 * c;
            for (uint256 k = 0; k < 18; ++k) {
                if ((val >> k) & 1 == 1) {
                    uint256 b = (bit + k) >> 3;
                    zB[b] = bytes1(uint8(zB[b]) | uint8(1 << ((bit + k) & 7)));
                }
            }
        }
    }

    // ============================== UseHint + w1Encode boundary sweep ==========

    /// UseHint (FIPS 204 Alg. 40) + w1Encode (Alg. 28) at the values the spec and
    /// literature single out, for both hint bits, across BOTH kernels and against
    /// an independent per-coefficient reference. Inputs are canonical (< q): the
    /// inverse NTT emits canonical coefficients, so r >= q cannot reach the
    /// kernel and is out of its domain.
    function test_usehint_boundary_values_both_kernels() public pure {
        uint256[7] memory boundaries =
            [uint256(0), 1, GAMMA2, ALPHA, GAMMA1, 8388608, Q - 1]; // 2^23 = 8388608
        uint256[] memory vals = new uint256[](7);
        for (uint256 i = 0; i < 7; ++i) {
            vals[i] = boundaries[i];
        }
        uint256[][] memory r = _mkR(vals);
        uint256[][] memory packed = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            packed[i] = packCoeffs(r[i]);
        }
        for (uint256 hb = 0; hb < 2; ++hb) {
            uint256 m = hb == 1 ? type(uint256).max : 0;
            uint256[4] memory masks = [m, m, m, m];
            bytes memory w1swar = useHintSwar(masks, packed);
            bytes memory w1ref = useHintFast2(masks, r);
            assertEq(keccak256(w1swar), keccak256(w1ref), "useHintSwar vs useHintFast2");
            for (uint256 i = 0; i < 4; ++i) {
                for (uint256 j = 0; j < 256; ++j) {
                    assertEq(_unpack6(w1swar, i, j), _refUseHint(r[i][j], hb), "useHintSwar vs FIPS 204");
                }
            }
        }
    }

    function _mkR(uint256[] memory rowVals) internal pure returns (uint256[][] memory r) {
        r = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            uint256[] memory row = new uint256[](256);
            for (uint256 j = 0; j < 256; ++j) {
                row[j] = rowVals[(i * 256 + j) % rowVals.length];
            }
            r[i] = row;
        }
    }

    function _unpack6(bytes memory w1, uint256 row, uint256 j) internal pure returns (uint256) {
        uint256 bit = 6 * j;
        uint256 base = row * 192 + (bit >> 3);
        uint256 acc = uint8(w1[base]);
        if (base + 1 < w1.length) acc |= uint256(uint8(w1[base + 1])) << 8;
        return (acc >> (bit & 7)) & 63;
    }

    /// division-based FIPS 204 Alg. 36 + 40 reference (tests only).
    function _refUseHint(uint256 rv, uint256 h) internal pure returns (uint256) {
        uint256 rp = rv % Q;
        int256 x = int256(rp % ALPHA);
        if (x > int256(GAMMA2)) x -= int256(ALPHA);
        uint256 r1;
        int256 r0;
        if (int256(rp) - x == int256(Q) - 1) {
            r1 = 0;
            r0 = x - 1;
        } else {
            r1 = uint256((int256(rp) - x) / int256(ALPHA));
            r0 = x;
        }
        if (h == 1) {
            if (r0 > 0) return (r1 + 1) % MHI;
            return (r1 + MHI - 1) % MHI;
        }
        return r1;
    }

    // ================================ signature length check (FIPS 204 §3.6.2) =

    /// A signature of any length other than 2420 is refused (both subjects,
    /// fail-closed via a false return, no revert).
    function test_signature_length_is_checked_exactly() public {
        bytes memory short_ = new bytes(2419);
        for (uint256 i = 0; i < 2419; ++i) {
            short_[i] = sig[i];
        }
        bytes memory long_ = bytes.concat(sig, hex"00");

        (bool okS, bool rS) = _shipVerify(msg_, short_);
        assertTrue(okS && !rS, "shipped: 2419-byte sig refused");
        (bool okL, bool rL) = _shipVerify(msg_, long_);
        assertTrue(okL && !rL, "shipped: 2421-byte sig refused");
        (okS, rS) = _refVerify(msg_, short_);
        assertTrue(okS && !rS, "reference: 2419-byte sig refused");
        (okL, rL) = _refVerify(msg_, long_);
        assertTrue(okL && !rL, "reference: 2421-byte sig refused");

        // the exact length still verifies
        (, bool rG) = _shipVerify(msg_, sig);
        assertTrue(rG, "shipped: 2420 bytes verifies");
        (, rG) = _refVerify(msg_, sig);
        assertTrue(rG, "reference: 2420 bytes verifies");
    }

    // ============================ message binding / domain separation ==========

    /// mu = SHAKE256(tr || 0x00 || 0x00 || M, 64) binds the EXACT message under a
    /// fixed empty-context domain prefix. No other message verifies, and a
    /// message that textually equals the internal M' body (0x00 || 0x00 || M) is
    /// a DIFFERENT message because the verifier prepends its own domain bytes.
    function test_message_binding_and_domain_separation() public {
        (, bool base0) = _shipVerify(msg_, sig);
        (, bool base1) = _refVerify(msg_, sig);
        assertTrue(base0 && base1, "baseline verifies on both subjects");

        bytes[5] memory variants;
        variants[0] = _flip(msg_, 0); // first byte flipped
        variants[1] = _flip(msg_, msg_.length - 1); // last byte flipped
        variants[2] = _slice(msg_, 0, msg_.length - 1); // truncated
        variants[3] = bytes.concat(msg_, hex"00"); // extended
        variants[4] = bytes.concat(hex"0000", msg_); // looks like the internal M' body

        for (uint256 i = 0; i < 5; ++i) {
            (bool okS, bool rS) = _shipVerify(variants[i], sig);
            assertTrue(okS && !rS, "shipped: wrong message must not verify");
            (bool okR, bool rR) = _refVerify(variants[i], sig);
            assertTrue(okR && !rR, "reference: wrong message must not verify");
        }
    }

    function _flip(bytes memory b, uint256 i) internal pure returns (bytes memory o) {
        o = bytes.concat(b);
        o[i] = bytes1(uint8(o[i]) ^ 0x01);
    }

    function _slice(bytes memory b, uint256 start, uint256 len) internal pure returns (bytes memory o) {
        o = new bytes(len);
        for (uint256 i = 0; i < len; ++i) {
            o[i] = b[start + i];
        }
    }
}
