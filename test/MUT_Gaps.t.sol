// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/MUT_Gaps.t.sol
//
// Mutation-gap regression tests. Each test pins a specific injected-defect class
// that a coverage-only suite failed to detect; the mutation catalogue lives in
// formal/mutation/.
//
// THE NAMING CONVENTION IS A CHECK, NOT A CLAIM. Two prefixes, and both are
// CHECKED by `formal/hypotheses.py::mut_attribution_problems()` against the
// killer lists in `formal/mutation/mutation_results_final.json`:
//
//   test_MUT_M<nn>_*        asserts "this test kills mutant M<nn>". The check
//                           requires M<nn> to be a NON-EQUIVALENT catalogue
//                           mutant AND this test's name to appear in M<nn>'s
//                           killer list in the artefact. Rename the test, or
//                           point it at the wrong mutant, and the check goes red.
//   test_equivalent_M<nn>_* records an EQUIVALENCE ARGUMENT: M<nn> is a pinned
//                           equivalent mutant, so nothing can kill it by
//                           construction, and the test demonstrates the
//                           behaviour the mutant preserves. The check requires
//                           M<nn> to be in `EXPECTED_EQUIVALENT` and to have
//                           SURVIVED.
//
// Anything else is an ordinary test with no attribution claim in its name.
//
// NO CITATIONS TO MUTANTS THAT DO NOT EXIST. This file is inside
// `doc_id_problems()`'s scan (`DOC_FILES` in formal/hypotheses.py), so a
// citation to a mutant nobody wrote FAILS the hypotheses check. Seven names
// that read exactly like catalogue ids but that `formal/mutation/mutants.py`
// has never defined are listed beside `DOC_FILES` there and deliberately NOT
// here: this file is scanned whole, so naming a non-existent id in it -- even
// in order to say it does not exist -- would be a permanent self-inflicted
// failure.
//
// ATTRIBUTION IS CHECKED, NOT ASSERTED. `doc_id_problems()` only ever asks
// whether the cited ids EXIST; the killer-list rule above is what makes a name
// mean something, and it is why two attributions here read the way they do:
//   * NO test is named for M39. Measured with --no-fail-fast, M39's killer set
//     in the whole corpus is exactly ONE test,
//     `test_MUT_M44_hint_weight_omega_bound` below; the neighbouring
//     `test_MUT_M45_shipped_cut_monotonicity_vs_vendor_oracle`, which drives
//     the same decoders, kills M45 and is named for M45.
//   * the M26 and M28 tests name PINNED EQUIVALENT mutants, which nothing can
//     kill by construction; they are equivalence arguments and are labelled as
//     such with the `test_equivalent_` prefix rather than a `test_MUT_` one --
//     no kill is claimed, exactly as `test_pkSizeGate_subsumes_existence`
//     below avoids a `test_MUT_` name because no catalogue mutant corresponds
//     to it at all.
// The ground truth has to be able to support those claims: `run_mutation.py`
// records COMPLETE, untruncated killer lists from a run with fail-fast
// OFF, and the artefact carries a `_meta` block the check verifies
// (mode FULL, fail-fast off, and the SHA-256 of this file and of mutants.py)
// so a stale artefact is refused rather than quoted.
//
// WHAT THE CHECK ESTABLISHES IS CO-OCCURRENCE, NOT CAUSATION, so the convention
// above earns less than it may appear to. The rule is "this test's name
// appears in that mutant's killer list", and most mutants here are killed by
// dozens of tests, so for those almost any name in the corpus would satisfy
// it. (The exact census moves with every campaign and is therefore quoted in
// formal/mutation/RESULTS.md, which is re-derived, and not here, which is
// not.) Where the killer set has exactly ONE member, co-occurrence IS
// causation: remove that test and the mutant survives. Those are pinned by
// value in `formal/hypotheses.py::SOLE_KILLER_PINS` and checked in both
// directions. The case that makes it matter: M44 and M39 are each killed by
// exactly one test in the whole corpus and it is the SAME test,
// test_MUT_M44_hint_weight_omega_bound below -- so weakening that one test
// silently un-kills two catalogued mutants. M20/M21 share a sole killer
// likewise, and M25 has one of its own.
//
// The subjects are the components that survive into the audited build: the two
// assembled verifiers (MLDSA44Verifier and the reference ZZZ_E2ERef), the shared
// HintBitUnpack decoder (unpackHFast in src/Decode.sol and test/ZZZ_decode.t.sol),
// its vendor reference (test/vendor/ZKNOX_dilithium_core.sol), the strict z
// decoders (unpackZPacked / unpackZStrict) and the fused UseHint+w1Encode kernels
// (useHintSwar / useHintFast2).
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {IMLDSAVerifier} from "../src/IMLDSAVerifier.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {ZZZ_E2ERef, unpackZStrict} from "./ZZZ_E2ERef.sol";
import {unpackH} from "./vendor/ZKNOX_dilithium_core.sol";
import {useHintFast2} from "./ZZZ_decode2.t.sol";
import {packCoeffs} from "./ZZZ_NttVariants.sol";
import {unpackHFast as unpackHFastSrc, unpackZPacked, useHintSwar} from "../src/Decode.sol";

contract MUTGapsTest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant SEED = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";

    uint256 constant Q = 8380417;
    uint256 constant GAMMA1 = 131072;
    uint256 constant GAMMA2 = 95232;
    uint256 constant ALPHA = 190464;
    uint256 constant MHI = 44;
    uint256 constant OMEGA = 80;

    address f1600;
    MLDSA44Verifier shipped;
    ZZZ_E2ERef refv;

    bytes sig1;
    bytes msg1;
    bytes pkBlob1;
    address shipPk1;
    address refPk1;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        f1600 = deployF1600_170();
        shipped = new MLDSA44Verifier(f1600);
        refv = new ZZZ_E2ERef();
        (sig1, pkBlob1, msg1) = _vec(SEED, MSG1_HEX);
        shipPk1 = _deployData(bytes.concat(hex"00", pkBlob1));
        refPk1 = _deployData(pkBlob1);
        assertTrue(shipped.verify(shipPk1, msg1, sig1), "shipped base vector must verify");
        assertTrue(refv.verify(refPk1, msg1, sig1), "reference base vector must verify");
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

    function _copy(bytes memory b) internal pure returns (bytes memory o) {
        o = new bytes(b.length);
        for (uint256 i = 0; i < b.length; ++i) {
            o[i] = b[i];
        }
    }

    // =====================================================================
    // z-norm strict window. The catalogue attacks this check from seven
    // directions and this test walks both edges of both decoders, so it is the
    // discrimination control for all of them:
    //   SHIPPED unpackZPacked (src/Decode.sol)   M40  low edge relaxed by one
    //                                            M40b high edge relaxed by one
    //                                            M41  check REMOVED at all 4 sites
    //                                            M42  high edge relaxed at ONE
    //                                                 site, lane 0 only
    //   REFERENCE unpackZStrict (ZZZ_E2ERef.sol) M11  strict window relaxed to
    //                                                 the loose one
    //                                            M12  widened by one at ONE of
    //                                                 the 4 check sites
    //                                            M13  check REMOVED entirely
    // Both strict decoders share the window v in [79, 262065]; a
    // signature-level accept/reject test CANNOT see any of these (tampering z
    // also breaks the Fiat-Shamir hash), so the decoders are pinned directly,
    // at every in-block position.
    // =====================================================================

    function test_MUT_zNormWindow_every_position_both_decoders() public pure {
        uint256[8] memory probes = [uint256(0), 1, 2, 3, 31, 32, 33, 1023];
        for (uint256 p = 0; p < 8; ++p) {
            uint256 j = probes[p];
            _assertWindow(j, 78, false); // |z| = gamma1 - beta: strictly out
            _assertWindow(j, 79, true); // one step inside
            _assertWindow(j, 262065, true); // upper edge inside
            _assertWindow(j, 262066, false); // one step out
        }
    }

    function _assertWindow(uint256 j, uint256 v, bool expect) internal pure {
        bytes memory zb = _zBlobOne(j, v);
        (, bool a) = unpackZPacked(zb);
        (, bool b) = unpackZStrict(zb);
        assertEq(a, expect, "shipped unpackZPacked window");
        assertEq(b, expect, "reference unpackZStrict window");
    }

    /// 2304-byte z blob: field j = v, every other field = gamma1 (z = 0).
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

    // =====================================================================
    // M60/M61/M63: the SHIPPED check is now ONE expression per QUAD -- bit 32 of
    // each 64-bit lane of `and(add(o, Z_NLO), sub(Z_NHI, o))` carries one
    // coefficient's verdict -- so "every coefficient is gated" no longer follows
    // from a site count. It follows from the two window constants being the same
    // value in all FOUR lanes, and a defect that blanks or relaxes ONE lane
    // leaves 256 of the 1024 coefficients ungated while every other test in the
    // suite still passes. This test is the discrimination control for that: it
    // walks BOTH boundaries, in BOTH directions, at EVERY lane (c mod 4) of the
    // FIRST and LAST quad of EVERY ONE of the four polynomials -- 32 coefficient
    // positions x 4 field values -- and requires the shipped decoder to agree
    // with the reference one at each. Mutants M60 (lane 3 of Z_NLO blanked),
    // M61 (lane 1 of Z_NHI relaxed) and M63 (lane 2 of Z_M18 narrowed) are all
    // killed here.
    // =====================================================================

    function test_MUT_zPackedGate_every_lane_every_polynomial() public pure {
        for (uint256 poly = 0; poly < 4; ++poly) {
            for (uint256 lane = 0; lane < 4; ++lane) {
                // first quad of this polynomial, and its last quad
                uint256 first = poly * 256 + lane;
                uint256 last = poly * 256 + 252 + lane;
                _assertWindow(first, 78, false);
                _assertWindow(first, 79, true);
                _assertWindow(first, 262065, true);
                _assertWindow(first, 262066, false);
                _assertWindow(last, 78, false);
                _assertWindow(last, 79, true);
                _assertWindow(last, 262065, true);
                _assertWindow(last, 262066, false);
            }
        }
    }

    /// ... and the same at every lane of an INTERIOR quad of each polynomial,
    /// with the z = 0 field (v = gamma1) as the neighbour value: the packed
    /// canonicalisation stores 0 for it, so a mutant that stores q instead
    /// (M62) changes the decoded word of every OTHER coefficient too.
    function test_MUT_zPackedDecode_words_match_reference_at_every_lane() public pure {
        uint256[6] memory probes = [uint256(0), 3, 4, 259, 1020, 1023];
        uint256[5] memory vals = [uint256(0), 79, GAMMA1, 262065, 262143];
        for (uint256 i = 0; i < 6; ++i) {
            for (uint256 k = 0; k < 5; ++k) {
                bytes memory zb = _zBlobOne(probes[i], vals[k]);
                (uint256[][] memory zp, bool okNew) = unpackZPacked(zb);
                (uint256[] memory flat, bool okRef) = unpackZStrict(zb);
                assertEq(okNew, okRef, "verdict diverged");
                for (uint256 c = 0; c < 1024; ++c) {
                    uint256 got = (zp[c >> 8][(c & 255) >> 2] >> (64 * (c & 3)))
                        & 0xffffffffffffffff;
                    assertEq(got, flat[c], "packed lane != reference coefficient");
                    assertTrue(got < Q, "stored lane not canonical");
                }
            }
        }
    }

    /// Fuzzed: four arbitrary 18-bit fields in ONE quad (so all four lanes of one
    /// packed word are exercised together, which is exactly the property a SWAR
    /// check can get wrong) against the per-coefficient reference decoder.
    function testFuzz_MUT_zPackedQuad_matches_reference(uint256 raw) public pure {
        uint256 base = (raw % 256) & ~uint256(3); // quad-aligned coefficient index
        bytes memory zb = new bytes(2304);
        uint256[4] memory v;
        for (uint256 l = 0; l < 4; ++l) {
            v[l] = (raw >> (32 + 18 * l)) & 0x3ffff;
        }
        for (uint256 c = 0; c < 1024; ++c) {
            uint256 val = GAMMA1;
            if (c >= base && c < base + 4) val = v[c - base];
            for (uint256 k = 0; k < 18; ++k) {
                if ((val >> k) & 1 == 1) {
                    uint256 bit = 18 * c + k;
                    zb[bit >> 3] = bytes1(uint8(zb[bit >> 3]) | uint8(1 << (bit & 7)));
                }
            }
        }
        (uint256[][] memory zp, bool okNew) = unpackZPacked(zb);
        (uint256[] memory flat, bool okRef) = unpackZStrict(zb);
        assertEq(okNew, okRef, "verdict diverged on a fuzzed quad");
        for (uint256 l = 0; l < 4; ++l) {
            uint256 c = base + l;
            uint256 got = (zp[c >> 8][(c & 255) >> 2] >> (64 * (c & 3))) & 0xffffffffffffffff;
            assertEq(got, flat[c], "fuzzed lane != reference coefficient");
        }
    }

    // =====================================================================
    // M44 (and M39): FIPS 204 Alg. 21 line 4, weight <= omega, on the SHIPPED
    // decoder (M44 removes the bound from src/Decode.sol::unpackHFast) and on
    // the VENDORED oracle (M39 removes it from
    // test/vendor/ZKNOX_dilithium_core.sol::unpackH). The delicate witness
    // below is accepted iff the bound is absent (every other check is
    // satisfied), so it pins the bound itself rather than a neighbouring rule.
    //
    // It is also, measured with --no-fail-fast, the SOLE killer of M39 in the
    // whole corpus -- the last assertion in this test is the only place the
    // vendored decoder is handed an over-weight encoding whose indices are
    // strictly increasing, which is what it takes to reach that bound. No
    // other test reaches it, which is why no test is named for M39; see the
    // ATTRIBUTION note in the header.
    // =====================================================================

    function test_MUT_M44_hint_weight_omega_bound() public pure {
        // y[0..79] = 0..79 (strictly increasing); cuts 81,82,82,82: with the
        // bound present, row-0 cut 81 > 80 = omega is rejected; without it, the
        // total weight 82 > omega slips through.
        bytes memory over = new bytes(84);
        for (uint256 j = 0; j < 80; ++j) {
            over[j] = bytes1(uint8(j));
        }
        over[80] = bytes1(uint8(81));
        over[81] = bytes1(uint8(82));
        over[82] = bytes1(uint8(82));
        over[83] = bytes1(uint8(82));
        (bool ok,, uint256 w) = unpackHFastSrc(over);
        assertFalse(ok, "weight 82 > omega must be rejected");
        assertEq(w, 0, "rejected encodings report weight 0");

        // one notch lower (cuts 80,80,80,80) is legal, weight exactly omega
        bytes memory edge = new bytes(84);
        for (uint256 j = 0; j < 80; ++j) {
            edge[j] = bytes1(uint8(j));
        }
        edge[80] = bytes1(uint8(80));
        edge[81] = bytes1(uint8(80));
        edge[82] = bytes1(uint8(80));
        edge[83] = bytes1(uint8(80));
        (bool okE,, uint256 wE) = unpackHFastSrc(edge);
        assertTrue(okE, "weight exactly omega must be accepted");
        assertEq(wE, OMEGA, "weight == omega");

        // the vendor reference decoder must agree on the over-weight witness
        (bool okRef,) = unpackH(over);
        assertFalse(okRef, "vendor reference must reject weight 82");
    }

    // =====================================================================
    // M45: the SHIPPED decoder's non-decreasing cut-position check
    // (`bad |= c0>c1 | c1>c2 | c2>c3`, removed by M45). The vendor reference
    // decoder is the oracle the differential tests compare against, and this
    // test drives BOTH decoders over the same battery of witnesses and requires
    // them to agree -- so a shipped decoder that stops rejecting a decreasing
    // cut counter (case 4) diverges from the oracle here. Mutating the ORACLE
    // and seeing nothing break would mean it is not actually exercised, so it
    // is pinned directly too.
    //
    // ATTRIBUTION: this test is named for M45 and not M39 because its
    // over-omega witnesses all carry index bytes that break the
    // strict-increase rule first, so the vendored omega bound is never
    // reached. Measured with --no-fail-fast, this body kills M45 (and nothing
    // else in the file does, apart from SEC2_Fips204Gates' empty-row test).
    // =====================================================================

    function test_MUT_M45_shipped_cut_monotonicity_vs_vendor_oracle() public pure {
        // a cut byte above omega must be rejected by the vendor decoder
        for (uint256 badCut = 81; badCut <= 84; ++badCut) {
            bytes memory y = new bytes(84);
            y[83] = bytes1(uint8(badCut));
            for (uint256 j = 0; j < 80; ++j) {
                y[j] = bytes1(uint8(j));
            }
            (bool ok,) = unpackH(y);
            assertFalse(ok, "vendor reference: cut byte above omega");
        }

        // vendor and fast decoders agree on a battery of witnesses
        bytes[6] memory cases;
        {
            bytes memory good = new bytes(84);
            good[80] = bytes1(uint8(2));
            good[81] = bytes1(uint8(3));
            good[82] = bytes1(uint8(3));
            good[83] = bytes1(uint8(4));
            good[0] = bytes1(uint8(1));
            good[1] = bytes1(uint8(7));
            good[2] = bytes1(uint8(9));
            good[3] = bytes1(uint8(200));
            cases[0] = good;

            bytes memory rep = _copy(good);
            rep[1] = bytes1(uint8(1)); // repeated index
            cases[1] = rep;

            bytes memory dec = _copy(good);
            dec[1] = bytes1(uint8(0)); // decreasing
            cases[2] = dec;

            bytes memory pad = _copy(good);
            pad[40] = bytes1(uint8(1)); // nonzero padding
            cases[3] = pad;

            bytes memory cut = _copy(good);
            cut[81] = bytes1(uint8(1)); // decreasing cut positions
            cases[4] = cut;

            bytes memory ov = _copy(good);
            ov[83] = bytes1(uint8(200)); // cut above omega
            cases[5] = ov;
        }
        for (uint256 i = 0; i < cases.length; ++i) {
            (bool okRef,) = unpackH(cases[i]);
            (bool okFast,,) = unpackHFastSrc(cases[i]);
            assertEq(okRef, okFast, "vendor and fast decoders must agree");
            assertEq(okRef, i == 0, "expected verdict");
        }
    }

    // =====================================================================
    // M26 is a PINNED EQUIVALENT mutant, so NOTHING can kill it and the test
    // below claims no kill -- its `test_equivalent_` prefix says as much. What
    // it records is the equivalence argument, by demonstration: FIPS 204
    // Decompose's edge case r1 == 44 is reachable only at r = q-1, a
    // uniform-random differential test essentially never hits it, and the
    // shipped kernel, the reference kernel and the per-coefficient FIPS
    // reference agree at that point and around it. That agreement is what
    // makes M26's rewrite semantics-preserving rather than merely unkilled.
    // =====================================================================

    function test_equivalent_M26_useHint_edge_case_q_minus_1() public pure {
        uint256[] memory vals = new uint256[](8);
        vals[0] = Q - 1; // q0 == 44 exactly
        vals[1] = Q - 2;
        vals[2] = 44 * ALPHA; // == q-1 as well
        vals[3] = 43 * ALPHA;
        vals[4] = 43 * ALPHA + GAMMA2;
        vals[5] = 43 * ALPHA + GAMMA2 + 1;
        vals[6] = 0;
        vals[7] = 1;
        _assertUseHintAgrees(vals);
    }

    // =====================================================================
    // M28 is a PINNED EQUIVALENT mutant too, so this is likewise an
    // equivalence argument, not a kill. The SWAR division constant
    // in useHintSwar (MDIV = 2886403, (r * MDIV) >> 39 == r / 190464 for every
    // r < q) is exercised at every boundary where a perturbed multiplier could
    // disagree -- the k*ALPHA-1 / k*ALPHA pairs, which are the only 60 of
    // 8,380,417 inputs on which the perturbation is wrong, and which a uniform
    // random test misses. Agreement there is the argument.
    // =====================================================================

    function test_equivalent_M28_swar_division_boundaries() public pure {
        uint256[] memory vals = new uint256[](88);
        for (uint256 k = 1; k <= 44; ++k) {
            vals[2 * (k - 1)] = k * ALPHA - 1;
            vals[2 * (k - 1) + 1] = k * ALPHA > Q - 1 ? Q - 1 : k * ALPHA;
        }
        _assertUseHintAgrees(vals);
    }

    /// build 4 rows cycling through `vals`, then assert useHintSwar (shipped),
    /// useHintFast2 (reference) and the per-coefficient FIPS reference all agree,
    /// for both hint bits.
    function _assertUseHintAgrees(uint256[] memory vals) internal pure {
        uint256[][] memory r = _mkR(vals);
        uint256[][] memory packed = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            packed[i] = packCoeffs(r[i]);
        }
        for (uint256 hb = 0; hb < 2; ++hb) {
            uint256 m = hb == 1 ? type(uint256).max : 0;
            uint256[4] memory masks = [m, m, m, m];
            bytes memory got = useHintSwar(masks, packed);
            bytes memory want = useHintFast2(masks, r);
            assertEq(keccak256(got), keccak256(want), "useHintSwar vs useHintFast2");
            for (uint256 i = 0; i < 4; ++i) {
                for (uint256 j = 0; j < 256; ++j) {
                    assertEq(_unpack6(got, i, j), _refUseHint(r[i][j], hb), "useHintSwar vs FIPS 204");
                }
            }
        }
    }

    // =====================================================================
    // M54: the final c~ comparison. A magic value that short-circuits the
    // Fiat-Shamir check is the canonical shape of a verifier backdoor, and M54
    // injects exactly that shape (an attacker-supplied all-zero c-tilde
    // accepted by the shipped verifier); pin that no such value is accepted by
    // either subject.
    // =====================================================================

    function test_MUT_M54_no_magic_ctilde_accepted() public view {
        bytes32[6] memory magic = [
            bytes32(0),
            bytes32(type(uint256).max),
            bytes32(uint256(1)),
            bytes32(uint256(0xdeadbeef)),
            keccak256(""),
            bytes32(uint256(1) << 255)
        ];
        for (uint256 k = 0; k < 6; ++k) {
            bytes memory s = _copy(sig1);
            for (uint256 i = 0; i < 32; ++i) {
                s[i] = magic[k][i];
            }
            (bool okS, bytes memory rs) = address(shipped).staticcall(
                abi.encodeCall(IMLDSAVerifier.verify, (shipPk1, msg1, s))
            );
            assertTrue(okS && !abi.decode(rs, (bool)), "magic c~ must never be accepted (shipped)");
            (bool okR, bytes memory rr) = address(refv).staticcall(
                abi.encodeCall(ZZZ_E2ERef.verify, (refPk1, msg1, s))
            );
            assertTrue(okR && !abi.decode(rr, (bool)), "magic c~ must never be accepted (reference)");
        }
    }

    // =====================================================================
    // M52 / M72: the pk-cache size check. The size pin is EXACT and is the sole
    // load-bearing pk check: relaxing it to `>=` (M52) would let two pkids share
    // one effective key, and shrinking the WIDTH CONSTANT it compares against
    // (M72) pins the wrong size without moving the shape of the check. Both are
    // killed by SEC_pkcache.t.sol's size-check battery; this test is the
    // end-to-end companion that walks +1 and -1 on BOTH subjects.
    // =====================================================================

    function test_MUT_M52_pk_size_pin_is_exact() public {
        // shipped requires EXACTLY 20545 (0x00 || 20544 payload)
        assertTrue(shipped.verify(shipPk1, msg1, sig1), "exact size verifies");
        address bigShip = _deployData(bytes.concat(hex"00", pkBlob1, hex"ff")); // 20546
        assertFalse(shipped.verify(bigShip, msg1, sig1), "shipped: oversized cache rejected");
        // one byte short of the payload
        {
            bytes memory shortPayload = new bytes(pkBlob1.length - 1);
            for (uint256 i = 0; i < shortPayload.length; ++i) {
                shortPayload[i] = pkBlob1[i];
            }
            address s = _deployData(bytes.concat(hex"00", shortPayload));
            assertFalse(shipped.verify(s, msg1, sig1), "shipped: undersized cache rejected");
        }

        // reference requires EXACTLY 20544
        assertTrue(refv.verify(refPk1, msg1, sig1), "reference exact size verifies");
        assertFalse(refv.verify(_deployData(bytes.concat(pkBlob1, hex"ff")), msg1, sig1), "reference: +1 rejected");
        {
            bytes memory shortRef = new bytes(pkBlob1.length - 1);
            for (uint256 i = 0; i < shortRef.length; ++i) {
                shortRef[i] = pkBlob1[i];
            }
            assertFalse(refv.verify(_deployData(shortRef), msg1, sig1), "reference: -1 rejected");
        }
    }

    /// NO CATALOGUE MUTANT CORRESPONDS TO THIS TEST, and its name deliberately
    /// claims none. It records a DESIGN argument -- that the exact-size pin
    /// already rejects a codeless or empty account, so a separate liveness check
    /// would be dead code -- by demonstrating it. The pin whose exactness the
    /// argument depends on is mutation-covered by M52 and M72 above; there is
    /// nothing left for a mutant of "the check that is not there" to remove.
    function test_pkSizeGate_subsumes_existence() public {
        // codeless account and (etched) empty-code account both fail the size check
        address nobody = address(uint160(uint256(keccak256("no code here"))));
        assertEq(nobody.code.length, 0, "precondition: codeless");
        assertFalse(shipped.verify(nobody, msg1, sig1), "shipped: codeless rejected by size check");
        assertFalse(refv.verify(nobody, msg1, sig1), "reference: codeless rejected by size check");

        address funded = address(uint160(uint256(keccak256("funded eoa"))));
        vm.deal(funded, 1 ether);
        assertEq(funded.code.length, 0, "precondition: codeless with balance");
        assertFalse(shipped.verify(funded, msg1, sig1), "shipped: funded EOA rejected");
        assertFalse(refv.verify(funded, msg1, sig1), "reference: funded EOA rejected");
    }

    // ------------------------------------------------------------ UseHint utils

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
}
