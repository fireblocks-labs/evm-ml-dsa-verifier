// SPDX-License-Identifier: MIT
// ===========================================================================
// FV_Kernels.t.sol — concrete cross-checks for the symbolic proofs in
// test/FV_Kernels.sol (see that file's header for the proof obligations and
// for the two tool-level assumptions [PIN]/[WITNESS] that these tests
// independently discharge).
//
// Where the input domain is small enough, the test is EXHAUSTIVE and therefore
// a complete proof at EVM-bytecode level by itself:
//   * (a) z decode / norm test  : all 2^18 packed field values.
//   * (f) 6-bit w1 packing      : all 44^2 pairs by default, all 44^3 groups
//                                under FV_EXHAUSTIVE=1.
// For (b) UseHint the domain is 2^23 x 2, which does not fit in an EVM test
// (~1.7e9 gas); the exhaustive sweep over all 16 760 834 (r,h) pairs is
// machine-checked in formal/z3/ instead, and this file covers every
// equivalence class of the kernel's control flow (b == 0 / 1 <= b <= gamma2 /
// b > gamma2, for all 45 quotients) plus a pseudo-random sample.
// ===========================================================================
pragma solidity ^0.8.25;

import "forge-std/Test.sol";
import {
    kStrictNormFail,
    kStrictCenter,
    kLooseNormFail,
    kLooseCenter,
    kUnpack4,
    kUseHint,
    kPack6,
    kLazyBarrett,
    kBarrettStep1,
    kQhat,
    kQhat2,
    kSwarBarrett4,
    kSwarStep1,
    refZCenterCanonical,
    refZCenterQForZero,
    refNormBadStrict,
    refNormBadLoose,
    refUseHintDiv,
    refW1Pack,
    Q as FVQ,
    MU33 as FVMU33,
    GAMMA2 as FVG2,
    ALPHA as FVA,
    MHI as FVM,
    LANE as FVLANE,
    INV_MAX as FVINVMAX,
    FWD_MAX as FVFWDMAX
} from "./FV_Kernels.sol";
// FV2_Barrett.sol's OWN kernel copies, and the two SHIPPED reductions they
// claim to be character-identical to.  See test_FV2_barrett_kernels_are_the
// _shipped_reductions below for why this import exists at all.
import {
    kLazyBarrett as fv2LazyBarrett,
    kBarrettStep1 as fv2BarrettStep1,
    kSwarBarrett4 as fv2SwarBarrett4,
    kSwarStep1 as fv2SwarStep1,
    kSwarStep2 as fv2SwarStep2
} from "./FV2_Barrett.sol";
import {lazyBarrett as shippedFwdLazyBarrett} from "../src/Ntt.sol";
import {invLazyBarrett as shippedInvLazyBarrett} from "../src/InvNtt.sol";

contract FVKernelsTest is Test {
    // =======================================================================
    // (a) EXHAUSTIVE over all 2^18 packed 18-bit z fields
    // =======================================================================
    function test_FV_a_zDecodeExhaustive2p18() public pure {
        for (uint256 v = 0; v < 262144; ++v) {
            // (a-i) strict/canonical centered map
            uint256 outS = kStrictCenter(v);
            require(outS == refZCenterCanonical(v), "strict center != FIPS ref");
            require(outS < FVQ, "strict center not canonical");

            // (a-ii) strict branchless norm test == FIPS |z| >= gamma1-beta
            require((kStrictNormFail(v) != 0) == refNormBadStrict(v), "strict norm != FIPS");

            // (a-i') loose kernel center map (z == 0 stored as q)
            uint256 outL = kLooseCenter(v);
            require(outL == refZCenterQForZero(v), "loose center != ref");
            require(outL >= 1 && outL <= FVQ, "loose center out of range");

            // (a-ii') loose norm test == |z| > gamma1-beta
            require((kLooseNormFail(v) != 0) == refNormBadLoose(v), "loose norm != ref");
        }
    }

    /// (a-iii) 18-bit field extraction: fuzzed cross-check of the layout proof
    function testFuzz_FV_a_bitExtract(bytes32 w) public pure {
        (uint256 v0, uint256 v1, uint256 v2, uint256 v3) = kUnpack4(w);
        uint256 W;
        for (uint256 i = 0; i < 9; ++i) {
            W |= uint256(uint8(w[i])) << (8 * i);
        }
        assertEq(v0, W & 0x3ffff);
        assertEq(v1, (W >> 18) & 0x3ffff);
        assertEq(v2, (W >> 36) & 0x3ffff);
        assertEq(v3, (W >> 54) & 0x3ffff);
    }

    // =======================================================================
    // (b) UseHint: every control-flow equivalence class, plus a random sample
    // =======================================================================
    function test_FV_b_useHintAllClasses() public pure {
        // the kernel branches only on  (b == 0) and (b > gamma2); the FIPS
        // reference additionally on (q0 == 44). Sweep all 45 quotients x the
        // class representatives and their neighbours x both hint bits.
        uint256[9] memory bs = [uint256(0), 1, 2, FVG2 - 1, FVG2, FVG2 + 1, FVA - 2, FVA - 1, FVA];
        for (uint256 q0 = 0; q0 <= 44; ++q0) {
            for (uint256 i = 0; i < 9; ++i) {
                uint256 rv = q0 * FVA + bs[i];
                if (rv >= FVQ) continue;
                for (uint256 h = 0; h < 2; ++h) {
                    uint256 got = kUseHint(rv, h);
                    require(got == refUseHintDiv(rv, h), "useHint != FIPS ref");
                    require(got < FVM, "useHint out of [0,44)");
                }
            }
        }
    }

    function test_FV_b_useHintRandomSample() public pure {
        uint256 s = uint256(keccak256("FV_useHint_seed"));
        for (uint256 i = 0; i < 4000; ++i) {
            s = uint256(keccak256(abi.encode(s)));
            uint256 rv = s % FVQ;
            uint256 h = (s >> 255) & 1;
            require(kUseHint(rv, h) == refUseHintDiv(rv, h), "useHint != FIPS ref (random)");
            require(kUseHint(rv, h) < FVM, "useHint out of [0,44)");
        }
    }

    function testFuzz_FV_b_useHint(uint256 rvIn, bool hIn) public pure {
        uint256 rv = rvIn % FVQ;
        uint256 h = hIn ? 1 : 0;
        assertEq(kUseHint(rv, h), refUseHintDiv(rv, h));
        assertLt(kUseHint(rv, h), FVM);
    }

    /// DOMAIN TIGHTNESS: the kernel is correct only for canonical r < q, and it
    /// diverges from FIPS at the very first non-canonical input, r == q with
    /// h == 1 (kernel 1 vs FIPS 43 — found independently by the exhaustive
    /// sweep and by z3, see formal/z3/). The caller's guarantee that w' is
    /// canonical (the canonicalising final pass of nttInvV3) is therefore
    /// load-bearing, not cosmetic.
    /// The unconditional final `mod(.., 44)` keeps the OUTPUT in [0,44) even
    /// out of domain, so the range postcondition alone would not catch this.
    function test_FV_b_useHintDomainIsTight() public pure {
        require(kUseHint(FVQ, 1) == 1, "kernel value at r == q, h == 1");
        require(refUseHintDiv(FVQ, 1) == 43, "FIPS value at r == q, h == 1");
        require(kUseHint(FVQ, 1) != refUseHintDiv(FVQ, 1), "expected divergence at r == q");
        require(kUseHint(FVQ, 1) < FVM, "output stays in range even out of domain");
        // ... and every canonical input agrees (see the exhaustive sweep)
        require(kUseHint(FVQ - 1, 1) == refUseHintDiv(FVQ - 1, 1), "last canonical input");
    }

    // =======================================================================
    // (c) Barrett reductions
    // =======================================================================
    function test_FV_c_barrettBoundaries() public pure {
        uint256[12] memory xs = [
            uint256(0),
            1,
            FVQ - 1,
            FVQ,
            FVQ + 1,
            2 * FVQ,
            2 * FVQ - 1,
            FVFWDMAX,
            FVFWDMAX - 1,
            FVINVMAX,
            FVINVMAX - 1,
            FVINVMAX / 2
        ];
        for (uint256 i = 0; i < 12; ++i) {
            _checkBarrett(xs[i]);
        }
    }

    function test_FV_c_barrettRandomSample() public pure {
        uint256 s = uint256(keccak256("FV_barrett_seed"));
        for (uint256 i = 0; i < 4000; ++i) {
            s = uint256(keccak256(abi.encode(s)));
            _checkBarrett(s % (FVINVMAX + 1));
        }
    }

    function testFuzz_FV_c_barrett(uint256 x) public pure {
        _checkBarrett(x % (FVINVMAX + 1));
    }

    function _checkBarrett(uint256 x) internal pure {
        uint256 qhat = kQhat(x);
        require(qhat < (1 << 31), "qhat exceeds QHATM31 mask");
        require(x * FVMU33 < (1 << 64), "first product leaves its 64-bit lane");
        uint256 x1 = kBarrettStep1(x);
        require(x1 == x - qhat * FVQ, "step 1 witness identity");
        require(x1 <= 7508854654, "step 1 output >= 2^33");
        uint256 qhat2 = kQhat2(x1);
        require(qhat2 <= 895, "step 2 quotient exceeds the 31-bit mask");
        uint256 r = kLazyBarrett(x);
        require(r == x1 - qhat2 * FVQ, "step 2 witness identity");
        require(r % FVQ == x % FVQ, "barrett changes residue");
        require(r < 2 * FVQ, "barrett result >= 2q");
        require(x == r + (qhat + qhat2) * FVQ, "barrett witness identity");
    }

    /// TIGHTNESS of the documented domain: the SMALLEST x for which the
    /// two-step lazy Barrett result is no longer < 2q is exactly
    /// 10285325456994078, proved minimal by a linear-integer optimisation query
    /// (z3 Optimize, obligation c-tight, machine-checked in formal/z3/). It sits
    /// 1.1441x above the inverse-NTT worst product 128*q*(q-1) =
    /// 8989616731324416 and 9.76x above the forward worst product, so the
    /// kernels' documented margin is real but THIN: any future layer-bound
    /// increase past 14% must be re-verified.
    /// Note the cliff is NOT the lane-overflow cliff: the first x whose product
    /// x*MU33 leaves its own 64-bit lane is 17996823486545905, well above this,
    /// so r < 2q is the binding constraint.
    function test_FV_c_barrettDomainTightness() public pure {
        uint256 firstBad = 10285325456994078;
        require(kLazyBarrett(firstBad) == 2 * FVQ, "first bad x should give exactly 2q");
        require(kLazyBarrett(firstBad - 1) < 2 * FVQ, "x-1 should still be < 2q");
        require(firstBad > FVINVMAX, "documented bound must be inside the safe domain");
        require((firstBad * 10000) / FVINVMAX == 11441, "margin over the inverse bound is 1.1441x");
        // the lane-overflow cliff sits ABOVE it, so it is not what binds
        require(17996823486545905 * FVMU33 >= (1 << 64), "lane cliff");
        require(17996823486545904 * FVMU33 < (1 << 64), "lane cliff is minimal");
        require(17996823486545905 > firstBad, "r < 2q is the binding constraint");
        // one more unreduced layer (2x the inverse worst product) would break it
        require(2 * FVINVMAX >= firstBad, "2*INV_MAX already reaches the cliff");
    }

    // =======================================================================
    // test/FV2_Barrett.sol IS ABOUT THE SHIPPED KERNEL
    // =======================================================================
    // `FORMAL_VERIFICATION.md` §5.7 marks the Lean<->bytecode refinement gap for
    // the Barrett family **Closed**, citing `test/FV2_Barrett.sol`.  That file
    // declares 22 `check_*` functions and 0 `test*` functions, so `forge test`
    // COMPILES it and runs nothing, and it is imported by no test.  Left at
    // that, its only tie to the shipped kernel would be a COMMENT asserting
    // character-identity with `src/Ntt.sol::lazyBarrett`, and §5.7's "Closed"
    // would rest on a claim nothing checks.
    //
    // Two mechanisms make the citation real, and this is the cheap half: the
    // identity the comment asserts is a fuzz test over the full documented
    // domain.  The other half is C18's residual digest over
    // `test/FV2_Barrett.sol` (`source_pins` otherwise covers `formal/` only,
    // C16 the NTT pair, C18 the four `src/` files), which makes any edit to
    // that file a FAILED obligation rather than an unnoticed divergence.
    // A mutant on `fv2LazyBarrett` fails this test.
    function testFuzz_FV2_barrett_kernels_are_the_shipped_reductions(uint256 xin) public pure {
        uint256 x = xin % (FVINVMAX + 1);
        // the scalar two-step reduction, against BOTH shipped copies
        assertEq(fv2LazyBarrett(x), shippedFwdLazyBarrett(x), "FV2 kLazyBarrett != src/Ntt.sol lazyBarrett");
        assertEq(fv2LazyBarrett(x), shippedInvLazyBarrett(x), "FV2 kLazyBarrett != src/InvNtt.sol invLazyBarrett");
        // ... and against FV_Kernels.sol's copy, which the rest of this file uses
        assertEq(fv2LazyBarrett(x), kLazyBarrett(x), "FV2 kLazyBarrett != FV_Kernels kLazyBarrett");
        assertEq(fv2BarrettStep1(x), kBarrettStep1(x), "FV2 step 1 != FV_Kernels step 1");
        // the packed form, one lane at a time: the SWAR block must agree with
        // the scalar reduction on every lane it is applied to
        assertEq(fv2SwarBarrett4(x), fv2SwarStep2(fv2SwarStep1(x)), "FV2 SWAR is not its two steps");
        assertEq(fv2SwarBarrett4(x), kSwarBarrett4(x), "FV2 SWAR != FV_Kernels SWAR");
        assertEq(fv2SwarStep1(x), kSwarStep1(x), "FV2 SWAR step 1 != FV_Kernels SWAR step 1");
        assertEq(fv2SwarBarrett4(x), fv2LazyBarrett(x), "single-lane SWAR != the scalar reduction");
    }

    function test_FV_c_swarLanesNoLeak() public pure {
        uint256 s = uint256(keccak256("FV_swar_seed"));
        for (uint256 i = 0; i < 2000; ++i) {
            s = uint256(keccak256(abi.encode(s)));
            uint256 l0 = (s % (FVINVMAX + 1));
            s = uint256(keccak256(abi.encode(s)));
            uint256 l1 = (s % (FVINVMAX + 1));
            s = uint256(keccak256(abi.encode(s)));
            uint256 l2 = (s % (FVINVMAX + 1));
            s = uint256(keccak256(abi.encode(s)));
            uint256 l3 = (s % (FVINVMAX + 1));

            // full 4-lane SWAR word, reduced in place: no spread, no repack
            uint256 w = l0 | (l1 << 64) | (l2 << 128) | (l3 << 192);
            uint256 r4 = kSwarBarrett4(w);
            require((r4 & FVLANE) == kLazyBarrett(l0), "swar lane0");
            require(((r4 >> 64) & FVLANE) == kLazyBarrett(l1), "swar lane1");
            require(((r4 >> 128) & FVLANE) == kLazyBarrett(l2), "swar lane2");
            require((r4 >> 192) == kLazyBarrett(l3), "swar lane3");

            // the intermediate word is lane-wise the scalar step 1 as well, so
            // neither of the two masks leaks
            uint256 y = kSwarStep1(w);
            require((y & FVLANE) == kBarrettStep1(l0), "swar step1 lane0");
            require(((y >> 64) & FVLANE) == kBarrettStep1(l1), "swar step1 lane1");
            require(((y >> 128) & FVLANE) == kBarrettStep1(l2), "swar step1 lane2");
            require((y >> 192) == kBarrettStep1(l3), "swar step1 lane3");
        }
    }

    /// STEP 2 IS LOAD-BEARING: the coarse step alone leaves values far above 2q
    /// over the documented domain (its output only has to be < 2^33).
    function test_FV_c_step2IsLoadBearing() public pure {
        require(kBarrettStep1(FVINVMAX) == 7508853632, "step 1 output at INV_MAX");
        require(kBarrettStep1(FVINVMAX) >= 2 * FVQ, "step 1 alone does not reach the lazy bound");
        require(kLazyBarrett(FVINVMAX) < 2 * FVQ, "both steps do");
    }

    function testFuzz_FV_c_swarLanes(uint64 a, uint64 b, uint64 c, uint64 d) public pure {
        uint256 l0 = uint256(a) % (FVINVMAX + 1);
        uint256 l1 = uint256(b) % (FVINVMAX + 1);
        uint256 l2 = uint256(c) % (FVINVMAX + 1);
        uint256 l3 = uint256(d) % (FVINVMAX + 1);
        uint256 w = l0 | (l1 << 64) | (l2 << 128) | (l3 << 192);
        uint256 r4 = kSwarBarrett4(w);
        assertEq(r4 & FVLANE, kLazyBarrett(l0));
        assertEq((r4 >> 64) & FVLANE, kLazyBarrett(l1));
        assertEq((r4 >> 128) & FVLANE, kLazyBarrett(l2));
        assertEq(r4 >> 192, kLazyBarrett(l3));
    }

    // =======================================================================
    // (f) 6-bit w1 packing
    // =======================================================================
    function test_FV_f_pack6Exhaustive2d() public pure {
        for (uint256 a0 = 0; a0 < 44; ++a0) {
            for (uint256 a1 = 0; a1 < 44; ++a1) {
                _checkPack6(a0, a1, a1, a0);
                _checkPack6(a0, a1, 43 - a0, 43 - a1);
            }
        }
    }

    /// exhaustive over 44^3 = 85184 groups with the 4th coefficient stepping
    /// through all 44 residues (the full 44^4 = 3.75M sweep does not fit
    /// foundry's 2^30 default gas limit; the property is proved symbolically
    /// for ALL values < 44 by check_f1_pack6 and the formal/z3/ queries).
    function test_FV_f_pack6Exhaustive3d() public view {
        if (!vm.envOr("FV_EXHAUSTIVE", false)) return;
        for (uint256 a0 = 0; a0 < 44; ++a0) {
            for (uint256 a1 = 0; a1 < 44; ++a1) {
                for (uint256 a2 = 0; a2 < 44; ++a2) {
                    _checkPack6(a0, a1, a2, (a0 * 13 + a1 * 7 + a2) % 44);
                }
            }
        }
    }

    function testFuzz_FV_f_pack6(uint8 a0, uint8 a1, uint8 a2, uint8 a3) public pure {
        _checkPack6(a0 % 44, a1 % 44, a2 % 44, a3 % 44);
    }

    function _checkPack6(uint256 a0, uint256 a1, uint256 a2, uint256 a3) internal pure {
        (uint256 b0, uint256 b1, uint256 b2) = kPack6(a0, a1, a2, a3);
        (uint256 e0, uint256 e1, uint256 e2) = refW1Pack(a0, a1, a2, a3);
        require(b0 == e0 && b1 == e1 && b2 == e2, "pack6 != SimpleBitPack");
        uint256 s = b0 | (b1 << 8) | (b2 << 16);
        require((s & 63) == a0, "pack6 recover a0");
        require(((s >> 6) & 63) == a1, "pack6 recover a1");
        require(((s >> 12) & 63) == a2, "pack6 recover a2");
        require(((s >> 18) & 63) == a3, "pack6 recover a3");
    }
}
