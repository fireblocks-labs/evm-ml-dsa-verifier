// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC_sampleinball.t.sol
//
// The only probabilistic loop in either verifier is SampleInBall's rejection
// sampler (FIPS 204 Algorithm 29, tau = 39), whose input c~ is fully
// attacker-chosen. This file bounds its behaviour on both subjects' samplers:
// the reference verifier's sampleInBallE2E (test/ZZZ_E2ERef.sol) and the shipped
// verifier's sampleInBallPacked (src/Decode.sol).
//
// Both samplers absorb the 32-byte c~ in one rate block, take the 8-byte sign
// word from the first squeeze, then draw rejection bytes from the SAME XOF
// stream, refilling by permuting the sponge once more when a 136-byte block is
// exhausted. Two facts make this safe against griefing:
//   * the refill is a correct XOF continuation, so a longer squeeze reproduces
//     the shorter one byte-for-byte (asserted below) — a refill changes no
//     decision, it only supplies more bytes;
//   * a single 136-byte block (8 sign bytes + 128 rejection bytes) suffices with
//     overwhelming probability, so a refill essentially never happens and, when
//     it does, costs exactly one extra permutation — no unbounded or amplifying
//     work. Capping the loop is not an option: it would break FIPS 204, whose
//     SampleInBall squeezes without bound.
//
// The two samplers consume the stream byte-identically, so they must agree
// coefficient-for-coefficient; the reference sampler (validated end to end
// against the ACVP vectors through ZZZ_E2ERef) is used as the differential
// oracle here.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {shake256Fast, _F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {shake256Fast170} from "../src/FastKeccak170.sol";
import {sampleInBallE2E, E2E_Q} from "./ZZZ_E2ERef.sol";
import {sampleInBallPacked} from "../src/Decode.sol";

contract SECSampleInBallTest is Test {
    address f1600;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE); // reference sampler's helper
        f1600 = deployF1600_170(); // shipped sampler's helper
    }

    /// unpack the shipped sampler's packed-SWAR output (4 coeffs / 64-bit lanes
    /// per 256-bit word; lane l of word i = coefficient 4i+l) to 256 coefficients.
    function _unpackPacked(uint256[] memory w) internal pure returns (uint256[] memory c) {
        c = new uint256[](256);
        for (uint256 k = 0; k < 256; ++k) {
            c[k] = (w[k >> 2] >> (64 * (k & 3))) & type(uint64).max;
        }
    }

    // ================================= two-sampler implementation equality ==

    function test_shipped_and_reference_samplers_agree() public view {
        for (uint256 k = 0; k < 48; ++k) {
            bytes32 ct = keccak256(abi.encode("sib", k));
            uint256[] memory a = _unpackPacked(sampleInBallPacked(ct, f1600));
            uint256[] memory b = sampleInBallE2E(ct);
            uint256 nz = 0;
            for (uint256 i = 0; i < 256; ++i) {
                assertEq(a[i], b[i], "shipped vs reference SampleInBall mismatch");
                assertTrue(a[i] == 0 || a[i] == 1 || a[i] == E2E_Q - 1, "coefficient in {0, 1, q-1}");
                if (a[i] != 0) ++nz;
            }
            assertEq(nz, 39, "tau = 39 nonzero coefficients");
        }
    }

    // ==================================== XOF continuation makes refill safe ==

    /// A longer squeeze extends a shorter one byte-for-byte, so the sampler's
    /// block-2 refill reproduces exactly the decisions of a single longer squeeze.
    function test_xof_continuation_is_transparent() public view {
        for (uint256 k = 0; k < 24; ++k) {
            bytes memory ct = abi.encodePacked(keccak256(abi.encode("prefix", k)));
            bytes memory s136 = shake256Fast170(ct, 136, f1600);
            bytes memory s272 = shake256Fast170(ct, 272, f1600);
            bytes memory s544 = shake256Fast170(ct, 544, f1600);
            // the reference sponge must extend identically
            bytes memory r272 = shake256Fast(ct, 272);
            for (uint256 i = 0; i < 136; ++i) {
                assertEq(s272[i], s136[i], "272-byte squeeze extends the 136-byte one");
                assertEq(s544[i], s136[i], "544-byte squeeze extends the 136-byte one");
                assertEq(r272[i], s136[i], "reference sponge agrees on the prefix");
            }
            for (uint256 i = 0; i < 272; ++i) {
                assertEq(s544[i], s272[i], "544 extends 272");
                assertEq(r272[i], s272[i], "reference sponge agrees to 272");
            }
        }
    }

    // ============================ rejection-byte consumption over one block ==

    /// Replays FIPS 204 SampleInBall's byte consumption on the 136-byte prefix.
    function _bytesConsumed(bytes32 ct) internal view returns (uint256 used, bool exhausted) {
        bytes memory stream = shake256Fast170(abi.encodePacked(ct), 136, f1600);
        uint256 pos = 8; // first 8 bytes are the sign word
        for (uint256 i = 217; i < 256; ++i) {
            while (true) {
                if (pos >= 136) return (pos - 8, true);
                uint256 j = uint8(stream[pos]);
                ++pos;
                if (j <= i) break;
            }
        }
        return (pos - 8, false);
    }

    function test_rejection_loop_fits_a_single_block() public view {
        uint256 maxUsed = 0;
        uint256 total = 0;
        uint256 n = 1024;
        for (uint256 k = 0; k < n; ++k) {
            (uint256 used, bool ex) = _bytesConsumed(keccak256(abi.encode("reject", k)));
            assertFalse(ex, "the 136-byte prefix must suffice (P(refill) ~ 2^-205)");
            if (used > maxUsed) maxUsed = used;
            total += used;
        }
        console.log("SampleInBall rejection bytes over 1024 attacker-chosen c~:");
        console.log("   max / mean(x100) / available:", maxUsed, (total * 100) / n, 128);
        assertLe(maxUsed, 128, "worst observed consumption fits the single prefix");
    }

    // ========================================= gas is bounded, not amplifying

    function test_shipped_sampler_gas_is_bounded() public view {
        uint256 lo = type(uint256).max;
        uint256 hi = 0;
        for (uint256 k = 0; k < 64; ++k) {
            bytes32 ct = keccak256(abi.encode("sib gas", k));
            uint256 g0 = gasleft();
            sampleInBallPacked(ct, f1600);
            uint256 used = g0 - gasleft();
            if (used < lo) lo = used;
            if (used > hi) hi = used;
        }
        console.log("sampleInBallPacked gas min / max over 64 c~:", lo, hi);
        assertLt(hi - lo, 20000, "gas spread must be small (bounded rejection loop)");
    }
}
