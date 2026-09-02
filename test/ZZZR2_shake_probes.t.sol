// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// ZZZR2 auditor scratch: empirically validate the two NON-measured SHAKE lines
// of the verify gas budget, which are derived by subtracting the
// per-permutation delta (62,120 - 44,750 = 17,370) from the shapes measured in
// ZZZR_shapes*.t.sol:
//   - mu shape (98B in -> 64B out):      claimed 65,430 - 17,370 = 48,060  (~48.1k)
//   - SampleInBall tight (32B -> stream): claimed 74,892 - 17,370 = 57,522 (~57.5k)
// Measured here against the CURRENT ZZZ_FastKeccak.sol (helper-contract f1600,
// 44,750/perm warm) with an explicit warm-up call so the lazy vm.etch + cold
// account access of the first invocation does not pollute the shape numbers
// (matching the warm basis used for the 44,750 figure itself).
// The SampleInBall glue below is copied VERBATIM from
// ZZZR_shapes2.t.sol::test_sampleinball_tight (same code, same inputs) so the
// only difference vs the 74,892 figure measured there is the new permutation.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {shake256Fast} from "./ZZZ_FastKeccak.sol";

contract ZZZR2ShakeProbesTest is Test {
    /// force the lazy etch of the f1600 helper + warm its account, off the clock
    function _warm() internal pure {
        bytes memory w = shake256Fast(hex"00", 32);
        require(w.length == 32, "warm");
    }

    // ------------------------------------------------------------------
    // mu shape: SHAKE256(tr(64B) || 0x00 0x00 || M(32B), 64) = 98B in, 64B out
    // (identical input construction to ZZZR_shapes.t.sol::test_mu_shape)
    // ------------------------------------------------------------------
    function test_mu_shape_warm() public view {
        _warm();
        bytes memory inp = new bytes(98);
        for (uint256 i = 0; i < 98; i++) {
            inp[i] = bytes1(uint8(i + 1));
        }
        uint256 g0 = gasleft();
        bytes memory mu = shake256Fast(inp, 64);
        uint256 g = g0 - gasleft();
        console.log("R2 mu shape (98B in, 64B out), warm helper, gas:", g);
        require(mu.length == 64, "len");
    }

    // ------------------------------------------------------------------
    // SampleInBall-equivalent: absorb 32B, squeeze 136B stream; consume 8 sign
    // bytes + ~50 single bytes through the tau=39 rejection loop; build the
    // full 256-word c poly + 39-entry sparse pair list. Verbatim ZZZR_shapes2 glue.
    // ------------------------------------------------------------------
    function test_sampleinball_tight_warm() public view {
        _warm();
        bytes memory ct = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            ct[i] = bytes1(uint8(0xA0 + i));
        }
        uint256[] memory c = new uint256[](256);
        uint256[] memory pairs = new uint256[](39);
        uint256 g0 = gasleft();
        bytes memory stream = shake256Fast(ct, 136);
        uint256 gShake = g0 - gasleft();
        assembly ("memory-safe") {
            let sp := add(stream, 32)
            let signs := shr(192, mload(sp)) // first 8 bytes as 64 sign bits
            let bp := add(sp, 8)
            let cData := add(c, 32)
            let prData := add(pairs, 32)
            let sIdx := 0
            for { let i := 217 } lt(i, 256) { i := add(i, 1) } {
                let j := byte(0, mload(bp))
                bp := add(bp, 1)
                for {} gt(j, i) {} {
                    j := byte(0, mload(bp))
                    bp := add(bp, 1)
                }
                let cj := add(cData, shl(5, j))
                mstore(add(cData, shl(5, i)), mload(cj))
                let sbit := and(shr(sIdx, signs), 1)
                mstore(cj, add(1, mul(sbit, 8380415))) // 1 or q-1
                mstore(add(prData, shl(5, sIdx)), or(j, shl(8, sbit)))
                sIdx := add(sIdx, 1)
            }
        }
        uint256 g = g0 - gasleft();
        console.log("R2 SampleInBall tight, warm: shake(32B->136B) part gas:", gShake);
        console.log("R2 SampleInBall tight, warm: total gas:", g);
        require(c.length == 256 && pairs.length == 39, "unused");
    }

    // ------------------------------------------------------------------
    // Full 9-permutation SHAKE verify-budget, all warm: mu + SIB-tight + w1 hash
    // (the derived budget above: 430k = 324.9k + 48.1k + 57.5k)
    // ------------------------------------------------------------------
    function test_full_shake_budget_warm() public view {
        _warm();
        // mu
        bytes memory inp = new bytes(98);
        for (uint256 i = 0; i < 98; i++) {
            inp[i] = bytes1(uint8(i + 1));
        }
        uint256 g0 = gasleft();
        bytes memory mu = shake256Fast(inp, 64);
        uint256 gMu = g0 - gasleft();
        // w1 hash shape: 832B in, 32B out (7 perms)
        bytes memory in832 = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            in832[i] = bytes1(uint8(i));
        }
        uint256 g2 = gasleft();
        bytes memory o2 = shake256Fast(in832, 32);
        uint256 gW1 = g2 - gasleft();
        // SIB shake part only (glue measured in the dedicated test)
        bytes memory ct = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            ct[i] = bytes1(uint8(0xA0 + i));
        }
        uint256 g3 = gasleft();
        bytes memory stream = shake256Fast(ct, 136);
        uint256 gSib = g3 - gasleft();
        console.log("R2 warm mu (98->64):", gMu);
        console.log("R2 warm w1 (832->32):", gW1);
        console.log("R2 warm SIB shake part (32->136):", gSib);
        console.log("R2 warm sum mu+w1+SIBshake:", gMu + gW1 + gSib);
        require(mu.length == 64 && o2.length == 32 && stream.length == 136, "unused");
    }
}
