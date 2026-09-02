// SPDX-License-Identifier: MIT
// FILE: test/NttMicro.t.sol
//
// Per-PASS gas profile of the packed-SWAR forward and inverse NTTs, plus
// loop-vs-unroll and modular-reduction-form microbenchmarks for the butterfly
// kernels. The forward runs its eight layers as THREE fused passes (radix-8
// L1+L2+L3, radix-8 L4+L5+L6, in-word L7+L8); the inverse runs FOUR.
// The NTT block (5 forward + 4 inverse transforms) dominates the
// verifier's arithmetic cost; the profile shows whether any single pass is
// anomalous or whether the cost is uniform codegen overhead.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {nttFwV3, packCoeffs, Q, nttFwTable} from "./ZZZ_NttVariants.sol";
import {nttInvV3, nttInvTable} from "./ZZZ_InvNtt.sol";

contract NttMicroTest is Test {
    uint256 sink;

    function _canon(uint256 seed) internal pure returns (uint256[] memory a) {
        a = new uint256[](256);
        for (uint256 i = 0; i < 256; ++i) {
            a[i] = uint256(keccak256(abi.encodePacked(seed, i))) % Q;
        }
    }

    function test_ntt_00_forward_layer_profile() public {
        uint256[] memory prof = new uint256[](10);
        uint256[] memory p = packCoeffs(_canon(1));
        // warm the code path once so the profile is steady-state
        nttFwV3(packCoeffs(_canon(2)), prof, nttFwTable());
        uint256 g0 = gasleft();
        nttFwV3(p, prof, nttFwTable());
        uint256 total = g0 - gasleft();
        console.log("nttFwV3 total:", total);
        // three fused passes: radix-8 L1+L2+L3, radix-8 L4+L5+L6, in-word L7+L8
        for (uint256 k = 1; k < 4; ++k) {
            if (prof[k - 1] > prof[k]) {
                console.log("  fwd segment", k, prof[k - 1] - prof[k]);
            }
        }
        sink = p[0];
    }

    function test_ntt_01_inverse_layer_profile() public {
        uint256[] memory prof = new uint256[](10);
        uint256[] memory p = nttFwV3(packCoeffs(_canon(3)), prof, nttFwTable());
        uint256[] memory prof2 = new uint256[](10);
        uint256 g0 = gasleft();
        nttInvV3(p, prof2, nttInvTable());
        uint256 total = g0 - gasleft();
        console.log("nttInvV3 total:", total);
        // four passes: entry fold + L1+L2, L3+L4, L5+L6, L7+L8+scale
        for (uint256 k = 1; k < 5; ++k) {
            if (prof2[k - 1] > prof2[k]) {
                console.log("  inv segment", k, prof2[k - 1] - prof2[k]);
            }
        }
        sink = p[0];
    }

    // ---- loop tax: identical work, rolled vs unrolled x2 vs unrolled x4 ----
    function test_ntt_10_loop_tax() public {
        uint256[] memory a = new uint256[](64);
        uint256 acc;
        uint256 g0;

        g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(a, 32)
            let e := add(p, 0x800)
            for {} lt(p, e) { p := add(p, 0x20) } { mstore(p, add(mload(p), 1)) }
        }
        console.log("rolled 64x (mload+add+mstore):", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(a, 32)
            let e := add(p, 0x800)
            for {} lt(p, e) { p := add(p, 0x40) } {
                mstore(p, add(mload(p), 1))
                mstore(add(p, 0x20), add(mload(add(p, 0x20)), 1))
            }
        }
        console.log("unrolled x2:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(a, 32)
            let e := add(p, 0x800)
            for {} lt(p, e) { p := add(p, 0x80) } {
                mstore(p, add(mload(p), 1))
                mstore(add(p, 0x20), add(mload(add(p, 0x20)), 1))
                mstore(add(p, 0x40), add(mload(add(p, 0x40)), 1))
                mstore(add(p, 0x60), add(mload(add(p, 0x60)), 1))
            }
        }
        console.log("unrolled x4:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(a, 32)
            for { let i := 0 } lt(i, 64) { i := add(i, 1) } { acc := add(acc, mload(add(p, shl(5, i)))) }
        }
        console.log("indexed loop (shl address calc):", g0 - gasleft());
        sink = acc;
    }

    // ---- Barrett vs MULMOD vs MOD for a single modular reduction ----
    // The shipped reduction is the TWO-STEP LANE-LOCAL Barrett: a coarse step
    // with MU33 = floor(2^33/q) = 1025 followed by the unit step
    // floor(2^23/q) == 1 (multiply elided). Two steps cost more opcodes than one
    // wide Barrett would, but every intermediate stays under 2^64, so the packed
    // form reduces all FOUR 64-bit lanes with the same four opcodes -- no
    // spreading, no repacking. The packed measurement below is the one that
    // matters: divide it by 4 for the per-coefficient cost.
    function test_ntt_20_reduction_forms() public {
        uint256 g0;
        uint256 acc = 0x123456789abc;
        uint256 MU33 = 1025;
        uint256 QHATM31 = 0x000000007fffffff000000007fffffff000000007fffffff000000007fffffff;

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                x := sub(x, mul(shr(33, mul(x, MU33)), Q))
                x := add(sub(x, mul(shr(23, x), Q)), 1)
            }
            acc := x
        }
        console.log("256x two-step lane-local Barrett (scalar):", g0 - gasleft());

        // the same block on a packed 4-lane word: 4 coefficients per iteration
        uint256 w = 0x0000000000123456000000000023456700000000003456780000000000456789;
        g0 = gasleft();
        assembly ("memory-safe") {
            let t0 := w
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                t0 := sub(t0, mul(and(shr(33, mul(t0, MU33)), QHATM31), Q))
                t0 := sub(t0, mul(and(shr(23, t0), QHATM31), Q))
                t0 := add(t0, 1)
            }
            w := t0
        }
        console.log("256x packed 4-lane block (= 1024 coeffs):", g0 - gasleft());
        acc = acc ^ w;

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := add(mod(x, Q), 1) }
            acc := x
        }
        console.log("256x MOD:", g0 - gasleft());

        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } { x := add(mulmod(x, 1, Q), 1) }
            acc := x
        }
        console.log("256x MULMOD(x,1,Q):", g0 - gasleft());
        sink = acc;
    }

    // ---- is a fused matvec row cheaper than 5 separate passes? ----
    function test_ntt_30_accumulator_traffic() public {
        uint256[] memory acc = new uint256[](64);
        uint256[] memory z = packCoeffs(_canon(9));
        uint256 g0;
        // 4 passes of read-modify-write over 64 words (the current shape)
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let k := 0 } lt(k, 4) { k := add(k, 1) } {
                let p := add(acc, 32)
                let s := add(z, 32)
                let e := add(p, 0x800)
                for {} lt(p, e) { p := add(p, 0x20) } {
                    mstore(p, add(mload(p), mload(s)))
                    s := add(s, 0x20)
                }
            }
        }
        console.log("4 separate accumulate passes:", g0 - gasleft());
        // one fused pass doing the same four adds
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(acc, 32)
            let s := add(z, 32)
            let e := add(p, 0x800)
            for {} lt(p, e) { p := add(p, 0x20) } {
                let v := mload(s)
                mstore(p, add(mload(p), add(add(v, v), add(v, v))))
                s := add(s, 0x20)
            }
        }
        console.log("1 fused accumulate pass:", g0 - gasleft());
        sink = acc[0];
    }
}
