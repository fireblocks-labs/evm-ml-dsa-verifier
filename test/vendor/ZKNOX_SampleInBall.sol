// Copyright (C) 2026 - ZKNOX
// License: This software is licensed under MIT License
// This Code may be reused including this header, license and copyright notice.
// FILE: ZKNOX_SampleInBall.sol
// Description: SampleInBall function necessary in Dilithium
// NOTE: vendored subset — only the NIST (SHAKE256) variant is retained; the
// upstream KeccakPrng variant and its ZKNOX_keccak_prng.sol dependency are not
// used by this repository's tests.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {CtxShake, shakeUpdate, shakeDigest, shakeSqueeze} from "./ZKNOX_shake.sol";

// SampleInBall as specified in Dilithium
function sampleInBallNist(bytes memory cTilde, uint256 tau, uint256 q) pure returns (uint256[] memory c) {
    CtxShake memory ctx;
    ctx = shakeUpdate(ctx, cTilde);
    bytes memory signBytes = shakeDigest(ctx, 8);
    uint256 signInt = 0;
    for (uint256 i = 0; i < 8; i++) {
        signInt |= uint256(uint8(signBytes[i])) << (8 * i);
    }

    // Now set tau values of c to be ±1
    c = new uint256[](256);
    uint256 j;
    bytes memory bytesJ;
    for (uint256 i = 256 - tau; i < 256; i++) {
        // Rejects values until a value j <= i is found
        while (true) {
            (ctx, bytesJ) = shakeSqueeze(ctx, 1);
            j = uint256(uint8(bytesJ[0]));
            if (j <= i) {
                break;
            }
        }
        c[i] = c[j];
        if (signInt & 1 == 1) {
            c[j] = q - 1;
        } else {
            c[j] = 1;
        }
        signInt >>= 1;
    }
}
