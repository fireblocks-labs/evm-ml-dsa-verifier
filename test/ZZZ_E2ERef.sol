// SPDX-License-Identifier: MIT
// FILE: test/ZZZ_E2ERef.sol
//
// End-to-end FIPS 204 ML-DSA-44 REFERENCE verifier for differential testing:
// the pre-extraction research build the shipped src/ contracts are measured
// and cross-checked against, assembled from the individually verified
// components in this test tree:
//   * Keccak-f[1600]/SHAKE256:  test/ZZZ_FastKeccak.sol (helper @ 0xF1600AA)
//   * z/h decode + UseHint+w1Encode: test/ZZZ_decode.t.sol, test/ZZZ_decode2.t.sol
//   * packed-SWAR forward NTT + MAC kernels: test/ZZZ_NttVariants.sol
//   * packed-SWAR inverse NTT: test/ZZZ_InvNtt.sol
// Algorithm flow mirrors the upstream reference decoder in
// test/vendor/ZKNOX_dilithium_core.sol, with the public key consumed from a
// raw data contract (no abi.decode, no expandMat/expandVec):
//   [    0 ..    64)  tr  (64 bytes)
//   [   64 ..  4160)  t1hat = NTT(t1 * 2^d), 4 polys, compact 8x32-bit/word
//   [ 4160 .. 20544)  Ahat (NTT domain), 16 polys row-major i*4+j, same packing
// (compact packing = coeff (8w+s) of poly at bits 32s of word w, exactly the
//  compact_256(32) layout of prepare/prepare.py and tools/fixtures/fx_common.py
//  `pk_blob`; blob built by tools/fixtures/e2e_pk.py).
//
// The matvec consumes the compact 8-coeff/word pk words DIRECTLY (32-bit
// fields, values < q < 2^23) against the 4-lane packed NTT vectors, with lazy
// 64-bit-lane accumulation (4 products < 2^48/lane), and the c*t1hat
// subtraction folded in as lane += Q*2^24 - c*t1 (Q*2^24 > (q-1)^2, total
// lane < 2^49), one reducePacked pass, then the packed inverse NTT.
pragma solidity ^0.8.25;

import {f1600Fast, shake256Fast, _xorBlockFast, _squeezeBlockFast} from "./ZZZ_FastKeccak.sol";
import {unpackHFast} from "./ZZZ_decode.t.sol";
import {useHintFast2} from "./ZZZ_decode2.t.sol";
import {nttFwV3, packCoeffs, reducePacked, nttFwTable} from "./ZZZ_NttVariants.sol";
import {nttInvV3, iunpackCoeffs, nttInvTable} from "./ZZZ_InvNtt.sol";

uint256 constant E2E_Q = 8380417; // Dilithium prime
uint256 constant E2E_KQ24 = 0x7fe001000000; // Q << 24, > (Q-1)^2 = 70231372333056
uint256 constant E2E_M32 = 0xffffffff;
uint256 constant E2E_M64 = 0xffffffffffffffff;
uint256 constant E2E_PK_SIZE = 20544;
uint256 constant E2E_T1_OFF = 64;
uint256 constant E2E_A_OFF = 4160;

// ---------------------------------------------------------------------------
// unpackZStrict: copied from test/ZZZ_decode2.t.sol:unpackZFast2 (machine
// re-generation by build_e2e_honest.py, which is not preserved; provenance
// in that file)
// with exactly two mechanical changes, applied to every coefficient block
// (a third, the de-unrolling from 8 quads per iteration to 1, came with the
// move to via-IR codegen and changes neither the predicate nor the output):
//   * norm check tightened to the strict FIPS-204 bound ||z||inf < gamma1-beta:
//     pass iff v in [79, 262065]  (was [78, 262066], which also accepted
//     |z| == gamma1-beta = 130994 — matching the repo verifier but off-by-one
//     vs FIPS 204 Algorithm 3 / dilithium_py's check_norm_bound).
//   * output canonicalized to [0, q): store mod(q + gamma1 - v, q) instead of
//     gamma1 + q*(v>>17) - v, so z == 0 (v == 131072) decodes to 0, not q.
//     The packed V3 NTT's machine-verified lane bounds require input < q.
// ---------------------------------------------------------------------------
function unpackZStrict(bytes memory input) pure returns (uint256[] memory out, bool normOk) {
    out = new uint256[](1024);
    uint256 fail = 0;
    assembly ("memory-safe") {
        let src := add(input, 32)
        let dst := add(out, 32)
        let w := 0
        for { let blk := 0 } lt(blk, 256) { blk := add(blk, 1) } {
                w := mload(src)
                {
                    let v := or(or(byte(0, w), shl(8, byte(1, w))), shl(16, and(byte(2, w), 3)))
                    fail := or(fail, iszero(lt(sub(v, 79), 261987)))
                    mstore(dst, mod(sub(8511489, v), 8380417))
                }
                {
                    let v := or(or(shr(2, byte(2, w)), shl(6, byte(3, w))), shl(14, and(byte(4, w), 15)))
                    fail := or(fail, iszero(lt(sub(v, 79), 261987)))
                    mstore(add(dst, 32), mod(sub(8511489, v), 8380417))
                }
                {
                    let v := or(or(shr(4, byte(4, w)), shl(4, byte(5, w))), shl(12, and(byte(6, w), 63)))
                    fail := or(fail, iszero(lt(sub(v, 79), 261987)))
                    mstore(add(dst, 64), mod(sub(8511489, v), 8380417))
                }
                {
                    let v := or(or(shr(6, byte(6, w)), shl(2, byte(7, w))), shl(10, byte(8, w)))
                    fail := or(fail, iszero(lt(sub(v, 79), 261987)))
                    mstore(add(dst, 96), mod(sub(8511489, v), 8380417))
                }
            src := add(src, 9)
            dst := add(dst, 128)
        }
    }
    normOk = (fail == 0);
}

// ---------------------------------------------------------------------------
// SampleInBall (FIPS 204 Algorithm 29, tau = 39), word-level against the fast
// sponge: absorb the 32-byte c-tilde in one rate block, squeeze sign bits +
// rejection bytes from the same XOF stream. Mirrors
// test/vendor/ZKNOX_SampleInBall.sol:sampleInBallNist byte-for-byte in stream
// consumption (first 8 squeezed bytes = sign bits little-endian == lane 0 of
// the state, then one rejection byte at a time, block-refill on exhaustion).
// Output: 256 coefficients in {0, 1, q-1}, canonical.
// ---------------------------------------------------------------------------
function sampleInBallE2E(bytes32 cTilde) pure returns (uint256[] memory c) {
    uint256[25] memory st; // zeroed sponge state
    bytes memory blk = new bytes(168); // 136-byte rate block (+24B squeeze spill +8 pad)
    uint256 bp;
    assembly ("memory-safe") {
        bp := add(blk, 32)
        mstore(bp, cTilde)
        mstore8(add(bp, 32), 0x1f) // SHAKE domain padding
        mstore8(add(bp, 135), 0x80) // final padding bit
    }
    _xorBlockFast(st, bp);
    f1600Fast(st);
    _squeezeBlockFast(st, bp);
    // first 8 squeezed bytes, little-endian == 64-bit lane 0 of the state
    uint256 signInt = st[0];
    c = new uint256[](256);
    uint256 pos = 8;
    unchecked {
        for (uint256 i = 217; i < 256; ++i) {
            // 217 = 256 - TAU
            uint256 j;
            while (true) {
                if (pos == 136) {
                    f1600Fast(st);
                    _squeezeBlockFast(st, bp);
                    pos = 0;
                }
                assembly ("memory-safe") {
                    j := byte(0, mload(add(bp, pos)))
                }
                ++pos;
                if (j <= i) break;
            }
            c[i] = c[j];
            c[j] = (signInt & 1 == 1) ? E2E_Q - 1 : 1;
            signInt >>= 1;
        }
    }
}

// ---------------------------------------------------------------------------
// packFromFlat: packCoeffs (test/ZZZ_NttVariants.sol) reading 256 coefficients
// starting at word offset `wordOff` of a flat array (canonical lanes in, 64
// packed words out). Copied kernel, offset parameter added.
// ---------------------------------------------------------------------------
function packFromFlat(uint256[] memory flat, uint256 wordOff) pure returns (uint256[] memory w) {
    w = new uint256[](64);
    assembly ("memory-safe") {
        let pa := add(add(flat, 0x20), shl(5, wordOff))
        let pw := add(w, 0x20)
        let pe := add(pa, 0x2000)
        for {} lt(pa, pe) {} {
            mstore(
                pw,
                or(
                    or(mload(pa), shl(64, mload(add(pa, 0x20)))),
                    or(shl(128, mload(add(pa, 0x40))), shl(192, mload(add(pa, 0x60))))
                )
            )
            pa := add(pa, 0x80)
            pw := add(pw, 0x20)
        }
    }
}

// ---------------------------------------------------------------------------
// macCompactLazy: acc[lane] += A[coeff] * z[lane] with A consumed directly in
// the pk's compact 8x32-bit/word layout (one A-word feeds two packed z/acc
// words) and z in the 4x64-bit-lane packed layout. Lazy accumulation
// (products < 2^46, up to 4 per lane before reducePacked). Derived from
// macPackedLazy in test/ZZZ_NttVariants.sol.
// ---------------------------------------------------------------------------
function macCompactLazy(uint256[] memory acc, uint256 aPtr, uint256[] memory z) pure {
    assembly ("memory-safe") {
        let pz := add(z, 0x20)
        let pd := add(acc, 0x20)
        let ae := add(aPtr, 0x400)
        for {} lt(aPtr, ae) {} {
            let wa := mload(aPtr)
            let wz := mload(pz)
            mstore(
                pd,
                add(
                    mload(pd),
                    or(
                        or(
                            mul(and(wa, E2E_M32), and(wz, E2E_M64)),
                            shl(64, mul(and(shr(32, wa), E2E_M32), and(shr(64, wz), E2E_M64)))
                        ),
                        or(
                            shl(128, mul(and(shr(64, wa), E2E_M32), and(shr(128, wz), E2E_M64))),
                            shl(192, mul(and(shr(96, wa), E2E_M32), shr(192, wz)))
                        )
                    )
                )
            )
            wz := mload(add(pz, 0x20))
            pd := add(pd, 0x20)
            mstore(
                pd,
                add(
                    mload(pd),
                    or(
                        or(
                            mul(and(shr(128, wa), E2E_M32), and(wz, E2E_M64)),
                            shl(64, mul(and(shr(160, wa), E2E_M32), and(shr(64, wz), E2E_M64)))
                        ),
                        or(
                            shl(128, mul(and(shr(192, wa), E2E_M32), and(shr(128, wz), E2E_M64))),
                            shl(192, mul(shr(224, wa), shr(192, wz)))
                        )
                    )
                )
            )
            aPtr := add(aPtr, 0x20)
            pz := add(pz, 0x40)
            pd := add(pd, 0x20)
        }
    }
}

// ---------------------------------------------------------------------------
// macSubCT1Lazy: acc[lane] += Q*2^24 - c[lane] * t1[coeff]  (the A*z - c*t1
// subtraction folded into the lazy accumulator; Q*2^24 > (q-1)^2 keeps every
// lane delta positive and < 2^47; total lane < 2^49 < 2^64). c is packed
// 4-lane canonical, t1 is the pk's compact 8x32-bit/word layout.
// ---------------------------------------------------------------------------
function macSubCT1Lazy(uint256[] memory acc, uint256[] memory c, uint256 tPtr) pure {
    assembly ("memory-safe") {
        let cp := add(c, 0x20)
        let pd := add(acc, 0x20)
        let te := add(tPtr, 0x400)
        for {} lt(tPtr, te) {} {
            let wt := mload(tPtr)
            let wc := mload(cp)
            mstore(
                pd,
                add(
                    mload(pd),
                    or(
                        or(
                            sub(E2E_KQ24, mul(and(wc, E2E_M64), and(wt, E2E_M32))),
                            shl(64, sub(E2E_KQ24, mul(and(shr(64, wc), E2E_M64), and(shr(32, wt), E2E_M32))))
                        ),
                        or(
                            shl(128, sub(E2E_KQ24, mul(and(shr(128, wc), E2E_M64), and(shr(64, wt), E2E_M32)))),
                            shl(192, sub(E2E_KQ24, mul(shr(192, wc), and(shr(96, wt), E2E_M32))))
                        )
                    )
                )
            )
            wc := mload(add(cp, 0x20))
            pd := add(pd, 0x20)
            mstore(
                pd,
                add(
                    mload(pd),
                    or(
                        or(
                            sub(E2E_KQ24, mul(and(wc, E2E_M64), and(shr(128, wt), E2E_M32))),
                            shl(64, sub(E2E_KQ24, mul(and(shr(64, wc), E2E_M64), and(shr(160, wt), E2E_M32))))
                        ),
                        or(
                            shl(128, sub(E2E_KQ24, mul(and(shr(128, wc), E2E_M64), and(shr(192, wt), E2E_M32)))),
                            shl(192, sub(E2E_KQ24, mul(shr(192, wc), shr(224, wt))))
                        )
                    )
                )
            )
            tPtr := add(tPtr, 0x20)
            cp := add(cp, 0x40)
            pd := add(pd, 0x20)
        }
    }
}

// ---------------------------------------------------------------------------
// The assembled verifier.
// ---------------------------------------------------------------------------
contract ZZZ_E2ERef {
    /// @notice FIPS 204 ML-DSA-44 Verify (empty context).
    /// @param pkPtr  raw pk data contract (layout in the file header)
    /// @param message the message M (mPrime = 0x00 || 0x00 || M internally)
    /// @param sig    c_tilde(32) || z(2304) || h(84), 2420 bytes
    function verify(address pkPtr, bytes calldata message, bytes calldata sig) external view returns (bool) {
        uint256[10] memory gasProbe;
        return _verify(pkPtr, message, sig, gasProbe);
    }

    /// @notice same as verify() but returns the internal gasleft() probes
    ///         (indices 0..7 = stage boundaries, see _verify).
    function verifyProfiled(address pkPtr, bytes calldata message, bytes calldata sig)
        external
        view
        returns (bool ok, uint256[10] memory gasProbe)
    {
        ok = _verify(pkPtr, message, sig, gasProbe);
    }

    function _verify(address pkPtr, bytes calldata message, bytes calldata sig, uint256[10] memory gasProbe)
        internal
        view
        returns (bool)
    {
        gasProbe[0] = gasleft();
        if (sig.length != 2420) return false;

        // ---- pk blob -> memory (single EXTCODECOPY stream); 0 on size mismatch
        uint256 pkB = _loadPk(pkPtr);
        if (pkB == 0) return false;

        // ---- decode signature: h -> bitmasks (validity + weight), z -> flat 1024
        uint256[4] memory hMasks;
        {
            bool hOk;
            uint256 hWeight;
            (hOk, hMasks, hWeight) = unpackHFast(sig[2336:2420]);
            if (!hOk || hWeight > 80) return false;
        }
        uint256[] memory zFlat;
        {
            bool normOk;
            (zFlat, normOk) = unpackZStrict(sig[32:2336]);
            if (!normOk) return false;
        }
        gasProbe[1] = gasleft();

        // ---- mu = SHAKE256(tr || 0x00 || 0x00 || M, 64)  (1 permutation for |M| <= 69)
        bytes memory mu = _computeMu(pkB, message);
        gasProbe[2] = gasleft();

        // ---- w'_i = InvNTT( A[i]*NTT(z) - NTT(c) o t1hat[i] ), rows as coefficients
        uint256[][] memory r = _wPrimeRows(pkB, bytes32(sig[0:32]), zFlat, gasProbe);
        gasProbe[5] = gasleft();

        // ---- w1 = UseHint + w1Encode (768 bytes)
        bytes memory w1 = useHintFast2(hMasks, r);
        gasProbe[6] = gasleft();

        // ---- cTilde' = SHAKE256(mu || w1, 32)  (7 permutations)
        bool res = _finalHash(mu, w1) == bytes32(sig[0:32]);
        gasProbe[7] = gasleft();
        return res;
    }

    /// copy the pk data contract into memory; returns the data pointer, or 0
    /// if the code size does not match the expected blob layout.
    function _loadPk(address pkPtr) private view returns (uint256 pkB) {
        assembly ("memory-safe") {
            if eq(extcodesize(pkPtr), E2E_PK_SIZE) {
                pkB := mload(0x40)
                mstore(0x40, add(pkB, E2E_PK_SIZE))
                extcodecopy(pkPtr, pkB, 0, E2E_PK_SIZE)
            }
        }
    }

    /// mu = SHAKE256(tr || 0x00 || 0x00 || M, 64) — tr at pkB, empty context.
    function _computeMu(uint256 pkB, bytes calldata message) private pure returns (bytes memory mu) {
        bytes memory muIn = new bytes(66 + message.length);
        assembly ("memory-safe") {
            let d := add(muIn, 32)
            mcopy(d, pkB, 64) // tr
            // bytes 64,65 (mPrime domain separator + ctx length) stay 0x00
            calldatacopy(add(d, 66), message.offset, message.length)
        }
        mu = shake256Fast(muIn, 64);
    }

    /// the arithmetic core: cHat = NTT(SampleInBall(cTilde)); zHat = NTT(z);
    /// row i: reduce(A[i] (.) zHat + (Q*2^24 - cHat o t1hat[i])) -> InvNTT -> coeffs.
    function _wPrimeRows(uint256 pkB, bytes32 cTilde, uint256[] memory zFlat, uint256[10] memory gasProbe)
        private
        view
        returns (uint256[][] memory r)
    {
        uint256[] memory ntProf = new uint256[](10); // scratch for the NTTs' gas probes

        // nttFwV3 emits LAZY lanes (< 17q, congruent); the REFERENCE pipeline
        // canonicalises them immediately so its own KQ24-offset lazy MACs keep
        // their original canonical-input bounds (gas is irrelevant here)
        uint256 fwT = nttFwTable();
        uint256 invT = nttInvTable();
        uint256[] memory cHat = nttFwV3(packCoeffs(sampleInBallE2E(cTilde)), ntProf, fwT);
        reducePacked(cHat);
        gasProbe[3] = gasleft();

        uint256[][] memory zHat = new uint256[][](4);
        for (uint256 j = 0; j < 4; ++j) {
            zHat[j] = nttFwV3(packFromFlat(zFlat, j << 8), ntProf, fwT);
            reducePacked(zHat[j]);
        }
        gasProbe[4] = gasleft();

        r = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            uint256[] memory acc = new uint256[](64); // zeroed lazy accumulator
            uint256 aRow = pkB + E2E_A_OFF + (i << 12);
            macCompactLazy(acc, aRow, zHat[0]);
            macCompactLazy(acc, aRow + 1024, zHat[1]);
            macCompactLazy(acc, aRow + 2048, zHat[2]);
            macCompactLazy(acc, aRow + 3072, zHat[3]);
            macSubCT1Lazy(acc, cHat, pkB + E2E_T1_OFF + (i << 10));
            reducePacked(acc); // canonical lanes < q
            nttInvV3(acc, ntProf, invT);
            r[i] = iunpackCoeffs(acc);
        }
    }

    /// cTilde' = SHAKE256(mu || w1, 32)
    function _finalHash(bytes memory mu, bytes memory w1) private pure returns (bytes32 cPrime) {
        bytes memory fin = new bytes(832);
        assembly ("memory-safe") {
            mcopy(add(fin, 32), add(mu, 32), 64)
            mcopy(add(fin, 96), add(w1, 32), 768)
        }
        bytes memory ct2 = shake256Fast(fin, 32);
        assembly ("memory-safe") {
            cPrime := mload(add(ct2, 32))
        }
    }
}
