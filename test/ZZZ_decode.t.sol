// SPDX-License-Identifier: MIT
// Floor benchmarks for signature decode + UseHint/w1Encode with tight assembly.
// Correctness checked against the repo's unpackZ/unpackH/useHintDilithium on a real signature.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {Constants} from "./seed.sol";
import {PythonSigner} from "./vendor/ZKNOX_PythonSigner.sol";
import {unpackH, unpackZ} from "./vendor/ZKNOX_dilithium_core.sol";
import {useHintDilithium} from "./vendor/ZKNOX_hint.sol";

// Unpack 4x256 coeffs of 18-bit z, map to centered-mod-q, fused norm check.
// Layout in: 2304 bytes little-endian bit packing (FIPS 204). Out: 1024 words.
function unpackZFast(bytes memory input) pure returns (uint256[] memory out, bool normOk) {
    out = new uint256[](1024);
    uint256 fail = 0;
    assembly ("memory-safe") {
        let src := add(input, 32)
        let dst := add(out, 32)
        let bitOff := 0
        for { let i := 0 } lt(i, 1024) { i := add(i, 1) } {
            let w := mload(add(src, shr(3, bitOff)))
            // little-endian 3-byte assembly from big-endian word
            let v := or(or(byte(0, w), shl(8, byte(1, w))), shl(16, byte(2, w)))
            v := and(shr(and(bitOff, 7), v), 0x3ffff)
            // centered: z = gamma1 - v  (in [0,q) representation)
            let zc
            switch lt(v, 131072)
            case 1 { zc := sub(131072, v) }
            default { zc := sub(add(8380417, 131072), v) }
            // norm: fail iff min(zc, q-zc) > bound
            fail := or(fail, and(gt(zc, 130994), gt(sub(8380417, zc), 130994)))
            mstore(add(dst, shl(5, i)), zc)
            bitOff := add(bitOff, 18)
        }
    }
    normOk = (fail == 0);
}

// Parse 84-byte hint encoding into 4 bitmasks + validity + weight (FIPS 204 HintBitUnpack).
function unpackHFast(bytes memory hBytes)
    pure
    returns (bool ok, uint256[4] memory masks, uint256 weight)
{
    uint256 OMEGA_ = 80;
    ok = true;
    uint256 kIdx = 0;
    unchecked {
        for (uint256 i = 0; i < 4; i++) {
            uint256 omegaVal = uint8(hBytes[OMEGA_ + i]);
            if (omegaVal < kIdx || omegaVal > OMEGA_) return (false, masks, 0);
            uint256 m = 0;
            for (uint256 j = kIdx; j < omegaVal; j++) {
                uint256 idx = uint8(hBytes[j]);
                if (j > kIdx && idx <= uint8(hBytes[j - 1])) return (false, masks, 0);
                m |= (uint256(1) << idx);
            }
            masks[i] = m;
            weight += omegaVal - kIdx;
            kIdx = omegaVal;
        }
        for (uint256 j = kIdx; j < OMEGA_; j++) {
            if (uint8(hBytes[j]) != 0) return (false, masks, 0);
        }
    }
}

// Fused UseHint + w1Encode over h bitmasks and r (4x256 words), output 768 bytes.
function useHintFast(uint256[4] memory hMasks, uint256[][] memory r) pure returns (bytes memory hint) {
    hint = new bytes(768);
    assembly ("memory-safe") {
        let dst := add(hint, 32)
        for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
            let hmask := mload(add(hMasks, shl(5, i)))
            let rdata := add(mload(add(add(r, 32), shl(5, i))), 32)
            let wp := add(dst, mul(i, 192))
            for { let j := 0 } lt(j, 256) { j := add(j, 4) } {
                let packed := 0
                for { let s := 0 } lt(s, 4) { s := add(s, 1) } {
                    let jj := add(j, s)
                    let rv := mload(add(rdata, shl(5, jj)))
                    let r0 := mod(rv, 190464)
                    // r0_pos: 0 < r0 <= GAMMA_2
                    let r0pos := and(gt(r0, 0), iszero(gt(r0, 95232)))
                    // premul = rv - r0 (+ 2*GAMMA_2 if r0 > GAMMA_2, i.e. signed r0 < 0)
                    let premul := add(sub(rv, r0), mul(gt(r0, 95232), 190464))
                    let r1 := mul(div(premul, 190464), iszero(eq(premul, 8380416)))
                    // hint adjust: +1 if r0pos else +43, then mod 44 (unconditional mod is fine)
                    let hb := and(shr(jj, hmask), 1)
                    r1 := mod(add(r1, mul(hb, add(1, mul(iszero(r0pos), 42)))), 44)
                    packed := or(packed, shl(mul(s, 6), r1))
                }
                mstore8(wp, packed)
                mstore8(add(wp, 1), shr(8, packed))
                mstore8(add(wp, 2), shr(16, packed))
                wp := add(wp, 3)
            }
        }
    }
}

contract DecodeFloorTest is Test {
    PythonSigner pythonSigner = new PythonSigner();

    function testDecodeFloor() public {
        (bytes memory cTildeB, bytes memory zB, bytes memory hB) = pythonSigner.sign(
            "pythonref",
            "0x1111222233334444111122223333444411112222333344441111222233334444",
            "NIST",
            Constants.SEED_POSTQUANTUM_STR
        );
        cTildeB; // silence
        uint256 g0;

        // ---- reference outputs ----
        uint256[][] memory zRef = unpackZ(zB);
        (bool okRef, uint256[][] memory hRef) = unpackH(hB);
        require(okRef, "ref h");

        // ---- fast unpackZ + fused norm check ----
        g0 = gasleft();
        (uint256[] memory zFlat, bool normOk) = unpackZFast(zB);
        console.log("unpackZFast_with_norm:", g0 - gasleft());
        assertTrue(normOk, "norm");
        for (uint256 i = 0; i < 4; i++) {
            for (uint256 j = 0; j < 256; j++) {
                assertEq(zFlat[i * 256 + j], zRef[i][j], "z mismatch");
            }
        }

        // ---- fast unpackH -> bitmasks ----
        g0 = gasleft();
        (bool ok2, uint256[4] memory masks, uint256 weight) = unpackHFast(hB);
        console.log("unpackHFast_with_weight:", g0 - gasleft());
        assertTrue(ok2, "h fast");
        assertLe(weight, 80, "omega");
        for (uint256 i = 0; i < 4; i++) {
            uint256 m = 0;
            for (uint256 j = 0; j < 256; j++) {
                if (hRef[i][j] == 1) m |= (uint256(1) << j);
            }
            assertEq(masks[i], m, "mask mismatch");
        }

        // ---- fused useHint + w1Encode ----
        // build an r input: reuse zRef values as stand-in coefficients mod q (values in range)
        bytes memory refHint = useHintDilithium(hRef, zRef);
        g0 = gasleft();
        bytes memory fastHint = useHintFast(masks, zRef);
        console.log("useHintFast_w1encode:", g0 - gasleft());
        assertEq(keccak256(fastHint), keccak256(refHint), "hint bytes mismatch");

        // repo reference costs at same memory level, for scale
        g0 = gasleft();
        uint256[][] memory zRef2 = unpackZ(zB);
        console.log("unpackZ_repo_again:", g0 - gasleft());
        zRef2;
    }
}
