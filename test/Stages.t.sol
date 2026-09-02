// SPDX-License-Identifier: MIT
// FILE: test/Stages.t.sol
//
// Per-kernel gas profile of the reference verifier's stages, measured on
// synthetic canonical inputs (every kernel here is data-independent in gas
// except sampleInBall's rejection loop and the norm test, which are noted).
// Purpose: attribute the end-to-end verify() cost to individual stages so
// that gas regressions can be localised. Bracket methodology: gasleft()
// around each isolated block.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {_F1600_AT, _F1600_CODE, shake256Fast} from "./ZZZ_FastKeccak.sol";
import {unpackHFast} from "./ZZZ_decode.t.sol";
import {useHintFast2} from "./ZZZ_decode2.t.sol";
import {nttFwV3, packCoeffs, reducePacked, nttFwTable} from "./ZZZ_NttVariants.sol";
import {nttInvV3, iunpackCoeffs, nttInvTable} from "./ZZZ_InvNtt.sol";
import {
    unpackZStrict,
    sampleInBallE2E,
    packFromFlat,
    macCompactLazy,
    macSubCT1Lazy,
    E2E_Q
} from "./ZZZ_E2ERef.sol";

contract StagesTest is Test {
    uint256 sink;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
    }

    /// canonical z encoding: every coefficient 0 (v == gamma1 == 131072), which
    /// passes the strict norm test; 2304 bytes.
    function _zBytes() internal pure returns (bytes memory z) {
        z = new bytes(2304);
        // 18-bit fields, value 131072 = 0x20000 -> bit pattern per 4 coeffs in
        // 9 bytes; all 1024 coefficients (4 polynomials), else the trailing
        // zero fields fail the strict norm check.
        for (uint256 blk = 0; blk < 1024; ++blk) {
            uint256 base = (blk / 4) * 9;
            uint256 sh = (blk % 4) * 18;
            uint256 v = 131072;
            for (uint256 b = 0; b < 18; ++b) {
                if ((v >> b) & 1 == 1) {
                    uint256 bit = sh + b;
                    z[base + bit / 8] = bytes1(uint8(z[base + bit / 8]) | uint8(1 << (bit % 8)));
                }
            }
        }
    }

    function _canonPoly(uint256 seed) internal pure returns (uint256[] memory a) {
        a = new uint256[](256);
        for (uint256 i = 0; i < 256; ++i) {
            a[i] = uint256(keccak256(abi.encodePacked(seed, i))) % E2E_Q;
        }
    }

    // ------------------------------------------------------------- decode
    function test_stage_10_decode() public {
        uint256 g0;
        bytes memory z = _zBytes();
        g0 = gasleft();
        (uint256[] memory zf, bool ok) = unpackZStrict(z);
        console.log("unpackZStrict(2304B):", g0 - gasleft());
        require(ok && zf.length == 1024);

        bytes memory h = new bytes(84);
        h[80] = bytes1(uint8(0)); // 0 hints in every poly -> valid, weight 0
        g0 = gasleft();
        (bool hok,, uint256 w) = unpackHFast(h);
        console.log("unpackHFast(84B):", g0 - gasleft());
        require(hok && w == 0);
    }

    // ---------------------------------------------------------------- NTT
    function test_stage_20_ntt() public {
        uint256 g0;
        uint256[] memory prof = new uint256[](10);
        uint256[] memory a = _canonPoly(1);

        g0 = gasleft();
        uint256[] memory p = packCoeffs(a);
        console.log("packCoeffs(256):", g0 - gasleft());

        g0 = gasleft();
        uint256[] memory hat = nttFwV3(p, prof, nttFwTable());
        console.log("nttFwV3:", g0 - gasleft());

        g0 = gasleft();
        nttInvV3(hat, prof, nttInvTable());
        console.log("nttInvV3:", g0 - gasleft());

        g0 = gasleft();
        uint256[] memory back = iunpackCoeffs(hat);
        console.log("iunpackCoeffs:", g0 - gasleft());

        uint256[] memory flat = new uint256[](1024);
        g0 = gasleft();
        uint256[] memory pf = packFromFlat(flat, 256);
        console.log("packFromFlat:", g0 - gasleft());
        sink = back[0] + pf[0];
    }

    // ------------------------------------------------------------- matvec
    function test_stage_30_matvec() public {
        uint256 g0;
        uint256[] memory prof = new uint256[](10);
        uint256[] memory zHat = nttFwV3(packCoeffs(_canonPoly(2)), prof, nttFwTable());
        uint256[] memory cHat = nttFwV3(packCoeffs(_canonPoly(3)), prof, nttFwTable());
        // a fake pk row in the compact 8x32-bit/word layout
        uint256[] memory arow = new uint256[](32);
        for (uint256 i = 0; i < 32; ++i) {
            uint256 wrd;
            for (uint256 s = 0; s < 8; ++s) {
                wrd |= (uint256(keccak256(abi.encodePacked(i, s))) % E2E_Q) << (32 * s);
            }
            arow[i] = wrd;
        }
        uint256 aPtr;
        assembly ("memory-safe") {
            aPtr := add(arow, 32)
        }

        uint256[] memory acc = new uint256[](64);
        g0 = gasleft();
        macCompactLazy(acc, aPtr, zHat);
        console.log("macCompactLazy(1 of 16):", g0 - gasleft());

        g0 = gasleft();
        macSubCT1Lazy(acc, cHat, aPtr);
        console.log("macSubCT1Lazy(1 of 4):", g0 - gasleft());

        g0 = gasleft();
        reducePacked(acc);
        console.log("reducePacked(1 of 4):", g0 - gasleft());
        sink = acc[0];
    }

    // ----------------------------------------------------------- UseHint
    function test_stage_40_usehint() public {
        uint256 g0;
        uint256[4] memory hMasks;
        uint256[][] memory r = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            r[i] = _canonPoly(10 + i);
        }
        g0 = gasleft();
        bytes memory w1 = useHintFast2(hMasks, r);
        console.log("useHintFast2(+w1Encode):", g0 - gasleft());
        require(w1.length == 768);
    }

    // ------------------------------------------------------------- SHAKE
    function test_stage_50_shake() public {
        uint256 g0;
        bytes memory muIn = new bytes(66);
        g0 = gasleft();
        bytes memory mu = shake256Fast(muIn, 64);
        console.log("shake256(66B->64B) [1 perm]:", g0 - gasleft());

        bytes memory fin = new bytes(832);
        g0 = gasleft();
        bytes memory ct = shake256Fast(fin, 32);
        console.log("shake256(832B->32B) [7 perms]:", g0 - gasleft());

        bytes memory c32 = new bytes(32);
        g0 = gasleft();
        bytes memory sq = shake256Fast(c32, 136);
        console.log("shake256(32B->136B) [1 perm]:", g0 - gasleft());
        sink = uint256(uint8(mu[0])) + uint256(uint8(ct[0])) + uint256(uint8(sq[0]));
    }

    function test_stage_51_sampleinball() public {
        uint256 g0;
        g0 = gasleft();
        uint256[] memory c = sampleInBallE2E(bytes32(uint256(0x1234)));
        console.log("sampleInBallE2E (incl 1 perm):", g0 - gasleft());
        sink = c[0];
    }

    // --------------------------------------------------- memory high-water
    function test_stage_60_memory_highwater() public {
        uint256 g0 = gasleft();
        uint256[] memory prof = new uint256[](10);
        uint256[][] memory zHat = new uint256[][](4);
        for (uint256 j = 0; j < 4; ++j) {
            zHat[j] = nttFwV3(packCoeffs(_canonPoly(j)), prof, nttFwTable());
        }
        uint256 fp;
        assembly ("memory-safe") {
            fp := mload(0x40)
        }
        console.log("free_mem_after_4_ntts:", fp);
        console.log("gas_for_4_ntts_incl_alloc:", g0 - gasleft());
        sink = zHat[0][0];
    }
}
