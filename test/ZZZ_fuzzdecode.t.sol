// SPDX-License-Identifier: MIT
// FFI fuzz harness: multi-vector equivalence of iter-2 decode kernels vs repo reference.
// Closes the single-vector gap in the fixed-vector equivalence checks of
// test/ZZZ_decode2.t.sol, which exercise the kernels on one FFI-signed vector.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {PythonSigner} from "./vendor/ZKNOX_PythonSigner.sol";
import {unpackH, unpackZ} from "./vendor/ZKNOX_dilithium_core.sol";
import {useHintDilithium} from "./vendor/ZKNOX_hint.sol";
import {unpackHFast} from "./ZZZ_decode.t.sol";
import {unpackZFast2, useHintFast2} from "./ZZZ_decode2.t.sol";

contract FuzzDecodeTest is Test {
    PythonSigner pythonSigner = new PythonSigner();

    bytes16 constant HEX = "0123456789abcdef";

    function toHex(bytes32 v) internal pure returns (string memory s) {
        bytes memory b = new bytes(64);
        for (uint256 i = 0; i < 32; i++) {
            b[2 * i] = HEX[uint8(v[i]) >> 4];
            b[2 * i + 1] = HEX[uint8(v[i]) & 0x0f];
        }
        return string(b);
    }

    function testFuzzDecodeKernels() public {
        uint256 vectors = 10;
        for (uint256 n = 0; n < vectors; n++) {
            bytes32 seed = keccak256(abi.encode("fuzz-seed", n));
            bytes32 msgWord = keccak256(abi.encode("fuzz-msg", n));
            string memory seedStr = toHex(seed);
            string memory dataStr = string(abi.encodePacked("0x", toHex(msgWord)));

            (, bytes memory zB, bytes memory hB) = pythonSigner.sign("pythonref", dataStr, "NIST", seedStr);

            // --- unpackZ: fast2 vs repo ---
            uint256[][] memory zRef = unpackZ(zB);
            (uint256[] memory zFlat, bool normOk) = unpackZFast2(zB);
            assertTrue(normOk, "norm should pass on honest sig");
            for (uint256 i = 0; i < 4; i++) {
                for (uint256 j = 0; j < 256; j++) {
                    assertEq(zFlat[i * 256 + j], zRef[i][j], "z mismatch");
                }
            }

            // --- unpackH: fast vs repo ---
            (bool okRef, uint256[][] memory hRef) = unpackH(hB);
            (bool okFast, uint256[4] memory masks, uint256 weight) = unpackHFast(hB);
            assertEq(okFast, okRef, "h validity mismatch");
            assertLe(weight, 80, "omega");
            for (uint256 i = 0; i < 4; i++) {
                uint256 m = 0;
                for (uint256 j = 0; j < 256; j++) {
                    if (hRef[i][j] == 1) m |= (uint256(1) << j);
                }
                assertEq(masks[i], m, "h mask mismatch");
            }

            // --- useHint+w1Encode: fast2 vs repo ---
            // NOTE: unpackZ encodes z=0 as q (not 0). useHint's domain is canonical [0,q)
            // (in the real pipeline it consumes mod-q-reduced w'); canonicalize first.
            // Feeding raw q exposes a LATENT BUG in the repo's useHintDilithium (outputs
            // 44, an invalid w1 value, at rv==q) — see testUseHintBoundaryQ below.
            for (uint256 i = 0; i < 4; i++) {
                for (uint256 j = 0; j < 256; j++) {
                    if (zRef[i][j] == 8380417) zRef[i][j] = 0;
                }
            }
            bytes memory refHint = useHintDilithium(hRef, zRef);
            bytes memory fastHint = useHintFast2(masks, zRef);
            assertEq(keccak256(fastHint), keccak256(refHint), "w1 bytes mismatch");
        }
        console.log("fuzz vectors passed:", vectors);
    }

    // Boundary regression: rv == q (produced by unpackZ for z=0 coefficients).
    // FIPS: use_hint(h, q mod q = 0) = 0. useHintFast2 returns 0 (correct).
    // The repo's useHintDilithium returns 44 — an out-of-range w1 value — because its
    // "edge case impossible here" branch comment is false for rv = q. Latent in the repo
    // (its pipeline never feeds q), but a reuse hazard. This test documents both facts.
    function testUseHintBoundaryQ() public pure {
        uint256[][] memory r = new uint256[][](4);
        uint256[][] memory h0 = new uint256[][](4);
        for (uint256 i = 0; i < 4; i++) {
            r[i] = new uint256[](256);
            h0[i] = new uint256[](256);
            r[i][0] = 8380417; // q
        }
        uint256[4] memory noMasks;
        bytes memory fast = useHintFast2(noMasks, r);
        // FIPS-correct: coefficient 0 encodes 0
        assertEq(uint8(fast[0]) & 0x3F, 0, "fast2 must give FIPS-correct 0 at rv=q");
        bytes memory repo = useHintDilithium(h0, r);
        // documents the repo's latent out-of-domain behavior (44 = 0b101100)
        assertEq(uint8(repo[0]) & 0x3F, 44, "repo latent bug expectation changed?");
    }

    function testFuzzDecodeRejectsMalformedH() public {
        // malformed h encodings must be rejected identically by both decoders
        (, , bytes memory hB) = pythonSigner.sign(
            "pythonref",
            "0x1111222233334444111122223333444411112222333344441111222233334444",
            "NIST",
            "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe"
        );
        for (uint256 k = 0; k < 6; k++) {
            bytes memory bad = bytes(hB);
            if (k == 0) bad[80] = 0xFF; // count > OMEGA
            if (k == 1) { bad[0] = 0x05; bad[1] = 0x05; } // non-monotone duplicate
            if (k == 2) { bad[0] = 0x09; bad[1] = 0x03; } // descending
            if (k == 3) bad[79] = 0x01; // nonzero padding past counts
            if (k == 4) { bad[83] = bad[82]; bad[82] = 0x00; } // counts decreasing
            if (k == 5) bad[81] = 0x00; // count below previous cumulative
            (bool okRef,) = unpackH(bad);
            (bool okFast,,) = unpackHFast(bad);
            assertEq(okFast, okRef, "reject-mismatch on malformed h");
        }
    }
}
