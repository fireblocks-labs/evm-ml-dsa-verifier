// SPDX-License-Identifier: MIT
// FILE: test/FUZZ_Shake.t.sol
//
// FIPS-202 SHAKE256 assurance for the XOF the ML-DSA-44 EVM verifiers depend
// on: the test-harness one-shot test/ZZZ_FastKeccak.sol shake256Fast and its
// EIP-170-deployable twin test/ZZZ_FastKeccak170.sol shake256Fast170 (the
// same construction as the shipped src/FastKeccak170.sol; the shipped
// MLDSA44Verifier binds the deployed helper by code hash).
//
// Corpus (built by tools/fixtures/shake_build.py; upstream URLs + SHA-256 in
// tools/fixtures/acvp_data/shake256.json under `_provenance`):
//   OFFICIAL — 251 NIST ACVP SHAKE-256 known-answer vectors, from
//     https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/
//       json-files/SHAKE-256-FIPS202/internalProjection.json  (237 AFT)
//       json-files/SHAKE-256-1.0/internalProjection.json      (AFT + VOT)
//     restricted to the byte-aligned cases (the EVM XOF is byte-oriented;
//     1646 bit-length cases are not expressible and were skipped).  Inputs up
//     to 8126 bytes, outputs up to 512 bytes.  Every md is additionally
//     re-derived with hashlib's FIPS-202 SHAKE-256 before emission, so ACVP
//     and the oracle agree on all 251.
//   RANDOM — 405 hashlib-oracle cases: the 19 x 15 grid of input lengths
//     {0,1,2,31,32,33,63,64,135,136,137,271,272,273,407,408,409,544,1000} x
//     output lengths {1,31,32,33,64,135,136,137,271,272,273,1000,1088,1500,
//     3000} (both sides straddle the 136-byte rate and the 3rd/4th block
//     boundary, include the empty input and outputs past 1000 bytes), plus 120
//     uniformly random (inLen <= 4096, outLen <= 2048) pairs.
//
// Plus three structural properties:
//   * squeeze continuation: a short output is a prefix of a longer one
//   * absorb-in-chunks: the vendored streaming sponge oracle in
//     test/vendor/ZKNOX_shake.sol (shakeInit / shakeUpdate x n / shakeDigest)
//     must agree bit-exactly with the one-shot shake256Fast, for splits at
//     1 / 135 / 136 / 137 / len-1
//   * the deployable shake256Fast170 twin must agree bit-exactly
//
// REGENERATE FIXTURES:
//   pythonref/myenv/bin/python tools/fixtures/shake_build.py --build
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {_F1600_AT, _F1600_CODE, shake256Fast} from "./ZZZ_FastKeccak.sol";
import {deployF1600_170, shake256Fast170} from "./ZZZ_FastKeccak170.sol";
import {CtxShake, shakeInit, shakeUpdate, shakeDigest} from "./vendor/ZKNOX_shake.sol";

contract FuzzShakeTest is Test {
    struct ShakeShard {
        bytes[] inputs;
        uint256[] outLens;
        bytes[] digests;
        string[] labels;
    }

    /// in-repo shard builder (see tools/fixtures/README_shards.md); vm.ffi
    /// runs with cwd = the repository root, so the path is repo-relative.
    string constant FX = "tools/fixtures/shake_build.py";

    address helper170;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        helper170 = deployF1600_170();
    }

    /// The builder prints the requested shard as hex on stdout (vm.ffi decodes
    /// hex automatically) and caches it under test/fixtures/, so the corpus is
    /// generated once and every later run is a plain file read.
    function _read(string memory name) internal returns (bytes memory out) {
        string[] memory c = new string[](3);
        c[0] = "pythonref/myenv/bin/python";
        c[1] = FX;
        c[2] = name;
        out = vm.ffi(c);
        require(out.length > 64, "empty fixture shard");
    }

    function _shard(string memory prefix, uint256 k) internal returns (ShakeShard memory s) {
        s = abi.decode(_read(string.concat(prefix, "_", vm.toString(k), ".hex")), (ShakeShard));
    }

    function _run(string memory prefix, uint256 k) internal {
        ShakeShard memory s = _shard(prefix, k);
        uint256 maxOut;
        uint256 maxIn;
        for (uint256 i = 0; i < s.inputs.length; ++i) {
            bytes memory got = shake256Fast(s.inputs[i], s.outLens[i]);
            assertEq(got.length, s.outLens[i], s.labels[i]);
            if (keccak256(got) != keccak256(s.digests[i])) {
                console.log("SHAKE MISMATCH:", s.labels[i]);
                console.log("  in / out bytes:", s.inputs[i].length, s.outLens[i]);
            }
            assertEq(keccak256(got), keccak256(s.digests[i]), s.labels[i]);
            if (s.outLens[i] > maxOut) maxOut = s.outLens[i];
            if (s.inputs[i].length > maxIn) maxIn = s.inputs[i].length;
        }
        console.log("shake shard cases / max input / max output:", s.inputs.length, maxIn, maxOut);
    }

    // ------------------------------------- official ACVP SHAKE-256 KATs (251)

    function test_shake_acvp_shard0() public {
        _run("sk", 0);
    }

    function test_shake_acvp_shard1() public {
        _run("sk", 1);
    }

    function test_shake_acvp_shard2() public {
        _run("sk", 2);
    }

    function test_shake_acvp_shard3() public {
        _run("sk", 3);
    }

    // ----------------------- randomized (inLen, outLen) battery, 405 vectors

    function test_shake_random_shard0() public {
        _run("sr", 0);
    }

    function test_shake_random_shard1() public {
        _run("sr", 1);
    }

    function test_shake_random_shard2() public {
        _run("sr", 2);
    }

    // ---------------------------------------------- squeeze continuation

    /// a shorter squeeze must be a byte-exact prefix of a longer one, across
    /// several permutations of the squeeze phase (32 -> 3000 bytes)
    function test_shake_squeeze_prefix_consistency() public view {
        uint256[8] memory lens = [uint256(1), 32, 135, 136, 137, 272, 1000, 3000];
        for (uint256 t = 0; t < 6; ++t) {
            bytes memory input = t == 0 ? bytes("") : abi.encodePacked(keccak256(abi.encode("sq", t)), t);
            bytes memory full = shake256Fast(input, 3000);
            for (uint256 j = 0; j < lens.length; ++j) {
                bytes memory part = shake256Fast(input, lens[j]);
                for (uint256 b = 0; b < lens[j]; ++b) {
                    assertEq(part[b], full[b], "squeeze prefix");
                }
            }
        }
        console.log("squeeze-continuation: 6 inputs x 8 output lengths (up to 3000 B) consistent");
    }

    // ------------------------------------------------- absorb in chunks

    /// The vendored streaming sponge of test/vendor/ZKNOX_shake.sol fed in n
    /// chunks must produce exactly the same stream as the one-shot
    /// shake256Fast on the concatenation.  Splits are placed on and around the
    /// 136-byte rate boundary.
    function test_shake_absorb_in_chunks_matches_oneshot() public view {
        uint256[6] memory inLens = [uint256(0), 1, 136, 137, 200, 300];
        uint256 checks;
        for (uint256 t = 0; t < inLens.length; ++t) {
            uint256 n = inLens[t];
            bytes memory input = new bytes(n);
            for (uint256 i = 0; i < n; ++i) {
                input[i] = bytes1(uint8(uint256(keccak256(abi.encode("chunk", t, i)))));
            }
            bytes memory want = shake256Fast(input, 136);

            // one-shot through the streaming API
            CtxShake memory ctx = shakeInit();
            ctx = shakeUpdate(ctx, input);
            assertEq(keccak256(shakeDigest(ctx, 136)), keccak256(want), "streaming one-shot");
            ++checks;

            // every split point in {1, 135, 136, 137, n-1} that applies
            uint256[5] memory cuts = [uint256(1), 135, 136, 137, n == 0 ? 0 : n - 1];
            for (uint256 c = 0; c < cuts.length; ++c) {
                uint256 cut = cuts[c];
                if (cut == 0 || cut >= n) continue;
                bytes memory a = new bytes(cut);
                bytes memory b = new bytes(n - cut);
                for (uint256 i = 0; i < cut; ++i) {
                    a[i] = input[i];
                }
                for (uint256 i = cut; i < n; ++i) {
                    b[i - cut] = input[i];
                }
                CtxShake memory c2 = shakeInit();
                c2 = shakeUpdate(c2, a);
                c2 = shakeUpdate(c2, b);
                assertEq(keccak256(shakeDigest(c2, 136)), keccak256(want), "chunked absorb");
                ++checks;
            }
        }
        console.log("absorb-in-chunks equivalences checked:", checks);
    }

    // --------------------------------------- deployable twin (EIP-170 variant)

    /// shake256Fast170 (helper contract deployed by CREATE, called with
    /// STATICCALL) must be bit-identical to the etched shake256Fast on the
    /// official ACVP corpus and on rate-crossing lengths.
    function test_shake170_matches_official_and_fast() public {
        ShakeShard memory s = _shard("sk", 0);
        for (uint256 i = 0; i < s.inputs.length; ++i) {
            bytes memory got = shake256Fast170(s.inputs[i], s.outLens[i], helper170);
            assertEq(keccak256(got), keccak256(s.digests[i]), s.labels[i]);
        }
        uint256[7] memory lens = [uint256(1), 32, 135, 136, 137, 272, 1000];
        for (uint256 j = 0; j < lens.length; ++j) {
            bytes memory input = abi.encodePacked(keccak256(abi.encode("f170", j)), lens[j]);
            assertEq(
                keccak256(shake256Fast170(input, lens[j], helper170)),
                keccak256(shake256Fast(input, lens[j])),
                "shake256Fast170 vs shake256Fast"
            );
        }
        console.log("shake256Fast170 agrees on ACVP shard 0 + 7 rate-crossing lengths:", s.inputs.length);
    }
}
