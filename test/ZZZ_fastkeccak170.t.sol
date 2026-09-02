// SPDX-License-Identifier: MIT
// FILE: test/ZZZ_fastkeccak170.t.sol
// Deployability (EIP-170, real CREATE -- no vm.etch), correctness (vs reference
// f1600 + SHAKE256 KATs) and gas benchmarks for ZZZ_FastKeccak170.sol.
// Same correctness checks as ZZZ_fastkeccak.t.sol; KAT values were computed
// offline with pythonref/myenv (pycryptodome SHAKE256).
pragma solidity ^0.8.25;

import "forge-std/Test.sol";
import {f1600} from "./vendor/ZKNOX_shake.sol";
import {deployF1600_170, f1600Fast170, shake256Fast170, _F1600_CODE_170} from "./ZZZ_FastKeccak170.sol";
import {shake256Batch170} from "../src/FastKeccak170.sol";

/// @dev thin wrapper so shake256Batch170's requires can be observed with
///      vm.expectRevert (which needs an external call boundary).
contract BatchProbe {
    function callBatch(bytes memory input, uint256 outLen, address helper)
        external
        view
        returns (bytes memory)
    {
        return shake256Batch170(input, outLen, helper);
    }
}

/// @dev a fake helper returning the wrong number of bytes for the batch
///      protocol (135, not 136) -- must be caught by the fail-closed check.
contract BadBatchHelper {
    fallback() external {
        assembly {
            return(0, 135)
        }
    }
}

contract ZZZFastKeccak170Test is Test {
    address internal helper;

    function setUp() public {
        // real bytecode deployment: minimal init stub + CREATE (no vm.etch)
        helper = deployF1600_170();
    }

    // ------------------------------------------------------------------
    // Deployability proof: runtime <= EIP-170 limit, real CREATE, code intact
    // ------------------------------------------------------------------
    function test_deployable_underEIP170_viaRealCreate() public {
        // 1. the runtime respects the EIP-170 deployed-code size limit
        assertLe(_F1600_CODE_170.length, 24576, "runtime exceeds EIP-170 limit");

        // 2. setUp deployed it with plain CREATE; the on-chain account has code
        assertTrue(helper != address(0), "helper not deployed");
        assertEq(helper.code.length, _F1600_CODE_170.length, "extcodesize mismatch");
        assertEq(keccak256(helper.code), keccak256(_F1600_CODE_170), "deployed code mismatch");

        // 3. the init-code wrapper is re-runnable: a fresh CREATE lands the
        //    identical runtime at a new address
        address h2 = deployF1600_170();
        assertTrue(h2 != address(0) && h2 != helper, "second CREATE failed");
        assertEq(h2.code.length, _F1600_CODE_170.length, "extcodesize mismatch (2nd)");
        assertEq(keccak256(h2.code), keccak256(_F1600_CODE_170), "deployed code mismatch (2nd)");

        console.log("helper runtime size (bytes):", _F1600_CODE_170.length);
        console.log("EIP-170 headroom (bytes):", 24576 - _F1600_CODE_170.length);
    }

    // ------------------------------------------------------------------
    // Correctness: f1600Fast170 vs the repo's reference f1600
    // (same check as ZZZ_fastkeccak.t.sol: 5 pseudorandom states x 3 chained)
    // ------------------------------------------------------------------
    function test_f1600Fast170_matches_reference() public view {
        for (uint256 s = 0; s < 5; s++) {
            uint64[25] memory a;
            uint256[25] memory b;
            for (uint256 i = 0; i < 25; i++) {
                uint256 v = uint256(keccak256(abi.encode("f1600 state", s, i)));
                a[i] = uint64(v);
                b[i] = v & 0xffffffffffffffff;
            }
            // 3 successive permutations per state
            for (uint256 r = 0; r < 3; r++) {
                a = f1600(a);
                f1600Fast170(b, helper);
                for (uint256 i = 0; i < 25; i++) {
                    assertEq(b[i], uint256(a[i]), "lane mismatch vs reference f1600");
                    assertLt(b[i], 1 << 64, "lane not 64-bit clean");
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // SHAKE256 KATs (expected values computed offline with pycryptodome)
    // ------------------------------------------------------------------
    function test_shake256Fast170_empty_KAT() public view {
        // SHAKE256(""), 32 bytes
        bytes memory out = shake256Fast170(hex"", 32, helper);
        assertEq(out, hex"46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f");
    }

    function test_shake256Fast170_singleBlock_KAT() public view {
        // 32-byte input (bytes 0x00..0x1f), 32-byte output
        bytes memory input = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            input[i] = bytes1(uint8(i));
        }
        bytes memory out = shake256Fast170(input, 32, helper);
        assertEq(out, hex"69f07c8840ce80024db30939882c3d5bbc9c98b3e31e4513ebd2ca9b4503cdd3");
    }

    function test_shake256Fast170_multiBlock_KAT() public view {
        // 200-byte input (crosses the 136-byte absorb rate boundary),
        // 300-byte output (crosses the squeeze rate boundary: 3 squeeze blocks).
        bytes memory input = new bytes(200);
        for (uint256 i = 0; i < 200; i++) {
            input[i] = bytes1(uint8(i));
        }
        bytes memory out32 = shake256Fast170(input, 32, helper);
        assertEq(out32, hex"4ee1ca03272b05d3bfb1e1c79a967f823b9fc5e4bb3987b1ba9e9cb5afb07a5e");

        bytes memory out300 = shake256Fast170(input, 300, helper);
        assertEq(
            out300,
            hex"4ee1ca03272b05d3bfb1e1c79a967f823b9fc5e4bb3987b1ba9e9cb5afb07a5e"
            hex"e3a07fbd457a94364964a841e7f466e5a022e21ab7f673c18ba98cdb1d5aecfa"
            hex"e62268b068f1e4bf9ee9853bcce08dcd491c629aa218b60d3d453e83a554eb17"
            hex"6cfef9729e99ff3a8127c49e3c3cf19ad26018ed796fedce98c5f867ec2bacbd"
            hex"b8012cc52b76e6d24a80fa3692d02a03634b34b2fb336232e4c027dca0cc4bd0"
            hex"3a01f1cec8c35ad0e51687fad4e18ebc23a75851d466979d59db7391b61702a7"
            hex"fc85a1162bdbaaeab699499162f551da8b0c839f88ff96b8dd79015606526ab7"
            hex"8fd1c101660de85653340f3d1dac2a22bcf1a2bef88d742de9006c2d5b6d8acd"
            hex"586b6bee76f85cccbf94e387c53c23e716c670c4db23c67901358ae64f3f0cce"
            hex"dfa05b29e84e1a11a635bfe7"
        );
    }

    function test_shake256Fast170_mldsaShape_KAT() public view {
        // 832-byte input = 6 full absorb blocks + padded final block (7 permutations),
        // matching the ML-DSA-44 w1 final hash shape.
        bytes memory input = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            input[i] = bytes1(uint8(i));
        }
        bytes memory out = shake256Fast170(input, 32, helper);
        assertEq(out, hex"04f3dc57d6f0bdcecbf785322919a3f7bbca7ec1ec394f59d94cf53871f2aa39");
    }

    // ------------------------------------------------------------------
    // Gas (call 1 pays EIP-2929 cold account access; calls 2-4 are warm)
    // ------------------------------------------------------------------
    function test_gas_f1600Fast170() public view {
        address h = helper; // one SLOAD outside the measured windows
        uint256[25] memory st;
        for (uint256 i = 0; i < 25; i++) {
            st[i] = uint256(keccak256(abi.encode("gas state", i))) & 0xffffffffffffffff;
        }
        uint256 g0 = gasleft();
        f1600Fast170(st, h);
        uint256 g1 = gasleft();
        f1600Fast170(st, h);
        uint256 g2 = gasleft();
        f1600Fast170(st, h);
        uint256 g3 = gasleft();
        f1600Fast170(st, h);
        uint256 g4 = gasleft();
        console.log("f1600Fast170 call 1 gas (cold):", g0 - g1);
        console.log("f1600Fast170 call 2 gas (warm):", g1 - g2);
        console.log("f1600Fast170 call 3 gas (warm):", g2 - g3);
        console.log("f1600Fast170 call 4 gas (warm):", g3 - g4);
        // vm.etch'ed oversized variant (ZZZ_FastKeccak.sol) measures 44750 warm
        console.log("warm delta vs 44750 baseline (call 3):", int256(g2 - g3) - int256(44750));
        // keep result alive
        require(st[0] != 0, "unused");
    }

    function test_gas_shake256Fast170() public view {
        address h = helper;
        bytes memory in32 = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            in32[i] = bytes1(uint8(i));
        }
        bytes memory in832 = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            in832[i] = bytes1(uint8(i));
        }
        // warm the helper account so the shape numbers below are all-warm
        bytes memory warmup = shake256Fast170(hex"", 32, h);

        uint256 g0 = gasleft();
        bytes memory o1 = shake256Fast170(in32, 32, h);
        uint256 g1 = gasleft();
        console.log("shake256Fast170(32B in, 32B out) gas:", g0 - g1);

        uint256 g2 = gasleft();
        bytes memory o2 = shake256Fast170(in832, 32, h);
        uint256 g3 = gasleft();
        console.log("shake256Fast170(832B in, 32B out) gas [7 permutations]:", g2 - g3);

        require(warmup.length == 32 && o1.length == 32 && o2.length == 32, "unused");
    }

    // ------------------------------------------------------------------
    // Batched one-call SHAKE256 entry point (shake256Batch170): the same
    // KATs as the lane-level sponge, equivalence across block boundaries,
    // fail-closed marshaling, and gas.
    // ------------------------------------------------------------------
    function test_shake256Batch170_KATs() public view {
        // SHAKE256(""), 32 bytes
        assertEq(
            shake256Batch170(hex"", 32, helper),
            hex"46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
        );
        // 32-byte input (bytes 0x00..0x1f), 32-byte output
        bytes memory in32 = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            in32[i] = bytes1(uint8(i));
        }
        assertEq(
            shake256Batch170(in32, 32, helper),
            hex"69f07c8840ce80024db30939882c3d5bbc9c98b3e31e4513ebd2ca9b4503cdd3"
        );
        // 200-byte input (crosses the absorb rate boundary), full 136-byte
        // (one-squeeze-block) output = prefix of the multi-block KAT above
        bytes memory in200 = new bytes(200);
        for (uint256 i = 0; i < 200; i++) {
            in200[i] = bytes1(uint8(i));
        }
        assertEq(
            shake256Batch170(in200, 136, helper),
            hex"4ee1ca03272b05d3bfb1e1c79a967f823b9fc5e4bb3987b1ba9e9cb5afb07a5e"
            hex"e3a07fbd457a94364964a841e7f466e5a022e21ab7f673c18ba98cdb1d5aecfa"
            hex"e62268b068f1e4bf9ee9853bcce08dcd491c629aa218b60d3d453e83a554eb17"
            hex"6cfef9729e99ff3a8127c49e3c3cf19ad26018ed796fedce98c5f867ec2bacbd"
            hex"b8012cc52b76e6d2"
        );
        // 832-byte ML-DSA w1 final-hash shape (7 permutations in one call)
        bytes memory in832 = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            in832[i] = bytes1(uint8(i));
        }
        assertEq(
            shake256Batch170(in832, 32, helper),
            hex"04f3dc57d6f0bdcecbf785322919a3f7bbca7ec1ec394f59d94cf53871f2aa39"
        );
    }

    /// batch path == lane-level sponge on every absorb-block-boundary shape,
    /// including the ML-DSA mu (98) / final-hash (832) preimage lengths and
    /// the lengths bracketing the reserved raw-protocol length 800.
    function test_shake256Batch170_equivalence_sweep() public view {
        uint16[16] memory lens =
            [0, 1, 17, 66, 98, 135, 136, 137, 271, 272, 559, 798, 799, 801, 832, 1360];
        for (uint256 k = 0; k < lens.length; k++) {
            uint256 n = lens[k];
            bytes memory input = new bytes(n);
            for (uint256 i = 0; i < n; i++) {
                input[i] = keccak256(abi.encode("sweep", k, i / 32))[i % 32];
            }
            assertEq(
                shake256Batch170(input, 64, helper),
                shake256Fast170(input, 64, helper),
                "batch != lane sponge (64B out)"
            );
            assertEq(
                shake256Batch170(input, 136, helper),
                shake256Fast170(input, 136, helper),
                "batch != lane sponge (136B out)"
            );
        }
    }

    function test_shake256Batch170_guards_and_failClosed() public {
        BatchProbe probe = new BatchProbe();
        // the reserved raw-protocol length is rejected...
        bytes memory in800 = new bytes(800);
        vm.expectRevert(bytes("f1600-170: length 800 unsupported"));
        probe.callBatch(in800, 32, helper);
        // ...and every neighbouring length is fine (checked in the sweep test)
        // outLen beyond one squeeze block is rejected
        vm.expectRevert(bytes("f1600-170: outLen > rate"));
        probe.callBatch(hex"", 137, helper);
        // a helper answering with the wrong returndata size fails closed
        address bad = address(new BadBatchHelper());
        vm.expectRevert(bytes("f1600-170: helper call failed"));
        probe.callBatch(hex"deadbeef", 32, bad);
        // a codeless helper fails closed
        vm.expectRevert(bytes("f1600-170: helper call failed"));
        probe.callBatch(hex"deadbeef", 32, address(0xDEAD));
    }

    function test_gas_shake256Batch170() public view {
        address h = helper;
        bytes memory in98 = new bytes(98); // the mu preimage shape (66 + 32B msg)
        for (uint256 i = 0; i < 98; i++) {
            in98[i] = bytes1(uint8(i));
        }
        bytes memory in832 = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            in832[i] = bytes1(uint8(i));
        }
        require(shake256Batch170(hex"", 32, h).length == 32, "warmup");

        {
            uint256 g0 = gasleft();
            bytes memory o1 = shake256Batch170(in98, 64, h);
            uint256 g1 = gasleft();
            console.log("shake256Batch170(98B in, 64B out) gas [1 permutation]:", g0 - g1);
            uint256 g2 = gasleft();
            bytes memory o2 = shake256Fast170(in98, 64, h);
            uint256 g3 = gasleft();
            console.log("   vs lane sponge, same shape:", g2 - g3);
            assertEq(keccak256(o1), keccak256(o2), "98B mismatch");
        }
        {
            uint256 g0 = gasleft();
            bytes memory o1 = shake256Batch170(in832, 32, h);
            uint256 g1 = gasleft();
            console.log("shake256Batch170(832B in, 32B out) gas [7 permutations]:", g0 - g1);
            uint256 g2 = gasleft();
            bytes memory o2 = shake256Fast170(in832, 32, h);
            uint256 g3 = gasleft();
            console.log("   vs lane sponge, same shape:", g2 - g3);
            assertEq(keccak256(o1), keccak256(o2), "832B mismatch");
        }
    }
}
