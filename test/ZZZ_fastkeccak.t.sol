// SPDX-License-Identifier: MIT
// FILE: test/ZZZ_fastkeccak.t.sol
// Correctness (vs reference f1600 + SHAKE256 KATs) and gas benchmarks for ZZZ_FastKeccak.sol.
// All KAT values below were computed offline with pythonref/myenv (pycryptodome SHAKE256).
pragma solidity ^0.8.25;

import "forge-std/Test.sol";
import {f1600} from "./vendor/ZKNOX_shake.sol";
import {f1600Fast, shake256Fast} from "./ZZZ_FastKeccak.sol";

contract ZZZFastKeccakTest is Test {
    // ------------------------------------------------------------------
    // Correctness: f1600Fast vs the repo's reference f1600
    // ------------------------------------------------------------------
    function test_f1600Fast_matches_reference() public pure {
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
                f1600Fast(b);
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
    function test_shake256Fast_empty_KAT() public pure {
        // SHAKE256(""), 32 bytes
        bytes memory out = shake256Fast(hex"", 32);
        assertEq(out, hex"46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f");
    }

    function test_shake256Fast_singleBlock_KAT() public pure {
        // 32-byte input (bytes 0x00..0x1f), 32-byte output
        bytes memory input = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            input[i] = bytes1(uint8(i));
        }
        bytes memory out = shake256Fast(input, 32);
        assertEq(out, hex"69f07c8840ce80024db30939882c3d5bbc9c98b3e31e4513ebd2ca9b4503cdd3");
    }

    function test_shake256Fast_multiBlock_KAT() public pure {
        // 200-byte input (crosses the 136-byte absorb rate boundary),
        // 300-byte output (crosses the squeeze rate boundary: 3 squeeze blocks).
        bytes memory input = new bytes(200);
        for (uint256 i = 0; i < 200; i++) {
            input[i] = bytes1(uint8(i));
        }
        bytes memory out32 = shake256Fast(input, 32);
        assertEq(out32, hex"4ee1ca03272b05d3bfb1e1c79a967f823b9fc5e4bb3987b1ba9e9cb5afb07a5e");

        bytes memory out300 = shake256Fast(input, 300);
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

    function test_shake256Fast_mldsaShape_KAT() public pure {
        // 832-byte input = 6 full absorb blocks + padded final block (7 permutations),
        // matching the ML-DSA-44 w1 final hash shape.
        bytes memory input = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            input[i] = bytes1(uint8(i));
        }
        bytes memory out = shake256Fast(input, 32);
        assertEq(out, hex"04f3dc57d6f0bdcecbf785322919a3f7bbca7ec1ec394f59d94cf53871f2aa39");
    }

    // ------------------------------------------------------------------
    // Gas
    // ------------------------------------------------------------------
    function test_gas_f1600Fast() public view {
        uint256[25] memory st;
        for (uint256 i = 0; i < 25; i++) {
            st[i] = uint256(keccak256(abi.encode("gas state", i))) & 0xffffffffffffffff;
        }
        uint256 g0 = gasleft();
        f1600Fast(st);
        uint256 g1 = gasleft();
        f1600Fast(st);
        uint256 g2 = gasleft();
        f1600Fast(st);
        uint256 g3 = gasleft();
        f1600Fast(st);
        uint256 g4 = gasleft();
        console.log("f1600Fast call 1 gas:", g0 - g1);
        console.log("f1600Fast call 2 gas:", g1 - g2);
        console.log("f1600Fast call 3 gas:", g2 - g3);
        console.log("f1600Fast call 4 gas:", g3 - g4);
        // keep result alive
        require(st[0] != 0, "unused");
    }

    function test_gas_f1600_reference() public view {
        uint64[25] memory st;
        for (uint256 i = 0; i < 25; i++) {
            st[i] = uint64(uint256(keccak256(abi.encode("gas state", i))));
        }
        uint256 g0 = gasleft();
        st = f1600(st);
        uint256 g1 = gasleft();
        console.log("reference f1600 gas:", g0 - g1);
        require(st[0] != 0, "unused");
    }

    function test_gas_shake256Fast() public view {
        bytes memory in32 = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            in32[i] = bytes1(uint8(i));
        }
        bytes memory in832 = new bytes(832);
        for (uint256 i = 0; i < 832; i++) {
            in832[i] = bytes1(uint8(i));
        }
        uint256 g0 = gasleft();
        bytes memory o1 = shake256Fast(in32, 32);
        uint256 g1 = gasleft();
        console.log("shake256Fast(32B in, 32B out) gas:", g0 - g1);

        uint256 g2 = gasleft();
        bytes memory o2 = shake256Fast(in832, 32);
        uint256 g3 = gasleft();
        console.log("shake256Fast(832B in, 32B out) gas [7 permutations]:", g2 - g3);

        require(o1.length == 32 && o2.length == 32, "unused");
    }
}
