// SPDX-License-Identifier: MIT
// Calibrate raw EVM op costs under this toolchain (solc 0.8.30, opt 10000, osaka).
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";

contract CalibTest is Test {
    function testCalib() public view {
        uint256 g0;
        uint256 acc = 0;
        bytes32 sink;

        // 1. empty-ish loop, 1024 iters
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 1024) { i := add(i, 1) } { acc := add(acc, 1) }
        }
        console.log("loop1024_add:", g0 - gasleft());

        // 2. loop with mload + add
        uint256[] memory arr = new uint256[](1024);
        g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(arr, 32)
            for { let i := 0 } lt(i, 1024) { i := add(i, 1) } {
                acc := add(acc, mload(add(p, shl(5, i))))
            }
        }
        console.log("loop1024_mload_add:", g0 - gasleft());

        // 3. loop with 1 mulmod
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 1024) { i := add(i, 1) } {
                acc := mulmod(acc, 5, 8380417)
            }
        }
        console.log("loop1024_mulmod:", g0 - gasleft());

        // 4. loop with ~10 ALU ops
        g0 = gasleft();
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 1024) { i := add(i, 1) } {
                let a := add(acc, i)
                let b := shr(3, a)
                let c := and(a, 7)
                let d := or(shl(8, b), c)
                let e := mul(d, 3)
                acc := xor(acc, e)
            }
        }
        console.log("loop1024_10ops:", g0 - gasleft());

        // 5. straight-line 64 mulmods, no loop
        g0 = gasleft();
        assembly ("memory-safe") {
            let x := acc
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417) x := mulmod(x, 3, 8380417)
            acc := x
        }
        console.log("straightline_64_mulmod:", g0 - gasleft());

        // 6. keccak256 opcode over 1024 bytes (for scale)
        bytes memory blob = new bytes(1024);
        g0 = gasleft();
        assembly ("memory-safe") {
            sink := keccak256(add(blob, 32), 1024)
        }
        console.log("keccak256_1024B:", g0 - gasleft());

        require(acc != 1 || sink != 0);
    }
}
