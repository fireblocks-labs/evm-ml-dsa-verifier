// SPDX-License-Identifier: MIT
// Benchmark Optimism's LibKeccak permutation vs repo f1600 vs our f1600Fast, same toolchain.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {LibKeccak} from "./ZZZ_LibKeccak_OP.sol";
import {f1600} from "./vendor/ZKNOX_shake.sol";
import {f1600Fast} from "./ZZZ_FastKeccak.sol";

contract OpKeccakBenchTest is Test {
    using LibKeccak for LibKeccak.StateMatrix;

    function testOpKeccakGasAndCrossCheck() public view {
        // pseudorandom initial state
        LibKeccak.StateMatrix memory op;
        uint64[25] memory refState;
        uint256[25] memory fastState;
        for (uint256 i = 0; i < 25; i++) {
            uint64 lane = uint64(uint256(keccak256(abi.encode("lane", i))));
            op.state[i] = lane;
            refState[i] = lane;
            fastState[i] = lane;
        }

        uint256 g0 = gasleft();
        LibKeccak.permutation(op);
        console.log("libkeccak_op_permutation:", g0 - gasleft());

        g0 = gasleft();
        LibKeccak.permutation(op);
        console.log("libkeccak_op_permutation_2:", g0 - gasleft());

        // cross-check all three agree after one permutation from same start
        LibKeccak.StateMatrix memory op2;
        for (uint256 i = 0; i < 25; i++) {
            op2.state[i] = uint64(uint256(keccak256(abi.encode("lane", i))));
        }
        LibKeccak.permutation(op2);
        refState = f1600(refState);
        f1600Fast(fastState);
        for (uint256 i = 0; i < 25; i++) {
            assertEq(uint256(op2.state[i]), uint256(refState[i]), "op vs ref");
            assertEq(fastState[i] & 0xFFFFFFFFFFFFFFFF, uint256(refState[i]), "fast vs ref");
        }
    }
}
