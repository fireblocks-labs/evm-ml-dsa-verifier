// SPDX-License-Identifier: MIT
// FILE: test/ZZZR_size.t.sol
// EIP-170 size probes: is a single deployable contract containing the measured
// components (fully-unrolled f1600, packed NTT, decode asm) within the
// EIP-170 24,576-byte runtime limit at optimizer runs=10000?
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {f1600Fast, shake256Fast} from "./ZZZ_FastKeccak.sol";
import {nttFwV3, packCoeffs, unpackCoeffs, macPackedLazy, reducePacked, nttFwTable} from "./ZZZ_NttVariants.sol";
import {unpackZFast, unpackHFast, useHintFast} from "./ZZZ_decode.t.sol";

contract KeccakOnlyProbe {
    function run(bytes calldata inp, uint256 n) external pure returns (bytes memory) {
        return shake256Fast(inp, n);
    }
}

contract NttOnlyProbe {
    function run(uint256[] calldata a) external view returns (uint256) {
        uint256[] memory prof = new uint256[](16);
        uint256[] memory w = nttFwV3(packCoeffs(a), prof, nttFwTable());
        return unpackCoeffs(w)[0];
    }

    function mac(uint256[] memory c, uint256[] memory a, uint256[] memory b) external pure returns (uint256) {
        macPackedLazy(c, a, b);
        reducePacked(c);
        return c[0];
    }
}

contract AllComponentsProbe {
    function pShake(bytes calldata inp, uint256 n) external pure returns (bytes memory) {
        return shake256Fast(inp, n);
    }

    function pF1600(uint256[25] memory st) external pure returns (uint256) {
        f1600Fast(st);
        return st[0];
    }

    function pNtt(uint256[] calldata a) external view returns (uint256) {
        uint256[] memory prof = new uint256[](16);
        uint256[] memory w = nttFwV3(packCoeffs(a), prof, nttFwTable());
        return unpackCoeffs(w)[0];
    }

    function pMac(uint256[] memory c, uint256[] memory a, uint256[] memory b) external pure returns (uint256) {
        macPackedLazy(c, a, b);
        reducePacked(c);
        return c[0];
    }

    function pDecode(bytes memory z, bytes memory h) external pure returns (uint256) {
        (uint256[] memory zf, bool ok) = unpackZFast(z);
        (bool ok2, uint256[4] memory masks, uint256 wgt) = unpackHFast(h);
        return zf[0] + (ok ? 1 : 0) + (ok2 ? 1 : 0) + masks[0] + wgt;
    }

    function pHint(uint256[4] memory m, uint256[][] memory r) external pure returns (bytes memory) {
        return useHintFast(m, r);
    }
}

contract ZZZRSizeTest is Test {
    function testComponentContractSizes() public {
        KeccakOnlyProbe k = new KeccakOnlyProbe();
        NttOnlyProbe n = new NttOnlyProbe();
        AllComponentsProbe a = new AllComponentsProbe();
        console.log("EIP-170 runtime limit bytes: 24576");
        console.log("KeccakOnlyProbe (shake256Fast incl. unrolled f1600):", address(k).code.length);
        console.log("NttOnlyProbe (V3 NTT + packed MAC):", address(n).code.length);
        console.log("AllComponentsProbe (shake+f1600+NTT+MAC+decode+hint):", address(a).code.length);
    }
}
