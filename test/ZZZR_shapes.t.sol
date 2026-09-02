// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// ZZZR auditor scratch: grounds the ESTIMATED lines of the verify gas budget:
//  - mu-shape SHAKE (98B in -> 64B out), claimed ~67k
//  - SampleInBall sponge+rejection+poly build, claimed ~73k
//  - powers table with 192-bit modulus P = 2^192-237, 511 entries, claimed ~22k
//  - inner products with realistic operand encodings (24-bit packed A, 8B s fields,
//    4B w'/f fields, dual-accumulator signed z), vs the clean 12.1k ipLazyMul
//  - unpackZFast / useHintFast at FRESH memory (decode test measured them at high mem)
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {shake256Fast} from "./ZZZ_FastKeccak.sol";
import {unpackZFast, useHintFast} from "./ZZZ_decode.t.sol";

uint256 constant QQ = 8380417;
uint256 constant P192 = 2 ** 192 - 237;

contract ZZZRShapesTest is Test {
    // ------------------------------------------------------------------
    // SHAKE shapes claimed but not measured in ZZZ_fastkeccak.t.sol
    // ------------------------------------------------------------------
    function test_mu_shape() public view {
        // mu = SHAKE256(tr(64B) || 0x00 0x00 || M(32B), 64) => 98B in, 64B out, 1 perm
        bytes memory inp = new bytes(98);
        for (uint256 i = 0; i < 98; i++) {
            inp[i] = bytes1(uint8(i + 1));
        }
        uint256 g0 = gasleft();
        bytes memory mu = shake256Fast(inp, 64);
        uint256 g = g0 - gasleft();
        console.log("mu shape (98B in, 64B out) gas:", g);
        require(mu.length == 64, "len");
    }

    function test_sampleinball_glue() public view {
        // c = SampleInBall(cTilde): absorb 32B, squeeze 136B stream, 8 sign bytes,
        // tau=39 rejection-sampled positions, build the full 256-word poly
        // and the 39-entry packed sparse list.
        bytes memory ct = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            ct[i] = bytes1(uint8(0xA0 + i));
        }
        uint256 g0 = gasleft();
        bytes memory stream = shake256Fast(ct, 136);
        uint256[] memory c = new uint256[](256);
        uint256[] memory pairs = new uint256[](39);
        uint256 signs;
        for (uint256 k = 0; k < 8; k++) {
            signs |= uint256(uint8(stream[k])) << (8 * k);
        }
        uint256 pos = 8;
        uint256 sIdx = 0;
        uint256 rejections = 0;
        for (uint256 i = 217; i < 256; i++) {
            uint256 j = uint8(stream[pos]);
            pos++;
            while (j > i) {
                j = uint8(stream[pos]);
                pos++;
                rejections++;
            }
            c[i] = c[j];
            uint256 sbit = (signs >> sIdx) & 1;
            sIdx++;
            c[j] = sbit == 1 ? QQ - 1 : 1;
            pairs[sIdx - 1] = j | (sbit << 8);
        }
        uint256 g = g0 - gasleft();
        console.log("SampleInBall total (1 perm + glue + poly + sparse list) gas:", g);
        console.log("  stream bytes consumed:", pos);
        console.log("  rejections:", rejections);
        require(c.length == 256 && pairs.length == 39, "unused");
    }

    // ------------------------------------------------------------------
    // mod-P (192-bit) powers table, 511 entries — claimed ~22k
    // ------------------------------------------------------------------
    function test_powers_table_P192() public view {
        uint256 alpha = uint256(keccak256("zzzr.alpha")) >> 65; // 191-bit alpha
        uint256[] memory pow = new uint256[](511);
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let p := 0xffffffffffffffffffffffffffffffffffffffffffffff13 // 2^192-237
            let d := add(pow, 32)
            mstore(d, 1)
            let prev := 1
            for { let i := 1 } lt(i, 511) { i := add(i, 1) } {
                prev := mulmod(prev, alpha, p)
                mstore(add(d, shl(5, i)), prev)
            }
        }
        uint256 g = g0 - gasleft();
        console.log("powers table mod P192, 511 entries gas:", g);
        require(pow[510] != 0, "unused");
    }

    // ------------------------------------------------------------------
    // Inner products with REAL operand encodings (all 256 terms, plain-mul lazy
    // accumulation mod P192, single final mod). Baseline clean version measured
    // 12,065 in K4 (both operands 1 word/coeff, q-sized).
    // ------------------------------------------------------------------
    function _powArr() internal pure returns (uint256[] memory pow) {
        pow = new uint256[](256);
        uint256 alpha = uint256(keccak256("zzzr.alpha2")) >> 65;
        pow[0] = 1;
        for (uint256 i = 1; i < 256; i++) {
            pow[i] = mulmod(pow[i - 1], alpha, P192);
        }
    }

    /// A-style: coefficients 24-bit, packed 3B/coeff in a byte buffer (EXTCODECOPY image)
    function test_ip_A_3bytepacked() public view {
        uint256[] memory pow = _powArr();
        bytes memory apacked = new bytes(768 + 32); // +32 slack for the tail mload
        for (uint256 i = 0; i < 768; i++) {
            apacked[i] = bytes1(uint8(uint256(keccak256(abi.encode("a", i / 3))) >> (8 * (i % 3))));
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let src := add(apacked, 32)
            let pw := add(pow, 32)
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                // 3-byte little-window read: top 3 bytes of the word at byte offset 3i
                let coeff := shr(232, mload(add(src, mul(i, 3))))
                acc := add(acc, mul(coeff, mload(add(pw, shl(5, i)))))
            }
            acc := mod(acc, 0xffffffffffffffffffffffffffffffffffffffffffffff13)
        }
        uint256 g = g0 - gasleft();
        console.log("IP 256 terms, 24-bit/3B-packed coeff x 192-bit power gas:", g);
        require(acc != 0, "unused");
    }

    /// s-style: 8B offset-encoded fields with in-loop 52-bit masking (bound enforcement)
    function test_ip_s_8bytefields() public view {
        uint256[] memory pow = _powArr();
        bytes memory sbuf = new bytes(2048 + 32);
        for (uint256 i = 0; i < 2048; i++) {
            sbuf[i] = bytes1(uint8(uint256(keccak256(abi.encode("s", i / 8))) >> (8 * (i % 8))));
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let src := add(sbuf, 32)
            let pw := add(pow, 32)
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                let v := and(shr(192, mload(add(src, shl(3, i)))), 0xfffffffffffff) // 52-bit mask
                acc := add(acc, mul(v, mload(add(pw, shl(5, i)))))
            }
            acc := mod(acc, 0xffffffffffffffffffffffffffffffffffffffffffffff13)
        }
        uint256 g = g0 - gasleft();
        console.log("IP 256 terms, 8B-field masked-52-bit x 192-bit power gas:", g);
        require(acc != 0, "unused");
    }

    /// w'/f-style: 4B aligned fields
    function test_ip_w_4bytefields() public view {
        uint256[] memory pow = _powArr();
        bytes memory wbuf = new bytes(1024 + 32);
        for (uint256 i = 0; i < 1024; i++) {
            wbuf[i] = bytes1(uint8(uint256(keccak256(abi.encode("w", i / 4))) >> (8 * (i % 4))));
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let src := add(wbuf, 32)
            let pw := add(pow, 32)
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                let v := shr(224, mload(add(src, shl(2, i))))
                acc := add(acc, mul(v, mload(add(pw, shl(5, i)))))
            }
            acc := mod(acc, 0xffffffffffffffffffffffffffffffffffffffffffffff13)
        }
        uint256 g = g0 - gasleft();
        console.log("IP 256 terms, 4B-field x 192-bit power gas:", g);
        require(acc != 0, "unused");
    }

    /// z-style: canonical-mod-q words, centered lift via dual accumulators
    function test_ip_z_dualacc() public view {
        uint256[] memory pow = _powArr();
        uint256[] memory z = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            z[i] = uint256(keccak256(abi.encode("z", i))) % QQ;
        }
        uint256 accP;
        uint256 accN;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let zp := add(z, 32)
            let pw := add(pow, 32)
            let half := 4190208 // q/2
            for { let i := 0 } lt(i, 256) { i := add(i, 1) } {
                let v := mload(add(zp, shl(5, i)))
                let a := mload(add(pw, shl(5, i)))
                switch gt(v, half)
                case 1 { accN := add(accN, mul(sub(8380417, v), a)) }
                default { accP := add(accP, mul(v, a)) }
            }
            let p := 0xffffffffffffffffffffffffffffffffffffffffffffff13
            accP := addmod(mod(accP, p), sub(p, mod(accN, p)), p)
        }
        uint256 g = g0 - gasleft();
        console.log("IP 256 terms, signed-z dual-accumulator gas:", g);
        require(accP != 0 || accN == 0, "unused");
    }

    // ------------------------------------------------------------------
    // Decode kernels at FRESH memory (ZZZ_decode measured them after FFI + refs,
    // i.e. at elevated memory). Same code, synthetic input, gas only.
    // ------------------------------------------------------------------
    function test_unpackZFast_fresh() public view {
        bytes memory zB = new bytes(2304);
        for (uint256 i = 0; i < 2304; i++) {
            zB[i] = bytes1(uint8(i * 7 + 1));
        }
        uint256 g0 = gasleft();
        (uint256[] memory zf, bool ok) = unpackZFast(zB);
        uint256 g = g0 - gasleft();
        console.log("unpackZFast at fresh memory gas:", g);
        console.log("  (norm result, data-dependent, ignore):", ok);
        require(zf.length == 1024, "unused");
    }

    function test_useHintFast_fresh() public view {
        uint256[4] memory masks =
            [uint256(keccak256("m0")), uint256(keccak256("m1")), uint256(keccak256("m2")), uint256(keccak256("m3"))];
        uint256[][] memory r = new uint256[][](4);
        for (uint256 i = 0; i < 4; i++) {
            r[i] = new uint256[](256);
            for (uint256 j = 0; j < 256; j++) {
                r[i][j] = uint256(keccak256(abi.encode(i, j))) % QQ;
            }
        }
        uint256 g0 = gasleft();
        bytes memory h = useHintFast(masks, r);
        uint256 g = g0 - gasleft();
        console.log("useHintFast+w1encode at fresh-ish memory gas:", g);
        require(h.length == 768, "unused");
    }
}
