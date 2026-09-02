// SPDX-License-Identifier: MIT
// FILE: test/ZZZR_shapes2.t.sol
// EVM cost-model calibration: UNROLLED x8 inner-product probes over different
// operand encodings (3-byte packed, 8-byte masked, 4-byte lanes, clean
// word-per-coefficient), all against the same wide-modulus power table, so
// the gas deltas between the probes are attributable to operand encoding
// only. Also includes a tight-assembly SampleInBall glue measurement.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {shake256Fast} from "./ZZZ_FastKeccak.sol";

uint256 constant QQ = 8380417;
uint256 constant P192 = 2 ** 192 - 237;

contract ZZZRShapes2Test is Test {
    function _powArr(uint256 n) internal pure returns (uint256[] memory pow) {
        pow = new uint256[](n);
        uint256 alpha = uint256(keccak256("zzzr.alpha2")) >> 65;
        pow[0] = 1;
        for (uint256 i = 1; i < n; i++) {
            pow[i] = mulmod(pow[i - 1], alpha, P192);
        }
    }

    // Unrolled x8 powers table with a 192-bit modulus (mulmod at width), 512 entries.
    function test_powers_table_P192_unrolled() public view {
        uint256 alpha = uint256(keccak256("zzzr.alpha")) >> 65;
        uint256[] memory pow = new uint256[](512);
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let p := add(pow, 0x20)
            let end := add(p, 16384)
            let acc := 1
            for {} lt(p, end) { p := add(p, 0x100) } {
                mstore(p, acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0x20), acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0x40), acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0x60), acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0x80), acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0xa0), acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0xc0), acc)
                acc := mulmod(acc, alpha, P192)
                mstore(add(p, 0xe0), acc)
                acc := mulmod(acc, alpha, P192)
            }
        }
        uint256 g = g0 - gasleft();
        console.log("powers table mod P192, 512 entries, unrolled x8 gas:", g);
        require(pow[511] != 0, "unused");
    }

    /// 24-bit coefficients packed 3 bytes/coeff, unrolled x8, plain-mul lazy acc mod P192.
    function test_ip_A_3bytepacked_unrolled() public view {
        uint256[] memory pow = _powArr(256);
        bytes memory apacked = new bytes(768 + 32);
        for (uint256 i = 0; i < 768; i++) {
            apacked[i] = bytes1(uint8(uint256(keccak256(abi.encode("a", i / 3))) >> (8 * (i % 3))));
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let src := add(apacked, 32)
            let pw := add(pow, 32)
            let end := add(src, 768)
            for {} lt(src, end) {
                src := add(src, 24)
                pw := add(pw, 0x100)
            } {
                acc := add(acc, mul(shr(232, mload(src)), mload(pw)))
                acc := add(acc, mul(shr(232, mload(add(src, 3))), mload(add(pw, 0x20))))
                acc := add(acc, mul(shr(232, mload(add(src, 6))), mload(add(pw, 0x40))))
                acc := add(acc, mul(shr(232, mload(add(src, 9))), mload(add(pw, 0x60))))
                acc := add(acc, mul(shr(232, mload(add(src, 12))), mload(add(pw, 0x80))))
                acc := add(acc, mul(shr(232, mload(add(src, 15))), mload(add(pw, 0xa0))))
                acc := add(acc, mul(shr(232, mload(add(src, 18))), mload(add(pw, 0xc0))))
                acc := add(acc, mul(shr(232, mload(add(src, 21))), mload(add(pw, 0xe0))))
            }
            acc := mod(acc, P192)
        }
        uint256 g = g0 - gasleft();
        console.log("IP256 A-style 3B-packed x P192-power, unrolled x8 gas:", g);
        require(acc != 0, "unused");
    }

    /// 8-byte fields with a 52-bit mask enforced in-loop, unrolled x8.
    function test_ip_s_8bytefields_unrolled() public view {
        uint256[] memory pow = _powArr(256);
        bytes memory sbuf = new bytes(2048 + 32);
        for (uint256 i = 0; i < 2048; i++) {
            sbuf[i] = bytes1(uint8(uint256(keccak256(abi.encode("s", i / 8))) >> (8 * (i % 8))));
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let src := add(sbuf, 32)
            let pw := add(pow, 32)
            let end := add(src, 2048)
            let M := 0xfffffffffffff
            for {} lt(src, end) {
                src := add(src, 64)
                pw := add(pw, 0x100)
            } {
                acc := add(acc, mul(and(shr(192, mload(src)), M), mload(pw)))
                acc := add(acc, mul(and(shr(192, mload(add(src, 8))), M), mload(add(pw, 0x20))))
                acc := add(acc, mul(and(shr(192, mload(add(src, 16))), M), mload(add(pw, 0x40))))
                acc := add(acc, mul(and(shr(192, mload(add(src, 24))), M), mload(add(pw, 0x60))))
                acc := add(acc, mul(and(shr(192, mload(add(src, 32))), M), mload(add(pw, 0x80))))
                acc := add(acc, mul(and(shr(192, mload(add(src, 40))), M), mload(add(pw, 0xa0))))
                acc := add(acc, mul(and(shr(192, mload(add(src, 48))), M), mload(add(pw, 0xc0))))
                acc := add(acc, mul(and(shr(192, mload(add(src, 56))), M), mload(add(pw, 0xe0))))
            }
            acc := mod(acc, P192)
        }
        uint256 g = g0 - gasleft();
        console.log("IP256 s-style 8B-masked x P192-power, unrolled x8 gas:", g);
        require(acc != 0, "unused");
    }

    /// 4-byte fields, 8 lanes per word, plain mul.
    function test_ip_w_4bytefields_unrolled() public view {
        uint256[] memory pow = _powArr(256);
        bytes memory wbuf = new bytes(1024);
        for (uint256 i = 0; i < 1024; i++) {
            wbuf[i] = bytes1(uint8(uint256(keccak256(abi.encode("w", i / 4))) >> (8 * (i % 4))));
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let src := add(wbuf, 32)
            let pw := add(pow, 32)
            let end := add(src, 1024)
            let M := 0xffffffff
            for {} lt(src, end) {
                src := add(src, 0x20)
                pw := add(pw, 0x100)
            } {
                let w := mload(src)
                acc := add(acc, mul(shr(224, w), mload(pw)))
                acc := add(acc, mul(and(shr(192, w), M), mload(add(pw, 0x20))))
                acc := add(acc, mul(and(shr(160, w), M), mload(add(pw, 0x40))))
                acc := add(acc, mul(and(shr(128, w), M), mload(add(pw, 0x60))))
                acc := add(acc, mul(and(shr(96, w), M), mload(add(pw, 0x80))))
                acc := add(acc, mul(and(shr(64, w), M), mload(add(pw, 0xa0))))
                acc := add(acc, mul(and(shr(32, w), M), mload(add(pw, 0xc0))))
                acc := add(acc, mul(and(w, M), mload(add(pw, 0xe0))))
            }
            acc := mod(acc, P192)
        }
        uint256 g = g0 - gasleft();
        console.log("IP256 w-style 4B-lanes x P192-power, unrolled x8 gas:", g);
        require(acc != 0, "unused");
    }

    /// Baseline: clean 1-word/coeff mod-q values x P192 powers, plain mul —
    /// the encoding-free shape the packed probes above are compared against.
    function test_ip_clean_unrolled_P192() public view {
        uint256[] memory pow = _powArr(256);
        uint256[] memory v = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            v[i] = uint256(keccak256(abi.encode("v", i))) % QQ;
        }
        uint256 acc;
        uint256 g0 = gasleft();
        assembly ("memory-safe") {
            let vp := add(v, 0x20)
            let pw := add(pow, 0x20)
            let end := add(vp, 8192)
            for {} lt(vp, end) {
                vp := add(vp, 0x100)
                pw := add(pw, 0x100)
            } {
                acc := add(acc, mul(mload(vp), mload(pw)))
                acc := add(acc, mul(mload(add(vp, 0x20)), mload(add(pw, 0x20))))
                acc := add(acc, mul(mload(add(vp, 0x40)), mload(add(pw, 0x40))))
                acc := add(acc, mul(mload(add(vp, 0x60)), mload(add(pw, 0x60))))
                acc := add(acc, mul(mload(add(vp, 0x80)), mload(add(pw, 0x80))))
                acc := add(acc, mul(mload(add(vp, 0xa0)), mload(add(pw, 0xa0))))
                acc := add(acc, mul(mload(add(vp, 0xc0)), mload(add(pw, 0xc0))))
                acc := add(acc, mul(mload(add(vp, 0xe0)), mload(add(pw, 0xe0))))
            }
            acc := mod(acc, P192)
        }
        uint256 g = g0 - gasleft();
        console.log("IP256 clean word-coeff x P192-power, unrolled x8 gas:", g);
        require(acc != 0, "unused");
    }

    // Tight-assembly SampleInBall glue: shake(32B -> 136B stream) + signs + tau=39
    // rejection loop + full c poly + sparse pair list, all in asm.
    function test_sampleinball_tight() public view {
        bytes memory ct = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            ct[i] = bytes1(uint8(0xA0 + i));
        }
        uint256[] memory c = new uint256[](256);
        uint256[] memory pairs = new uint256[](39);
        uint256 g0 = gasleft();
        bytes memory stream = shake256Fast(ct, 136);
        uint256 gShake = g0 - gasleft();
        assembly ("memory-safe") {
            let sp := add(stream, 32)
            let signs := shr(192, mload(sp)) // first 8 bytes as 64 sign bits
            let bp := add(sp, 8)
            let cData := add(c, 32)
            let prData := add(pairs, 32)
            let sIdx := 0
            for { let i := 217 } lt(i, 256) { i := add(i, 1) } {
                let j := byte(0, mload(bp))
                bp := add(bp, 1)
                for {} gt(j, i) {} {
                    j := byte(0, mload(bp))
                    bp := add(bp, 1)
                }
                let cj := add(cData, shl(5, j))
                mstore(add(cData, shl(5, i)), mload(cj))
                let sbit := and(shr(sIdx, signs), 1)
                mstore(cj, add(1, mul(sbit, 8380415))) // 1 or q-1
                mstore(add(prData, shl(5, sIdx)), or(j, shl(8, sbit)))
                sIdx := add(sIdx, 1)
            }
        }
        uint256 g = g0 - gasleft();
        console.log("SampleInBall tight: shake(32B->136B) part gas:", gShake);
        console.log("SampleInBall tight: total (shake + asm glue + poly + pairs) gas:", g);
        require(c.length == 256 && pairs.length == 39, "unused");
    }
}
