// SPDX-License-Identifier: MIT
// FILE: test/FV2_AcvpKeyGen.t.sol
//
// CORPUS EXTENSION — the NIST ACVP **ML-DSA-keyGen** vectors.
//
// test/ACVP_MLDSA44.t.sol covers the ACVP sigVer and sigGen corpora.  It does
// not cover keyGen, so without this file the off-chain public-key transform
// (tr ‖ t1hat = NTT(2^d·t1) ‖ Ahat = ExpandA(rho), packed into the pk data
// contract) would only ever be exercised on the 15 distinct public keys that
// appear in sigVer.  keyGen adds 25 further official ML-DSA-44 key pairs,
// each of which is re-signed off-chain and must verify through BOTH in-tree
// subjects: the reference verifier test/ZZZ_E2ERef.sol and the shipped
// src/MLDSA44Verifier.sol.
//
// EXACT ACVP COUNTS for ML-DSA-44 (measured from the upstream
// internalProjection.json files; SHA-256 digests are recorded in
// formal/acvp/data/provenance.json and tools/fixtures/acvp_data/):
//
//   corpus   ML-DSA-44 cases   external/pure   external/preHash   internal
//   sigVer          60              15                15             30
//   sigGen         120              30                30             60
//   keyGen          25               —                 —              —
//
//   exercised on chain without this file : 90  (15 SV + 30 SG + 45 preHash replays)
//   exercised on chain with    this file : 115 (+25 keyGen)
//   NOT applicable                       : 90  internal-interface cases
//
// The 90 internal-interface cases drive ML-DSA.Sign_internal / Verify_internal,
// i.e. they hand the implementation a pre-formatted M′.  Both verifiers here
// implement the EXTERNAL interface only and construct M′ = 0x00‖0x00‖M
// themselves — deliberately, because letting a caller supply M′ is exactly the
// domain-separation hazard FIPS 204 §5.2 warns about.  Those vectors are
// therefore *not applicable*, not skipped; there is no API to feed them to.
//
// Fixture: formal/acvp/keygen_build.py (verifies the cached ACVP corpus
// against its recorded SHA-256 on every run, and checks every case against
// the dilithium_py oracle before emitting).
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {ZZZ_E2ERef, E2E_PK_SIZE} from "./ZZZ_E2ERef.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

contract FV2AcvpKeyGenTest is Test {
    string constant PYBIN = "pythonref/myenv/bin/python";
    string constant BUILDER = "formal/acvp/keygen_build.py";

    /// field order matches the tuple emitted by formal/acvp/keygen_build.py
    struct KG {
        bytes[] pkBlobs; // 20,544-byte pk payloads
        bytes[] msgs;
        bytes[] sigs;
        string[] labels;
    }

    ZZZ_E2ERef refVerifier;
    MLDSA44Verifier shipped;
    uint256 _pkNonce;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        refVerifier = new ZZZ_E2ERef();
        shipped = new MLDSA44Verifier(deployF1600_170());
    }

    /// The reference verifier's pk cache is a RAW data contract (code == blob,
    /// no prefix), so it is placed with vm.etch exactly as
    /// test/ACVP_MLDSA44.t.sol does — a blob whose first byte is 0xEF could
    /// not be CREATE-deployed (EIP-3541; see that file's
    /// test_acvp_eip3541_pk_prefix).
    function _placeRefPk(bytes memory blob) internal returns (address a) {
        a = address(uint160(uint256(keccak256(abi.encodePacked("fv2.kg.pk", ++_pkNonce)))));
        vm.etch(a, blob);
    }

    /// The shipped verifier's pk data contract is 0x00 || payload; the 0x00
    /// prefix makes it EIP-3541-deployable for every key, so a plain CREATE
    /// always works.
    function _deployShippedPk(bytes memory blob) internal returns (address ptr) {
        bytes memory data = bytes.concat(hex"00", blob);
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "pk data contract deploy failed");
    }

    /// 25 cases in 5 shards of 5, decoded straight from the builder's stdout
    /// (the builder caches each shard under test/fixtures/kg_acvp_<k>.hex).
    function _load(uint256 shard) internal returns (KG memory s) {
        string[] memory c = new string[](3);
        c[0] = PYBIN;
        c[1] = BUILDER;
        c[2] = string.concat("kg_", vm.toString(shard));
        // the builder emits abi_encode(["(bytes[],...)"], [tuple]) i.e. a single
        // TUPLE argument, so the blob carries a leading offset word; decoding it
        // as a struct (exactly as test/ACVP_MLDSA44.t.sol does) consumes that.
        s = abi.decode(vm.ffi(c), (KG));
    }

    uint256 constant N_SHARDS = 5;

    /// every official ML-DSA-44 keyGen key pair, verified by BOTH subjects
    function _runShard(uint256 shard) internal {
        KG memory s = _load(shard);
        assertEq(s.pkBlobs.length, 5, "shard case count");
        for (uint256 i = 0; i < s.pkBlobs.length; ++i) {
            assertEq(s.pkBlobs[i].length, E2E_PK_SIZE, "pk blob size");
            address refPk = _placeRefPk(s.pkBlobs[i]);
            address shipPk = _deployShippedPk(s.pkBlobs[i]);
            bool gotRef = refVerifier.verify(refPk, s.msgs[i], s.sigs[i]);
            bool gotShip = shipped.verify(shipPk, s.msgs[i], s.sigs[i]);
            if (!gotRef || !gotShip) {
                console.log("ACVP keyGen mismatch:", s.labels[i]);
                console.log("  reference / shipped:", gotRef, gotShip);
            }
            assertTrue(gotRef, s.labels[i]);
            assertTrue(gotShip, s.labels[i]);
        }
    }

    function test_FV2_acvp_keygen_shard0() public { _runShard(0); }
    function test_FV2_acvp_keygen_shard1() public { _runShard(1); }
    function test_FV2_acvp_keygen_shard2() public { _runShard(2); }
    function test_FV2_acvp_keygen_shard3() public { _runShard(3); }
    function test_FV2_acvp_keygen_shard4() public { _runShard(4); }

    /// negative control: a one-bit flip in each official signature must be
    /// rejected by both verifiers, on official NIST key material
    function test_FV2_acvp_keygen_bitflip_rejected() public {
        KG memory s = _load(0);
        for (uint256 i = 0; i < s.sigs.length; ++i) {
            bytes memory bad = new bytes(s.sigs[i].length);
            for (uint256 k = 0; k < bad.length; ++k) {
                bad[k] = s.sigs[i][k];
            }
            // flip a bit in c~ (offset i mod 32) — deterministic, spread over the field
            bad[i % 32] = bytes1(uint8(bad[i % 32]) ^ 0x01);

            address refPk = _placeRefPk(s.pkBlobs[i]);
            (bool okR, bytes memory retR) = address(refVerifier).staticcall(
                abi.encodeCall(ZZZ_E2ERef.verify, (refPk, s.msgs[i], bad))
            );
            // a tampered c~ must make the verifier return FALSE or revert;
            // it must never return TRUE
            if (okR) assertFalse(abi.decode(retR, (bool)), s.labels[i]);

            address shipPk = _deployShippedPk(s.pkBlobs[i]);
            (bool okS, bytes memory retS) = address(shipped).staticcall(
                abi.encodeCall(MLDSA44Verifier.verify, (shipPk, s.msgs[i], bad))
            );
            if (okS) assertFalse(abi.decode(retS, (bool)), s.labels[i]);
        }
    }
}
