// SPDX-License-Identifier: MIT
// FILE: test/ACVP_MLDSA44.t.sol
//
// OFFICIAL NIST ACVP ML-DSA-44 VECTORS against both in-tree verifiers: the
// reference implementation test/ZZZ_E2ERef.sol and the shipped
// src/MLDSA44Verifier.sol.
//
// Source (distilled into tools/fixtures/acvp_data/mldsa44.json; upstream URLs
// and SHA-256 digests are recorded under its `_provenance` key):
//   https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/
//     json-files/ML-DSA-sigVer-FIPS204/internalProjection.json
//   https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/
//     json-files/ML-DSA-sigGen-FIPS204/internalProjection.json
//   https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/
//     json-files/ML-DSA-sigGen-FIPS204-tr1/internalProjection.json
//
// Every one of those URLs is pinned by SHA-256 in ACVP_FILES
// (tools/fixtures/fx_common.py) and the digest is CHECKED on fetch.
//
// The sigVer set is the gold standard: it contains deliberately INVALID
// signatures that MUST be rejected (testPassed=false, reasons "modified
// message", "modified signature - commitment / - z / - hint").
//
// Case categories (built by tools/fixtures/acvp_build.py; expected verdicts
// come from ACVP's own internalProjection, and every one of them is
// independently reproduced by the pythonref oracle at build time):
//   SV<tc>  official sigVer ML-DSA-44 external/pure case, ACVP verdict
//   SG<tc>  official sigGen ML-DSA-44 external/pure case (always valid)
//   *:ctxbind   same official case, but both verifiers here implement ML-DSA
//               with an EMPTY context only (M' = 0x00||0x00||M), so a
//               non-empty-ctx signature must NOT be accepted — a
//               context/domain-separation check.
//   PH<tc>  official ACVP HashML-DSA (preHash) case: M' = 0x01||len||ctx||OID||
//           PH(M), so it must NEVER verify as PURE ML-DSA (M' = 0x00||...) —
//           the FIPS 204 pure/preHash domain separation.  45 such cases, all
//           must-reject; the build confirms each one verifies correctly in
//           its own preHash domain first.
//   DV<tc>  ACVP-derived: the official (sk, message) re-signed with ctx="" so
//           that both verifiers get true-positive coverage on official NIST
//           key material, plus the four ACVP mutation classes applied to that
//           fresh signature (each confirmed rejected by the oracle).
//   TP<tc>:<keyFormat> / TH<tc>:<keyFormat>
//           the FIPS204-tr1 sigGen corpus (at_* shards): 60 external/pure and
//           60 external/preHash cases on 120 keys disjoint from every other
//           corpus here.  5 of the 60 pure cases carry an EMPTY context and
//           are MUST-ACCEPT — the only official-answer must-accepts in this
//           suite (see below).
//
// WHAT THE OFFICIAL sigVer CORPUS DOES AND DOES NOT GIVE US.  Its `testPassed`
// distribution is 3 valid / 12 invalid, but all three valid cases carry a
// NON-EMPTY context, and this interface is empty-context only, so all 15 SV
// cases are MUST-REJECT.  The official sigVer set therefore contributes ZERO
// must-accept coverage here; the must-accepts in ah_* are 3 sigGen cases with
// an empty context plus the 15 repo-derived DV re-signings.  The at_* shards
// are where an official ACVP answer says "accept" and this verifier accepts.
//
// Fixtures are produced in-repo by tools/fixtures/acvp_build.py, read through
// vm.ffi (cwd = repository root) and cached under test/fixtures/.
//
// REGENERATE FIXTURES:
//   pythonref/myenv/bin/python tools/fixtures/acvp_build.py --build
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {ZZZ_E2ERef, E2E_PK_SIZE} from "./ZZZ_E2ERef.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

contract ACVPMLDSA44Test is Test {
    /// one fixture shard (ABI tuple emitted by acvp_build.py; field order
    /// matches SHARD_T there — abi.decode is positional)
    struct Shard {
        bytes[] pkBlobs; // deduplicated 20,544-byte pk payloads
        uint256[] pkIdx; // case -> pk index
        bytes[] msgs;
        bytes[] sigs;
        bool[] expect; //   ACVP verdict, oracle-reproduced (empty ctx)
        string[] labels;
    }

    /// in-repo shard builder (see tools/fixtures/README_shards.md); vm.ffi
    /// runs with cwd = the repository root, so the path is repo-relative.
    string constant FX = "tools/fixtures/acvp_build.py";

    ZZZ_E2ERef refVerifier;
    MLDSA44Verifier shipped;
    RawDataDeployer deployer;
    uint256 private _pkNonce;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        refVerifier = new ZZZ_E2ERef();
        shipped = new MLDSA44Verifier(deployF1600_170());
        deployer = new RawDataDeployer();
    }

    // ------------------------------------------------------------------ utils

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

    /// Place a raw pk payload as account code (code == blob, no prefix), which
    /// is what the reference verifier's EXTCODECOPY stream expects.
    ///
    /// vm.etch is used instead of CREATE on purpose: the raw payload starts
    /// with tr = H(pk,64), so ~1/256 of ML-DSA-44 keys yield a blob whose first
    /// byte is 0xEF, which EIP-3541 makes IMPOSSIBLE to deploy with
    /// CREATE/CREATE2 (see test_acvp_eip3541_pk_prefix, which reproduces it
    /// with an official ACVP key).  The shipped verifier's 0x00-prefixed
    /// layout does not have this limitation.
    function _placeRefPk(bytes memory blob) internal returns (address a) {
        a = address(uint160(uint256(keccak256(abi.encodePacked("acvp.pk.slot", ++_pkNonce)))));
        vm.etch(a, blob);
    }

    /// Deploy a data contract whose code is exactly `data` (raw CREATE).
    function _deployData(bytes memory data) internal returns (address ptr) {
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "pk data contract deploy failed");
    }

    /// The shipped verifier's pk data contract: 0x00 || payload (20,545 bytes).
    /// The 0x00 prefix keeps the code EIP-3541-deployable for every key, so a
    /// plain CREATE always works here — no vm.etch needed.
    function _deployShippedPk(bytes memory blob) internal returns (address) {
        return _deployData(bytes.concat(hex"00", blob));
    }

    /// reference verifier, revert-tolerant: accepted == (call ok && true)
    function _acceptRef(address pk, bytes memory m, bytes memory sig) internal view returns (bool accepted) {
        (bool ok, bytes memory ret) = address(refVerifier).staticcall(abi.encodeCall(ZZZ_E2ERef.verify, (pk, m, sig)));
        accepted = ok && ret.length == 32 && abi.decode(ret, (bool));
    }

    /// shipped verifier, revert-tolerant
    function _acceptShipped(address pk, bytes memory m, bytes memory sig) internal view returns (bool accepted) {
        (bool ok, bytes memory ret) =
            address(shipped).staticcall(abi.encodeCall(MLDSA44Verifier.verify, (pk, m, sig)));
        accepted = ok && ret.length == 32 && abi.decode(ret, (bool));
    }

    // ------------------------------------------------------------ shard runner

    /// Every case of the shard is fed to BOTH verifiers; any divergence from
    /// the ACVP/oracle verdict — or between the two implementations — fails.
    ///
    /// THE PER-SHARD CASE COUNT IS ASSERTED HERE, ON CHAIN: `nWant` is the size
    /// this file pins for the shard, exactly as
    /// `FV2_AcvpKeyGen.t.sol::_runShard` asserts its own 5. The 165/120 CORPUS
    /// CENSUSES and the corpus SHA-256 are checked ONLY inside the Python
    /// builders, and `fx_common.serve` short-circuits to `target.read_text()`
    /// whenever the cache file already exists — so against a WARM
    /// `test/fixtures/` nothing re-derives either, and without this assertion a
    /// truncated or substituted cache file would simply run fewer cases and
    /// still pass.
    /// (`test/fixtures/` is gitignored, so CI is always cold; this is the guard
    /// for a developer tree that is not.)
    function _runShard(uint256 k, uint256 nWant) internal {
        _runNamedShard(string.concat("ah_", vm.toString(k), ".hex"), k, nWant);
    }

    function _runShard(string memory prefix, uint256 k, uint256 nWant) internal {
        _runNamedShard(string.concat(prefix, vm.toString(k), ".hex"), k, nWant);
    }

    function _runNamedShard(string memory name, uint256 k, uint256 nWant) internal {
        Shard memory s = abi.decode(_read(name), (Shard));
        assertEq(s.sigs.length, nWant, "shard case count");
        assertEq(s.expect.length, nWant, "shard verdict count");
        assertEq(s.msgs.length, nWant, "shard message count");

        address[] memory refPk = new address[](s.pkBlobs.length);
        address[] memory shipPk = new address[](s.pkBlobs.length);
        for (uint256 i = 0; i < s.pkBlobs.length; ++i) {
            assertEq(s.pkBlobs[i].length, E2E_PK_SIZE, "pk blob size");
            refPk[i] = _placeRefPk(s.pkBlobs[i]);
            shipPk[i] = _deployShippedPk(s.pkBlobs[i]);
        }

        uint256 nPos;
        uint256 nNeg;
        for (uint256 i = 0; i < s.sigs.length; ++i) {
            bool gotRef = _acceptRef(refPk[s.pkIdx[i]], s.msgs[i], s.sigs[i]);
            bool gotShip = _acceptShipped(shipPk[s.pkIdx[i]], s.msgs[i], s.sigs[i]);
            if (gotRef != s.expect[i] || gotShip != s.expect[i]) {
                console.log("ACVP MISMATCH shard/case:", k, i);
                console.log("  label / expected:", s.labels[i], s.expect[i]);
                console.log("  reference / shipped:", gotRef, gotShip);
            }
            assertEq(gotRef, s.expect[i], s.labels[i]);
            assertEq(gotShip, s.expect[i], s.labels[i]);
            if (s.expect[i]) ++nPos;
            else ++nNeg;
        }
        console.log("ACVP shard, cases / must-accept / must-reject:", s.sigs.length, nPos, nNeg);
    }

    function test_acvp_shard0() public {
        _runShard(0, 28); // 165 = 28+28+28+27+27+27
    }

    function test_acvp_shard1() public {
        _runShard(1, 28); // 165 = 28+28+28+27+27+27
    }

    function test_acvp_shard2() public {
        _runShard(2, 28); // 165 = 28+28+28+27+27+27
    }

    function test_acvp_shard3() public {
        _runShard(3, 27); // 165 = 28+28+28+27+27+27
    }

    function test_acvp_shard4() public {
        _runShard(4, 27); // 165 = 28+28+28+27+27+27
    }

    function test_acvp_shard5() public {
        _runShard(5, 27); // 165 = 28+28+28+27+27+27
    }

    // ------------------------------------------------- FIPS204-tr1 (at_*)
    //
    // The technical-corrigendum-1 sigGen projection: 120 ML-DSA-44
    // external-interface cases on 120 official keys that appear NOWHERE ELSE
    // in this tree (acvp_build.py asserts the key sets are disjoint).  It is
    // the only official-answer corpus here that yields must-ACCEPTs at this
    // interface: 5 of its 60 pure cases were generated with an EMPTY context,
    // which is exactly the interface both verifiers implement.  The remaining
    // 55 pure cases are must-reject on context binding, and all 60 preHash
    // cases are must-reject on pure/preHash domain separation.  Both verifiers
    // are asserted on every case, as above.

    function test_acvp_tr1_shard0() public {
        _runShard("at_", 0, 30); // 120 = 4 x 30
    }

    function test_acvp_tr1_shard1() public {
        _runShard("at_", 1, 30); // 120 = 4 x 30
    }

    function test_acvp_tr1_shard2() public {
        _runShard("at_", 2, 30); // 120 = 4 x 30
    }

    function test_acvp_tr1_shard3() public {
        _runShard("at_", 3, 30); // 120 = 4 x 30
    }

    // ----------------------------------------------------- EIP-3541 / 0xEF pk
    //
    // A RAW pk data contract (code == payload, as the reference layout uses)
    // starts with tr = SHAKE256(pk, 64).  EIP-3541 forbids deploying any
    // contract whose code starts with 0xEF, so a public key whose tr[0] is
    // 0xEF (uniformly ~1/256 of all ML-DSA-44 keys) can NEVER be registered
    // with CREATE/CREATE2 — the deployment fails and returns the zero address.
    // Official ACVP shard ah_1 contains such a key (sigVer tcId 14).
    //
    // The shipped MLDSA44Verifier avoids this by construction: its pk data
    // contract is 0x00 || payload (prepare/prepare.py output), so the first
    // code byte is always 0x00 and every key is deployable.  This test
    // demonstrates both halves with the official 0xEF-tr key:
    //   (a) the raw payload cannot be CREATE-deployed at all, while a control
    //       payload from the same shard can;
    //   (b) the 0x00-prefixed payload deploys fine and the shipped verifier
    //       accepts that key's must-accept vectors through it.
    function test_acvp_eip3541_pk_prefix() public {
        Shard memory s = abi.decode(_read("ah_1.hex"), (Shard));
        uint256 idxEF = type(uint256).max;
        uint256 idxOk = type(uint256).max;
        for (uint256 i = 0; i < s.pkBlobs.length; ++i) {
            if (uint8(s.pkBlobs[i][0]) == 0xEF) idxEF = i;
            else if (idxOk == type(uint256).max) idxOk = i;
        }
        assertTrue(idxEF != type(uint256).max, "expected a tr[0]==0xEF ACVP key in shard 1");
        assertTrue(idxOk != type(uint256).max, "expected a normal ACVP key in shard 1");

        // (a) a normal raw payload deploys fine ...
        address ok = deployer.deployRaw{gas: 30_000_000}(s.pkBlobs[idxOk]);
        assertTrue(ok != address(0), "control blob must deploy");
        assertEq(ok.code.length, E2E_PK_SIZE, "control blob code size");

        // ... but the raw 0xEF payload cannot be deployed at all
        address bad;
        try deployer.deployRaw{gas: 30_000_000}(s.pkBlobs[idxEF]) returns (address a) {
            bad = a;
        } catch {
            bad = address(0);
        }
        assertEq(bad, address(0), "EIP-3541: raw 0xEF-prefixed pk payload must fail to deploy");

        // (b) the shipped layout deploys the very same key with a plain CREATE
        // (first code byte is the 0x00 prefix) and verifies its official
        // must-accept vectors.
        address shipPk = _deployShippedPk(s.pkBlobs[idxEF]);
        assertEq(shipPk.code.length, E2E_PK_SIZE + 1, "shipped pk data contract size");
        assertEq(uint8(shipPk.code[0]), 0x00, "shipped pk data contract prefix");
        uint256 verified;
        for (uint256 i = 0; i < s.sigs.length; ++i) {
            if (s.pkIdx[i] != idxEF || !s.expect[i]) continue;
            assertTrue(_acceptShipped(shipPk, s.msgs[i], s.sigs[i]), "0xEF-tr key must verify via shipped layout");
            ++verified;
        }
        assertGt(verified, 0, "expected at least one must-accept vector for the 0xEF-tr key");
        console.log("EIP-3541: raw 0xEF payload undeployable; 0x00-prefixed layout verifies N vectors:", verified);
    }
}

/// Minimal helper so a failing (all-gas-consuming) CREATE can be attempted
/// inside a gas-capped external frame.
contract RawDataDeployer {
    function deployRaw(bytes calldata data) external returns (address ptr) {
        require(data.length < 24576, "EIP-170");
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
    }
}
