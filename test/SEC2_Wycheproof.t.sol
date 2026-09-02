// SPDX-License-Identifier: MIT
// FILE: test/SEC2_Wycheproof.t.sol
//
// PROJECT WYCHEPROOF ML-DSA-44 VERIFY VECTORS against both in-tree verifiers:
// the reference implementation test/ZZZ_E2ERef.sol and the shipped
// src/MLDSA44Verifier.sol.
//
// Source (vendored verbatim, URL + SHA-256 + date in
// test/vectors/wycheproof/provenance.txt):
//   https://raw.githubusercontent.com/C2SP/wycheproof/main/
//     testvectors_v1/mldsa_44_verify_test.json
//   sha256 5ec04790c240c443ca8b662b8fc871834602c7cce87fcd36a193110745b2b9ea
//   27 groups, 180 tests, 77 valid / 103 invalid / 0 acceptable.
//
// WHY THIS SUITE EXISTS — it is not a duplicate of test/ACVP_MLDSA44.t.sol.
// The official NIST ACVP sigVer corpus has no systematic coverage of malformed
// HintBitPack encodings (the hEncode(h) region of the FIPS 204 signature).
// Wycheproof does, and that is precisely where real ML-DSA verifiers have
// broken:
//
//   tcId 15   hints in reverse order                   (non-monotone indices)
//   tcId 16   too many hints                           (buffer overflow)
//   tcId 17   non-zero padding in the hint section
//   tcId 18   a REPEATED hint index  <-- CVE-2026-24850 class (RustCrypto
//             `ml-dsa`); passes ACVP, fails Wycheproof
//   tcId 19   omega+1 hints                            (buffer overflow)
//   tcId 137  hint limit goes backwards (limit < idx)
//   tcId 138  last limit = 255, indices read past the 84-byte hint section
//   tcId 139  last limit = omega+k+1 = 85, reads one byte past the section
//
// plus 42 InfinityNormViolation cases (||z||inf / r0 / ct0 bounds, including
// the exact +-1 boundary pairs "z_max below/above the limit"), 35 ZeroPublicKey
// cases (t1 = 0), 61 BoundaryCondition cases (decompose / centered_mod /
// power_2_round / sample_in_ball edges) and the wrong-length inputs.
//
// EXPECTED VERDICTS are Wycheproof's own `result` field, never softened to
// match an implementation.  The builder additionally cross-checks every verdict
// against the pythonref dilithium_py reference oracle and aborts on any
// unadjudicated disagreement.
//
// >>> KNOWN ORACLE DIVERGENCE (python oracle, NOT the EVM verifiers) <<<
// The pythonref `dilithium_py` oracle that the rest of this test tree uses as
// its ground truth ACCEPTS tcId 18, the repeated-hint signature: its _unpack_h
// does not enforce the strictly-increasing index requirement of FIPS 204
// Algorithm 21, so a signature can be re-encoded into a second distinct byte
// string that still verifies (signature malleability).  Both in-tree EVM
// verifiers enforce monotonicity, the omega limits and the zero padding in
// their hint decoding — see test_wycheproof_repeated_hint_index, which pins
// that behaviour.
//
// Fixtures are produced in-repo by tools/fixtures/wycheproof_build.py, read
// through vm.ffi (cwd = repository root) and cached under test/fixtures/.
//
// REGENERATE FIXTURES:
//   pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py --build
//   pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py --audit
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {ZZZ_E2ERef, E2E_PK_SIZE} from "./ZZZ_E2ERef.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

contract SEC2WycheproofTest is Test {
    /// Wycheproof shard: the same cases fed to BOTH verifiers.
    /// Field order matches COMBO_T in tools/fixtures/wycheproof_build.py.
    struct Combo {
        bytes[] pkBlobs; //      deduplicated 20,544-byte pk payloads
        uint256[] pkIdx; //      case -> pk index
        uint256[] tcIds; //      Wycheproof tcId
        bytes[] msgs;
        bytes[] sigs; //         may be 2419 / 2420 / 2421 bytes on purpose
        bool[] expect; //        Wycheproof verdict (ctx forced empty; both
        //                       verifiers implement empty-ctx ML-DSA only)
        string[] labels; //      "WP<tcId>[flags]" (+ ":ctxbind")
    }

    /// Registration-layer shard: the four IncorrectPublicKeyLength cases.
    /// Field order matches PKLEN_T in tools/fixtures/wycheproof_build.py.
    struct PkLenShard {
        bytes[] rawPk; //        the malformed pk verbatim (1,311 / 1,313 bytes)
        bytes[] pkBlobs; //      payload built from the CANONICALISED key
        uint256[] tcIds;
        bytes[] msgs;
        bytes[] sigs;
        bool[] canonAccepts; //  MEASURED oracle verdict for the canonical key
        string[] labels;
    }

    /// in-repo shard builder; vm.ffi runs with cwd = the repository root.
    string constant FX = "tools/fixtures/wycheproof_build.py";

    uint256 constant ML_DSA_44_PK_LEN = 1312;

    ZZZ_E2ERef refVerifier;
    MLDSA44Verifier shipped;
    uint256 private _pkNonce;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        refVerifier = new ZZZ_E2ERef();
        shipped = new MLDSA44Verifier(deployF1600_170());
    }

    // ------------------------------------------------------------------ utils

    /// The builder prints the requested shard as hex on stdout (vm.ffi decodes
    /// hex automatically) and caches it under test/fixtures/.
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
    /// vm.etch rather than CREATE, for the reason documented in
    /// test/ACVP_MLDSA44.t.sol::test_acvp_eip3541_pk_prefix: the raw payload
    /// starts with tr = H(pk,64), so ~1/256 of ML-DSA-44 keys produce a blob
    /// whose first byte is 0xEF, which EIP-3541 makes impossible to deploy.
    function _placeRefPk(bytes memory blob) internal returns (address a) {
        a = address(uint160(uint256(keccak256(abi.encodePacked("wycheproof.pk.slot", ++_pkNonce)))));
        vm.etch(a, blob);
    }

    /// the shipped verifier's pk data contract: 0x00 || payload, deployed with
    /// a plain CREATE (always possible thanks to the 0x00 prefix)
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

    /// reference verifier, revert-tolerant: accepted == (call ok && true).
    /// A revert counts as "not accepted", never as a pass.
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

    /// Run every case of a shard against BOTH verifiers.
    /// `only` empty  => run all cases; otherwise run only those tcIds.
    ///
    /// `nWant` is the shard's PINNED case count, asserted ON CHAIN. The
    /// 176-case census and the corpus SHA-256 are checked only inside
    /// `wycheproof_build.py`, and `fx_common.serve` short-circuits to
    /// `target.read_text()` whenever the cache file already exists — so
    /// against a WARM `test/fixtures/` neither is re-derived, and the only
    /// other on-chain guard is `assertGt(ran, 0)` below, which a truncated
    /// cache passes. (`test/fixtures/` is gitignored, so CI is always cold;
    /// this is the guard for a developer tree that is not.)
    function _runCombo(string memory name, uint256 nWant, uint256[] memory only)
        internal
        returns (uint256 ran)
    {
        Combo memory s = abi.decode(_read(name), (Combo));
        assertEq(s.sigs.length, nWant, "shard case count");
        assertEq(s.expect.length, nWant, "shard verdict count");
        assertEq(s.tcIds.length, nWant, "shard tcId count");

        address[] memory refPk = new address[](s.pkBlobs.length);
        address[] memory shipPk = new address[](s.pkBlobs.length);
        for (uint256 i = 0; i < s.pkBlobs.length; ++i) {
            assertEq(s.pkBlobs[i].length, E2E_PK_SIZE, "pk blob size");
            refPk[i] = _placeRefPk(s.pkBlobs[i]);
            shipPk[i] = _deployShippedPk(s.pkBlobs[i]);
        }

        uint256 nAcc;
        uint256 nRej;
        for (uint256 i = 0; i < s.sigs.length; ++i) {
            if (only.length != 0 && !_contains(only, s.tcIds[i])) continue;
            ++ran;

            bool gotRef = _acceptRef(refPk[s.pkIdx[i]], s.msgs[i], s.sigs[i]);
            bool gotShip = _acceptShipped(shipPk[s.pkIdx[i]], s.msgs[i], s.sigs[i]);
            if (gotRef != s.expect[i] || gotShip != s.expect[i]) {
                console.log("WYCHEPROOF MISMATCH tcId:", s.tcIds[i]);
                console.log("  label / expected:", s.labels[i], s.expect[i]);
                console.log("  reference / shipped:", gotRef, gotShip);
            }
            assertEq(gotRef, s.expect[i], s.labels[i]);
            assertEq(gotShip, s.expect[i], s.labels[i]);

            if (s.expect[i]) ++nAcc;
            else ++nRej;
        }

        console.log("Wycheproof shard:", name);
        console.log("  cases / must-accept / must-reject:", ran, nAcc, nRej);
        assertGt(ran, 0, "shard selection matched no case");
    }

    function _runCombo(string memory name, uint256 nWant) internal returns (uint256) {
        return _runCombo(name, nWant, new uint256[](0));
    }

    function _contains(uint256[] memory xs, uint256 v) internal pure returns (bool) {
        for (uint256 i = 0; i < xs.length; ++i) {
            if (xs[i] == v) return true;
        }
        return false;
    }

    function _tc(uint256 a) internal pure returns (uint256[] memory o) {
        o = new uint256[](1);
        o[0] = a;
    }

    function _tc(uint256 a, uint256 b) internal pure returns (uint256[] memory o) {
        o = new uint256[](2);
        o[0] = a;
        o[1] = b;
    }

    function _tc(uint256 a, uint256 b, uint256 c) internal pure returns (uint256[] memory o) {
        o = new uint256[](3);
        o[0] = a;
        o[1] = b;
        o[2] = c;
    }

    // ============================================================ FULL CORPUS
    //
    // All 176 representable cases (180 minus the 4 wrong-length public keys,
    // which are registration-layer cases — see test_wycheproof_wrong_lengths),
    // round-robin sharded so every flag class appears in every shard:
    // 176 = 4 x 44, and each shard asserts its own 44 ON CHAIN.

    function test_wycheproof_corpus_shard0() public {
        _runCombo("wp_0.hex", 44);
    }

    function test_wycheproof_corpus_shard1() public {
        _runCombo("wp_1.hex", 44);
    }

    function test_wycheproof_corpus_shard2() public {
        _runCombo("wp_2.hex", 44);
    }

    function test_wycheproof_corpus_shard3() public {
        _runCombo("wp_3.hex", 44);
    }

    // ================================================= FLAGSHIP REGRESSIONS
    //
    // Each of the following pulls the specific tcIds carrying the corresponding
    // Wycheproof flag, so a reviewer can find the historically-real bug classes
    // by name.  All of them also run inside the corpus shards above; the
    // duplication is deliberate.

    /// InvalidHintsEncoding, tcId 18 — "signature with a repeated hint".
    /// The CVE-2026-24850 class (RustCrypto `ml-dsa`): HintBitUnpack (FIPS 204
    /// Algorithm 21) requires the indices within each polynomial's slice to be
    /// STRICTLY increasing, so a repeated index is a non-canonical encoding and
    /// the signature is invalid.  A verifier that misses it admits signature
    /// malleability: the same signature re-encodes to a different byte string
    /// that still verifies.
    ///
    /// The pythonref dilithium_py oracle used everywhere else in this tree
    /// ACCEPTS this vector — the builder reports that divergence loudly and
    /// keeps Wycheproof's "invalid" verdict.  Both in-tree EVM verifiers
    /// enforce the requirement in their hint decoding.
    ///
    /// tcId 16 and 19 are the companion "too many hints" / "omega+1 hints"
    /// buffer-overflow encodings.
    function test_wycheproof_repeated_hint_index() public {
        uint256 n = _runCombo("wpc_hints.hex", 8, _tc(18, 16, 19));
        assertEq(n, 3, "expected tcId 16/18/19 in wpc_hints.hex");
        console.log("tcId 18 (repeated hint, CVE-2026-24850 class) rejected by BOTH EVM verifiers");
        console.log("  NOTE: pythonref dilithium_py ACCEPTS this vector (see builder stderr banner)");
    }

    /// InvalidHintsEncoding, non-monotone / backwards limits.
    ///   tcId 15  hints in reverse order
    ///   tcId 137 hint limit goes backwards (limit < idx)
    function test_wycheproof_unsorted_hints() public {
        uint256 n = _runCombo("wpc_hints.hex", 8, _tc(15, 137));
        assertEq(n, 2, "expected tcId 15/137 in wpc_hints.hex");
    }

    /// InvalidHintsEncoding, tcId 17 — non-zero padding in the hint section.
    /// FIPS 204 Algorithm 21 requires hEncode[j] == 0 for every j past the last
    /// limit; a verifier that ignores the tail admits malleability.
    function test_wycheproof_nonzero_hint_padding() public {
        uint256 n = _runCombo("wpc_hints.hex", 8, _tc(17));
        assertEq(n, 1, "expected tcId 17 in wpc_hints.hex");
    }

    /// InvalidHintsEncoding, tcId 138/139 — crafted limits that make a naive
    /// decoder read past the 84-byte hint section (buffer overread).
    function test_wycheproof_hint_section_overread() public {
        uint256 n = _runCombo("wpc_hints.hex", 8, _tc(138, 139));
        assertEq(n, 2, "expected tcId 138/139 in wpc_hints.hex");
    }

    /// The whole InvalidHintsEncoding class in one go (8 cases, all must-reject).
    function test_wycheproof_hint_encoding_class() public {
        uint256 n = _runCombo("wpc_hints.hex", 8);
        assertEq(n, 8, "expected 8 InvalidHintsEncoding cases");
    }

    /// ZeroPublicKey — 35 cases whose pk has t1 = 0.  Forging against such a
    /// key is trivial, which is deliberately "none of the verification
    /// algorithm's business" (Wycheproof's own note): tcId 68 and one case in
    /// the degenerate group are VALID and must be ACCEPTED, while the other 33
    /// are invalid signatures that must still be rejected.  The registration-
    /// time pk validator, not the verifier, must reject degenerate keys
    /// (docs/SAFETY.md section 3).
    function test_wycheproof_zero_public_key() public {
        uint256 n = _runCombo("wpc_zeropk.hex", 35);
        assertEq(n, 35, "expected 35 ZeroPublicKey cases");
    }

    /// InfinityNormViolation — 42 cases, all must-reject, including the exact
    /// off-by-one boundary pairs that historically broke verifiers:
    ///   "z_max below the limit" / "z_max above the limit"
    ///   "r0_max below/above the limit", "ct0_max below/above the limit"
    ///   "h_ones below/above the limit"
    ///   "index 0 is exactly gamma1 - tau*eta"
    ///   "index 255 is exactly -(gamma1 - tau*eta)"
    /// Both verifiers enforce the strict FIPS 204 bound
    /// ||z||inf < gamma1 - beta.
    function test_wycheproof_infinity_norm_boundary() public {
        uint256 n = _runCombo("wpc_norm.hex", 42);
        assertEq(n, 42, "expected 42 InfinityNormViolation cases");
    }

    /// BoundaryCondition — 61 cases exercising decompose / centered_mod /
    /// power_2_round / use_hint / sample_in_ball edges (mixed accept/reject).
    function test_wycheproof_boundary_conditions() public {
        uint256 n = _runCombo("wpc_bound.hex", 61);
        assertEq(n, 61, "expected 61 BoundaryCondition cases");
    }

    /// ManySteps — 44 cases whose SampleInBall / RejNTTPoly sampling needs an
    /// unusually long rejection walk (mixed accept/reject).
    function test_wycheproof_many_steps() public {
        uint256 n = _runCombo("wpc_many.hex", 44);
        assertEq(n, 44, "expected 44 ManySteps cases");
    }

    /// Context binding.  Both in-tree verifiers implement ML-DSA with an EMPTY
    /// context only, so tcId 3 (7-byte ctx) and tcId 4 (255-byte ctx) — both
    /// VALID under their own context — must NOT be accepted (that is the
    /// FIPS 204 ctx domain separation working, label ":ctxbind").  tcId 2
    /// (ctx explicitly "") is the positive control and must be ACCEPTED.
    /// tcId 5 and 140..143 carry a 256-byte context: too long for FIPS 204,
    /// and the four 140..143 cases are the classic length-encoding confusions
    /// (len mod 256, min(len,255), 2-byte big/little-endian length) that a
    /// sloppy M' construction would accept.  All must-reject here.
    function test_wycheproof_context_binding() public {
        uint256 n = _runCombo("wpc_ctx.hex", 8);
        assertEq(n, 8, "expected 8 context cases");
    }

    // ------------------------------------------------------ wrong-length input

    /// IncorrectSignatureLength (representable) + IncorrectPublicKeyLength
    /// (NOT representable — registration layer).
    ///
    /// Signature length: both verifiers take `bytes calldata sig` and can be
    /// handed a 2,419- or 2,421-byte signature directly.  Both return false
    /// (or revert, which counts as reject).
    ///
    /// Public-key length: both verifiers consume a FIXED-SIZE pre-expanded pk
    /// data contract built off-chain from a 1,312-byte pk.  A 1,311- or
    /// 1,313-byte pk cannot be turned into one at all, so these four cases are
    /// NOT verifier cases and this test does not pretend otherwise.  What it
    /// asserts instead is the registration invariant plus the measured
    /// consequence of canonicalising the length:
    ///
    ///   tcId 64  1,311 B, zero-padded to 1,312 -> cache REJECTS
    ///   tcId 65  1,313 B, truncated  to 1,312 -> cache **ACCEPTS**
    ///   tcId 145 1,313 B (sig over H(long_pk))  -> cache REJECTS
    ///   tcId 146 1,311 B (sig over H(short_pk)) -> cache REJECTS
    ///
    /// FINDING (registration layer, not the verifier): tcId 65's "long public
    /// key" is a genuine 1,312-byte ML-DSA-44 key with a trailing 0x00 byte
    /// appended, and the signature was made over the real key.  A registration
    /// layer that "helpfully" truncates an over-long pk therefore accepts a
    /// non-canonical public-key encoding — pk-encoding malleability, two
    /// distinct pk byte strings mapping to the same on-chain cache.  The only
    /// safe rule is to enforce len(pk) == 1312 exactly, before hashing.
    function test_wycheproof_wrong_lengths() public {
        // ---- signature length: real verifier cases
        uint256 n = _runCombo("wpc_siglen.hex", 3);
        assertEq(n, 3, "expected 3 IncorrectSignatureLength cases");

        // ---- public-key length: registration-layer cases
        PkLenShard memory s = abi.decode(_read("wpc_pklen.hex"), (PkLenShard));
        assertEq(s.rawPk.length, 4, "expected 4 IncorrectPublicKeyLength cases");

        uint256 nCanonAccept;
        for (uint256 i = 0; i < s.rawPk.length; ++i) {
            if (_pkLenCase(s, i)) ++nCanonAccept;
        }
        assertEq(nCanonAccept, 1, "expected exactly one canonicalises-to-accepting case (tcId 65)");
        console.log("Wycheproof pk-length: 4 registration-layer cases, canonicalises-to-accept:", nCanonAccept);
    }

    /// One registration-layer (wrong pk length) case; returns whether
    /// canonicalising the length yields a cache that ACCEPTS.
    /// Split out of `test_wycheproof_wrong_lengths` only because the two halves
    /// together exceed the via-IR stack scheduler's budget.
    function _pkLenCase(PkLenShard memory s, uint256 i) internal returns (bool) {
        // (a) the registration invariant: a conforming registration layer must
        //     reject this pk on length alone, before it ever builds a cache.
        //     Nothing downstream can compensate.
        assertTrue(s.rawPk[i].length != ML_DSA_44_PK_LEN, "raw pk must NOT be 1312 bytes");
        assertTrue(
            s.rawPk[i].length == ML_DSA_44_PK_LEN - 1 || s.rawPk[i].length == ML_DSA_44_PK_LEN + 1,
            "expected a +-1 byte length"
        );

        // (b) what canonicalising the length would actually get you.
        bool gotRef = _acceptRef(_placeRefPk(s.pkBlobs[i]), s.msgs[i], s.sigs[i]);
        bool gotShip = _acceptShipped(_deployShippedPk(s.pkBlobs[i]), s.msgs[i], s.sigs[i]);

        if (gotRef != s.canonAccepts[i] || gotShip != s.canonAccepts[i]) {
            console.log("WYCHEPROOF PKLEN MISMATCH tcId:", s.tcIds[i]);
            console.log("  label / expected:", s.labels[i], s.canonAccepts[i]);
            console.log("  reference / shipped:", gotRef, gotShip);
        }
        assertEq(gotRef, s.canonAccepts[i], s.labels[i]);
        assertEq(gotShip, s.canonAccepts[i], s.labels[i]);

        if (s.canonAccepts[i]) {
            console.log("  REGISTRATION FINDING: tcId", s.tcIds[i]);
            console.log("    raw pk length:", s.rawPk[i].length);
            console.log("    canonicalising it to 1312 B yields a cache that ACCEPTS the signature");
            console.log("    => registration MUST enforce len(pk) == 1312 exactly, never truncate/pad");
        }
        return s.canonAccepts[i];
    }

    // ------------------------------------------------------------- flag census
    //
    // Flag classes present in the corpus and how they reach the verifiers, so
    // any structural gap is explicit rather than silent.  As of the vendored
    // file (sha256 5ec0479...) every flag class except IncorrectPublicKeyLength
    // has at least one case that reaches both EVM verifiers;
    // IncorrectPublicKeyLength is structurally a registration-layer class
    // (see above).
    function test_wycheproof_flag_coverage_report() public pure {
        console.log("Wycheproof flag coverage against the two EVM verifiers:");
        console.log("  ValidSignature            64  representable");
        console.log("  BoundaryCondition         61  representable");
        console.log("  ManySteps                 44  representable");
        console.log("  InfinityNormViolation     42  representable");
        console.log("  ZeroPublicKey             35  representable");
        console.log("  InvalidSignature          33  representable");
        console.log("  InvalidHintsEncoding       8  representable");
        console.log("  ModifiedSignature          7  representable");
        console.log("  InvalidContext             5  representable (both verifiers are empty-ctx,");
        console.log("                                so every over-long-ctx case is must-reject)");
        console.log("  IncorrectSignatureLength   3  representable");
        console.log("  InvalidPrivateKey          2  representable");
        console.log("  IncorrectPublicKeyLength   4  NOT representable: the on-chain pk cache is fixed-size,");
        console.log("                                so a 1311/1313-byte pk cannot reach a verifier at all.");
        console.log("                                Covered as a REGISTRATION-layer assertion instead");
        console.log("                                (test_wycheproof_wrong_lengths).");
        console.log("  acceptable-result cases    0  (policy would be MUST-REJECT; this file has none)");
    }
}
