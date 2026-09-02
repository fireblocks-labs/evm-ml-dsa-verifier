// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC_pkcache.t.sol
//
// Security tests for the public-key data-contract handling of both verifier
// subjects: the reference verifier (test/ZZZ_E2ERef.sol, code == 20,544-byte
// payload) and the shipped MLDSA44Verifier (src, code == 0x00 || 20,544-byte
// payload, payload read from offset 1).
//
// STRUCTURAL CHECK (tested first): neither verifier can consume a blob of the
// wrong size. EXTCODECOPY zero-pads silently, so both check EXTCODESIZE EXACTLY
// and fail closed (verify returns false) on any absent, truncated, oversized or
// unrelated data contract. The shipped verifier's leading 0x00 byte is a
// deployability device (EIP-3541 forbids deployed code beginning with 0xEF);
// it is NOT authenticated content — the verifier reads the payload from offset 1
// and never inspects byte 0.
//
// RESIDUAL RISK (the reason docs/SAFETY.md section 3 makes registration-time
// validation MANDATORY): the size check is the only pk validation a verifier can
// make cheaply. A correctly-sized but bogus blob passes every structural check,
// and a forger who knows the blob can compute a matching signature with no
// secret key:
//   * an all-zero cache makes w' = 0 and w1Encode(w1) = 0^768, so the challenge
//     c~ = SHAKE256(mu || 0^768) is a value the forger simply evaluates;
//   * the DEGENERATE public key t1 = 0 has a perfectly well-formed, honestly
//     derived cache (A = ExpandA(rho), t1 = 0) under which the same forgery
//     succeeds — and it is accepted by the reference FIPS 204 verifier too, so
//     a validator that merely RE-DERIVES the cache from a standard pk is not
//     enough: it must also reject degenerate keys — by an explicit criterion ON
//     THE KEY. PROOF-OF-POSSESSION IS NOT SUCH A CRITERION: it is a signature
//     check, and under a degenerate key a signature is free, so anyone answers a
//     registrar's challenge under it with no secret material
//     (test_proof_of_possession_does_not_reject_a_degenerate_key below).
//     NEITHER IS A PROOF OF KNOWLEDGE OF (s1, s2), a candidate check that
//     docs/SAFETY.md §3.1 quotes as "the complete answer" and then refutes:
//     the degenerate class has PUBLICLY COMPUTABLE, norm-conforming, exact
//     secret keys — (0, 0, 0) for t1 = 0 and
//     (0, -1, 0) for t1 = 1023 — and they really sign
//     (test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key).
// Both forgeries are demonstrated below against both subjects, along with the
// maximal degenerate key (t1 = 1023 everywhere, every pkEncode byte 0xff) and a
// degenerate-key forgery whose signature looks entirely ordinary.
//
// KERNEL BOUND: the matvec MAC kernels assume canonical (< q) cache
// coefficients. A non-canonical field violates their 64-bit-lane no-borrow
// invariant, which is a further reason the cache must be validated before use.
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {_F1600_AT, _F1600_CODE, shake256Fast} from "./ZZZ_FastKeccak.sol";
import {ZZZ_E2ERef, E2E_PK_SIZE, E2E_KQ24, macCompactLazy, macSubCT1Lazy} from "./ZZZ_E2ERef.sol";

contract SECPkCacheTest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant DEGEN = "tools/fixtures/degen.py";
    string constant DEGEN2 = "tools/fixtures/degen2.py";
    string constant SEED = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    /// a SECOND degenerate key, so the proof-of-possession case below is not the
    /// same key as the forgery case above.
    string constant DEGEN_SEED2 = "5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed5eed";
    /// The REGISTRAR's challenge: chosen by the registrar at registration time,
    /// with no input from the party being registered. ASCII
    /// "MLDSA-REG-CHALLENGE:2026-08-15:nonce=8f3c1a90d47b6e25".
    string constant POP_CHALLENGE_HEX =
        "0x4d4c4453412d5245472d4348414c4c454e47453a323032362d30382d31353a6e6f6e63653d38663363316139306434376236653235";
    bytes constant POP_CHALLENGE =
        hex"4d4c4453412d5245472d4348414c4c454e47453a323032362d30382d31353a6e6f6e63653d38663363316139306434376236653235";
    uint256 constant Q_ = 8380417;
    uint256 constant GAMMA2_ = 95232; // (q - 1) / 88
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";
    bytes constant MSG = hex"1111222233334444111122223333444411112222333344441111222233334444";

    address f1600;
    ZZZ_E2ERef refv;
    MLDSA44Verifier shipped;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE); // reference verifier's helper
        f1600 = deployF1600_170(); // shipped verifier's helper
        refv = new ZZZ_E2ERef();
        shipped = new MLDSA44Verifier(f1600);
    }

    // --------------------------------------------------------------- fixtures

    function _vec(string memory seedHex, string memory msgHex)
        internal
        returns (bytes memory sig, bytes memory pkBlob, bytes memory m)
    {
        string[] memory cmds = new string[](5);
        cmds[0] = PY;
        cmds[1] = VECGEN;
        cmds[2] = "seed";
        cmds[3] = seedHex;
        cmds[4] = msgHex;
        (sig, pkBlob, m) = abi.decode(vm.ffi(cmds), (bytes, bytes, bytes));
    }

    function _deployData(bytes memory data) internal returns (address ptr) {
        require(data.length < 24576, "EIP-170");
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "deploy failed");
    }

    /// reference verifier expects the raw 20,544-byte payload as code.
    function _refPk(bytes memory blob) internal returns (address) {
        return _deployData(blob);
    }

    /// shipped verifier expects 0x00 || payload (payload read from offset 1).
    function _shipPk(bytes memory blob) internal returns (address) {
        return _deployData(bytes.concat(hex"00", blob));
    }

    /// zEncode(z = 0): every 18-bit field carries the raw value gamma1 = 2^17,
    /// which both decoders map to the centered value 0.
    function _zeroZBytes() internal pure returns (bytes memory zb) {
        zb = new bytes(2304);
        for (uint256 i = 0; i < 2304; i += 9) {
            zb[i + 2] = 0x02; // field0 bit 17
            zb[i + 4] = 0x08; // field1 bit 17
            zb[i + 6] = 0x20; // field2 bit 17
            zb[i + 8] = 0x80; // field3 bit 17
        }
    }

    /// the forged signature for an all-zero cache: c~ = SHAKE256(mu || 0^768, 32)
    /// with mu = SHAKE256(tr = 0^64 || 0x00 || 0x00 || M, 64), z = 0, h = 0.
    function _forgeZeroCacheSig(bytes memory m) internal view returns (bytes memory sig) {
        bytes memory muIn = new bytes(66 + m.length); // tr = 0^64, dom = 0, |ctx| = 0
        for (uint256 i = 0; i < m.length; ++i) {
            muIn[66 + i] = m[i];
        }
        bytes memory mu = shake256Fast(muIn, 64);
        bytes memory fin = new bytes(832); // mu || 768 zero bytes (w1Encode(0))
        for (uint256 i = 0; i < 64; ++i) {
            fin[i] = mu[i];
        }
        bytes32 cTilde = bytes32(shake256Fast(fin, 32));
        sig = bytes.concat(cTilde, _zeroZBytes(), new bytes(84));
        require(sig.length == 2420, "sig len");
    }

    function _fill(uint256 n, uint8 v) internal pure returns (bytes memory b) {
        b = new bytes(n);
        for (uint256 i = 0; i < n; ++i) {
            b[i] = bytes1(v);
        }
    }

    // ======================================== reference size-check battery ==

    function test_reference_size_gate_rejects_bad_pk_contracts() public {
        bytes memory sig = _forgeZeroCacheSig(MSG);

        // codeless address
        assertFalse(refv.verify(address(0xdead), MSG, sig), "codeless pk");
        // every precompile address
        for (uint256 a = 1; a <= 9; ++a) {
            assertFalse(refv.verify(address(uint160(a)), MSG, sig), "precompile-as-pk");
        }
        // truncated / oversized blobs
        assertFalse(refv.verify(_deployData(new bytes(E2E_PK_SIZE - 1)), MSG, sig), "size-1");
        assertFalse(refv.verify(_deployData(new bytes(E2E_PK_SIZE + 1)), MSG, sig), "size+1");
        assertFalse(refv.verify(_deployData(hex"00"), MSG, sig), "1-byte contract");
        // an unrelated contract (wrong size) and the keccak helper itself
        assertFalse(refv.verify(address(refv), MSG, sig), "verifier-as-pk");
        assertFalse(refv.verify(_F1600_AT, MSG, sig), "helper-as-pk");
    }

    // ========================================== shipped size-check battery ==

    function test_shipped_size_gate_rejects_bad_pk_contracts() public {
        bytes memory sig = _forgeZeroCacheSig(MSG);

        assertFalse(shipped.verify(address(0xdead), MSG, sig), "codeless pk");
        for (uint256 a = 1; a <= 9; ++a) {
            assertFalse(shipped.verify(address(uint160(a)), MSG, sig), "precompile-as-pk");
        }
        // the shipped verifier requires 20,545 bytes (0x00 || payload); the raw
        // 20,544-byte payload with no prefix is one byte short and rejected.
        assertFalse(shipped.verify(_deployData(new bytes(E2E_PK_SIZE)), MSG, sig), "missing prefix");
        assertFalse(shipped.verify(_deployData(new bytes(E2E_PK_SIZE + 2)), MSG, sig), "oversized");
        assertFalse(shipped.verify(_deployData(hex"00"), MSG, sig), "1-byte contract");
        assertFalse(shipped.verify(address(shipped), MSG, sig), "verifier-as-pk");
        assertFalse(shipped.verify(f1600, MSG, sig), "helper-as-pk");
    }

    // ================================ shipped prefix byte is not authenticated

    /// The leading byte of the shipped verifier's data contract is only there so
    /// deployment satisfies EIP-3541; it is not part of the authenticated key
    /// material. A cache with any other prefix byte yields the identical verdict.
    function test_shipped_prefix_byte_is_not_authenticated() public {
        (bytes memory sig, bytes memory pkBlob, bytes memory m) = _vec(SEED, MSG1_HEX);

        address pkZeroPrefix = _deployData(bytes.concat(hex"00", pkBlob));
        address pkFfPrefix = _deployData(bytes.concat(hex"ff", pkBlob)); // 0xff is deployable
        assertEq(pkZeroPrefix.code.length, E2E_PK_SIZE + 1, "size ok");
        assertEq(pkFfPrefix.code.length, E2E_PK_SIZE + 1, "size ok");

        assertTrue(shipped.verify(pkZeroPrefix, m, sig), "genuine tuple, 0x00 prefix");
        assertTrue(shipped.verify(pkFfPrefix, m, sig), "genuine tuple, 0xff prefix (byte 0 ignored)");
    }

    // ============================== S1 residual: all-zero cache is forgeable ==

    /// A correctly-sized all-zero cache passes every structural check, yet admits
    /// a key-free universal forgery on BOTH subjects. Only registration-time
    /// validation of the blob (docs/SAFETY.md section 3) prevents this.
    function test_all_zero_cache_admits_universal_forgery_on_both_subjects() public {
        bytes memory forged = _forgeZeroCacheSig(MSG);

        // reference: raw 20,544-byte all-zero cache
        address refZero = _refPk(new bytes(E2E_PK_SIZE));
        assertEq(refZero.code.length, E2E_PK_SIZE, "reference cache size check satisfied");
        assertTrue(refv.verify(refZero, MSG, forged), "reference accepts the forgery");

        // shipped: 0x00 || 20,544-byte all-zero cache
        address shipZero = _shipPk(new bytes(E2E_PK_SIZE));
        assertEq(shipZero.code.length, E2E_PK_SIZE + 1, "shipped cache size check satisfied");
        assertTrue(shipped.verify(shipZero, MSG, forged), "shipped accepts the forgery");

        // an HONEST signature (made for a real key) is NOT accepted by the zero
        // cache: it is specifically the forger's freedom to choose c~ that breaks
        // the scheme, not any weakness in the verifier's arithmetic.
        (bytes memory honestSig,,) = _vec(SEED, MSG1_HEX);
        assertFalse(refv.verify(refZero, MSG, honestSig), "honest sig rejected by zero cache");
        assertFalse(shipped.verify(shipZero, MSG, honestSig), "honest sig rejected by zero cache");
    }

    /// A hostile-content but correctly-sized cache (all 0xff) never accepts a
    /// signature and never reverts (fail-closed, deterministic).
    function test_hostile_cache_contents_are_fail_closed() public {
        bytes memory sig = _forgeZeroCacheSig(MSG);
        assertFalse(refv.verify(_refPk(_fill(E2E_PK_SIZE, 0xff)), MSG, sig), "0xff cache, reference");
        assertFalse(shipped.verify(_shipPk(_fill(E2E_PK_SIZE, 0xff)), MSG, sig), "0xff cache, shipped");
    }

    // ================================ degenerate key (t1 = 0) forgery =========

    /// The degenerate public key t1 = 0 has a well-formed, HONESTLY DERIVED cache
    /// (A is the genuine ExpandA(rho) image; only t1 is zero), under which anyone
    /// can forge a signature for any message. It is accepted by both subjects and
    /// by the reference FIPS 204 verifier, so it is ML-DSA's known lack of
    /// key-substitution robustness, not a verifier bug. The consequence for this
    /// design: the mandatory registration-time validator (docs/SAFETY.md section
    /// 3) must REJECT degenerate keys, not merely re-derive the cache.
    function test_degenerate_key_cache_forgery_accepted_by_both_and_by_FIPS() public {
        string[] memory cmds = new string[](4);
        cmds[0] = PY;
        cmds[1] = DEGEN;
        cmds[2] = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";
        cmds[3] = MSG1_HEX;
        (bytes memory pkBlob, bytes memory sig, bytes memory pk, bool fipsOk) =
            abi.decode(vm.ffi(cmds), (bytes, bytes, bytes, bool));

        assertEq(pkBlob.length, E2E_PK_SIZE, "cache size");
        assertEq(pk.length, 1312, "standard ML-DSA-44 pk size");
        assertTrue(fipsOk, "the reference FIPS 204 verifier also accepts this forgery");

        assertTrue(refv.verify(_refPk(pkBlob), MSG, sig), "reference accepts the degenerate-key forgery");
        assertTrue(shipped.verify(_shipPk(pkBlob), MSG, sig), "shipped accepts the degenerate-key forgery");

        // the A block (offset 4160..) is the genuine, non-zero ExpandA image, so a
        // re-derivation-only validator would have signed off on this cache.
        bool aNonZero = false;
        for (uint256 i = 4160; i < pkBlob.length; ++i) {
            if (pkBlob[i] != 0) {
                aNonZero = true;
                break;
            }
        }
        assertTrue(aNonZero, "A must be the genuine (non-zero) ExpandA image");
    }

    // ================= PROOF-OF-POSSESSION IS NOT A DEGENERACY CHECK =========

    /// |centred lift| of every t1 coefficient of a 1,312-byte pk, counted against
    /// gamma2 — the quantity docs/SAFETY.md section 3.1's criterion (ii) thresholds.
    /// pkEncode(t1) is 1,024 ten-bit little-endian fields after the 32-byte rho.
    function _bigLiftCount(bytes memory pk) internal pure returns (uint256 big) {
        for (uint256 c = 0; c < 1024; ++c) {
            uint256 bit = 10 * c;
            uint256 b = 32 + (bit >> 3);
            uint256 acc = uint256(uint8(pk[b])) | (uint256(uint8(pk[b + 1])) << 8);
            uint256 v = (acc >> (bit & 7)) & 0x3ff;
            uint256 t = (v << 13) % Q_;
            uint256 mag = t > Q_ / 2 ? Q_ - t : t; // |2^13 * v mod± q|
            if (mag > GAMMA2_) ++big;
        }
    }

    /// PROOF-OF-POSSESSION IS NOT A DEGENERACY CHECK, as a test rather than as
    /// prose. docs/SAFETY.md §3.1 quotes the tempting advice to "lead with
    /// proof-of-possession" against degenerate keys, justified by "a
    /// key-free-forgeable pk has no owner", and then refutes it: such a key has
    /// EVERY owner. PoP is a SIGNATURE check, and under a degenerate key a
    /// signature is exactly what is free, so PoP is not merely weak on this
    /// class — it is vacuous on it.
    ///
    /// The shape below is the registrar's, not the attacker's: the REGISTRAR picks
    /// the challenge, the applicant holds no secret material at all, and one shot
    /// with no grinding produces a response over that exact challenge which the
    /// reference FIPS 204 verifier and BOTH on-chain subjects accept. A registrar
    /// whose only degeneracy check is PoP therefore admits t1 = 0 — while the
    /// criterion section 3.1 actually mandates refuses it.
    function test_proof_of_possession_does_not_reject_a_degenerate_key() public {
        string[] memory cmds = new string[](4);
        cmds[0] = PY;
        cmds[1] = DEGEN;
        cmds[2] = DEGEN_SEED2;
        cmds[3] = POP_CHALLENGE_HEX; // the registrar's challenge, verbatim
        (bytes memory pkBlob, bytes memory sig, bytes memory pk, bool fipsOk) =
            abi.decode(vm.ffi(cmds), (bytes, bytes, bytes, bool));

        assertEq(pk.length, 1312, "standard ML-DSA-44 pk size");
        assertEq(pkBlob.length, E2E_PK_SIZE, "cache size");
        assertEq(sig.length, 2420, "standard ML-DSA-44 signature size");

        // (1) the response satisfies proof-of-possession under a genuine FIPS 204
        //     verifier, and under both subjects, with NO secret key in existence.
        assertTrue(fipsOk, "PoP: the reference FIPS 204 verifier accepts the response");
        assertTrue(
            refv.verify(_refPk(pkBlob), POP_CHALLENGE, sig), "PoP: reference verifier accepts the response"
        );
        assertTrue(
            shipped.verify(_shipPk(pkBlob), POP_CHALLENGE, sig), "PoP: shipped verifier accepts the response"
        );

        // (2) the key it "proves possession of" is the degenerate one: pkEncode(t1)
        //     is 1,280 zero bytes, so ANY party could have produced (1).
        for (uint256 i = 32; i < 1312; ++i) {
            assertEq(uint8(pk[i]), 0, "the registered key must be the degenerate t1 = 0");
        }

        // (3) ... and the criterion section 3.1 mandates DOES refuse it: not one of
        //     the 1,024 centred lifts exceeds gamma2, far below the "at least half"
        //     floor. That is the check; PoP is not, and never substitutes for it.
        assertEq(_bigLiftCount(pk), 0, "every centred lift of t1 = 0 is 0");
        assertTrue(_bigLiftCount(pk) < (4 * 256) / 2, "centred-lift criterion REFUSES this key");
    }

    // ======== A PROOF OF KNOWLEDGE OF (s1, s2) IS NOT A DEGENERACY CHECK =====

    /// docs/SAFETY.md §3.1 quotes "a proof of knowledge of (s1, s2) — the
    /// complete answer, because it demands the one object a degenerate key does
    /// not have" as the natural replacement for proof-of-possession, and then
    /// refutes it. A DEGENERATE KEY DOES HAVE THAT OBJECT, AND IT IS PUBLIC.
    /// Both flagship members of the class carry an exact, norm-conforming
    /// ML-DSA secret key that any party can write down without knowing
    /// anything:
    ///
    ///   t1 = 0    everywhere  <-  (s1, s2, t0) = ( 0,  0, 0)
    ///   t1 = 1023 everywhere  <-  (s1, s2, t0) = ( 0, -1, 0)
    ///
    /// because Power2Round(0, 13) = (0, 0), and 1023 * 2^13 == q - 1 EXACTLY so
    /// Power2Round(q - 1, 13) = (1023, 0) with ||s2||inf = 1 <= eta = 2.
    ///
    /// This is not an argument about encodings: the fixture BUILDS the FIPS 204
    /// secret key from the witness and SIGNS a registrar-chosen challenge with
    /// the reference signer — which uses s1 in z = y + c*s1, s2 in the r0 check
    /// and t0 in the hint — and the resulting signature is accepted by the
    /// reference FIPS 204 verifier and by BOTH on-chain subjects, under the very
    /// key test_proof_of_possession_does_not_reject_a_degenerate_key registers.
    /// So NO proof about the secret key can be the degeneracy check; the check is
    /// the centred-lift floor (asserted below) or a binding to the KeyGen seed.
    function test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key() public {
        // (a) t1 = 0 — the same key the proof-of-possession case registers.
        _witnessCase(0, DEGEN_SEED2);
        // (b) t1 = 1023 — maximal value, maximal weight, every pkEncode byte
        //     0xff, and its witness is norm-conforming with ||s2||inf = 1.
        _witnessCase(1023, SEED);
    }

    /// One witness case: sign with the PUBLIC witness, then check the signature
    /// against FIPS and both subjects, and check the criterion section 3.1
    /// mandates still refuses the key.
    function _witnessCase(uint256 t1Val, string memory seedHex) internal {
        string[] memory c = new string[](6);
        c[0] = PY;
        c[1] = DEGEN2;
        c[2] = "witness";
        c[3] = vm.toString(t1Val);
        c[4] = seedHex;
        c[5] = POP_CHALLENGE_HEX; // the registrar's challenge, verbatim
        (
            bytes memory pkBlob,
            bytes memory sig,
            bytes memory pk,
            bool fipsOk,
            uint256 s1max,
            uint256 s2max,
            uint256 t0max,
            uint256 eta,
            bool relationHolds
        ) = abi.decode(vm.ffi(c), (bytes, bytes, bytes, bool, uint256, uint256, uint256, uint256, bool));

        assertEq(pk.length, 1312, "standard ML-DSA-44 pk size");
        assertEq(pkBlob.length, E2E_PK_SIZE, "cache size");
        assertEq(sig.length, 2420, "standard ML-DSA-44 signature size");

        // (1) the witness is a GENUINE ML-DSA secret key for this pk: the exact
        //     key relation holds in all 1,024 coefficients, and every norm is
        //     inside the FIPS 204 bound.
        assertTrue(relationHolds, "Power2Round(A*s1 + s2) == (t1, 0) everywhere");
        assertLe(s1max, eta, "||s1||inf <= eta");
        assertLe(s2max, eta, "||s2||inf <= eta");
        assertLe(t0max, 1 << 12, "||t0||inf <= 2^(d-1)");
        assertEq(s2max, t1Val == 0 ? 0 : 1, "the witness is (0,0,0) / (0,-1,0)");

        // (2) ... and it really signs: the reference FIPS 204 signer produced a
        //     signature over the registrar's challenge that everything accepts.
        assertTrue(fipsOk, "PoK: the reference FIPS 204 verifier accepts the witness signature");
        assertTrue(refv.verify(_refPk(pkBlob), POP_CHALLENGE, sig), "PoK: reference verifier accepts");
        assertTrue(shipped.verify(_shipPk(pkBlob), POP_CHALLENGE, sig), "PoK: shipped verifier accepts");

        // (3) the key is the degenerate one, and the criterion section 3.1
        //     mandates REFUSES it: not one centred lift exceeds gamma2.
        //     |lift(0)| = 0 and |lift(1023)| = 1 — BOTH ends of the range.
        for (uint256 i = 32; i < 1312; ++i) {
            assertEq(uint8(pk[i]), t1Val == 0 ? 0 : 0xff, "the key must be the degenerate one");
        }
        assertEq(_bigLiftCount(pk), 0, "every centred lift is tiny");
        assertTrue(_bigLiftCount(pk) < (4 * 256) / 2, "centred-lift criterion REFUSES this key");
    }

    // ================== the MAXIMAL degenerate key, and an ordinary sigma =====

    /// t1 = 1023 in all 1,024 coefficients: MAXIMAL coefficient value, MAXIMAL
    /// Hamming weight, every pkEncode byte 0xff — nothing resembling the t1 = 0
    /// fixture, so a "reject low-weight / near-zero t1" registrar rule passes
    /// it. It is key-free forgeable by the IDENTICAL z = 0 / h = 0 construction,
    /// because lift(1023) = -1 (1023 * 2^13 == q - 1), so
    /// ||c (*) lift(t1)||inf <= tau = 39, far inside gamma2. The CENTRED-LIFT
    /// criterion does refuse it; that is the point of stating the criterion on
    /// |lift| rather than on the coefficient value.
    function test_maximal_t1_key_is_key_free_forgeable() public {
        string[] memory c = new string[](5);
        c[0] = PY;
        c[1] = DEGEN2;
        c[2] = "maxdegen";
        c[3] = SEED;
        c[4] = MSG1_HEX;
        (bytes memory pkBlob, bytes memory sig, bytes memory pk, bool fipsOk) =
            abi.decode(vm.ffi(c), (bytes, bytes, bytes, bool));

        assertEq(pk.length, 1312, "standard ML-DSA-44 pk size");
        for (uint256 i = 32; i < 1312; ++i) {
            assertEq(uint8(pk[i]), 0xff, "t1 must be 1023 in every coefficient");
        }
        assertTrue(fipsOk, "the reference FIPS 204 verifier accepts the forgery");
        assertTrue(refv.verify(_refPk(pkBlob), MSG, sig), "reference accepts the maximal-t1 forgery");
        assertTrue(shipped.verify(_shipPk(pkBlob), MSG, sig), "shipped accepts the maximal-t1 forgery");
        assertEq(_bigLiftCount(pk), 0, "the centred-lift criterion refuses it: |lift(1023)| = 1");
    }

    /// The published degenerate-key fixture uses z = 0 and h = 0, the single most
    /// conspicuous signature in the space. A registrar that "hardens" its
    /// proof-of-possession by refusing conspicuous responses is NOT helped: the
    /// same key-free forgery closes with ||z||inf just under gamma1 - beta and
    /// 60 real hint bits. Conspicuousness is not the property that matters; the
    /// key is.
    function test_degenerate_forgery_with_an_ordinary_looking_signature() public {
        string[] memory c = new string[](5);
        c[0] = PY;
        c[1] = DEGEN2;
        c[2] = "fatsig";
        c[3] = SEED;
        c[4] = MSG1_HEX;
        (bytes memory pkBlob, bytes memory sig,, bool fipsOk, uint256 zmax, uint256 hweight) =
            abi.decode(vm.ffi(c), (bytes, bytes, bytes, bool, uint256, uint256));

        assertGt(zmax, 130000, "||z||inf is at the top of the legal window, not 0");
        assertLt(zmax, 130994, "... and still strictly inside gamma1 - beta");
        assertEq(hweight, 60, "60 real hint bits, not the all-zero hint");
        assertTrue(fipsOk, "the reference FIPS 204 verifier accepts");
        assertTrue(refv.verify(_refPk(pkBlob), MSG, sig), "reference accepts the ordinary-looking forgery");
        assertTrue(shipped.verify(_shipPk(pkBlob), MSG, sig), "shipped accepts the ordinary-looking forgery");
    }

    // ============================== non-canonical cache breaks lane bounds ====

    /// The matvec MAC kernels assume canonical (< q) cache coefficients. A
    /// non-canonical 32-bit field makes the folded subtraction KQ24 - c*t1
    /// underflow its 64-bit lane and borrow into the neighbour, corrupting the
    /// result — another reason the cache must be validated before it is streamed.
    function test_reference_lane_bounds_violated_by_noncanonical_cache() public pure {
        // c: packed 4 lanes/word, canonical. Only lane 0 of word 0 is set to q-1.
        uint256[] memory c = new uint256[](64);
        c[0] = 8380416;
        uint256[] memory tbuf = new uint256[](32);
        uint256 tPtr;
        assembly ("memory-safe") {
            tPtr := add(tbuf, 0x20)
        }

        // (i) canonical coefficient q-1: lane 0 = KQ24 - (q-1)^2 > 0, lanes 1..3
        //     keep the KQ24 offset exactly.
        tbuf[0] = 8380416;
        uint256[] memory acc1 = new uint256[](64);
        macSubCT1Lazy(acc1, c, tPtr);
        assertEq(acc1[0] & type(uint64).max, E2E_KQ24 - 8380416 * 8380416, "canonical lane 0");
        assertEq((acc1[0] >> 64) & type(uint64).max, E2E_KQ24, "canonical lane 1 = KQ24");

        // (ii) non-canonical coefficient 2^32-1: c*t1 = 2^55 > KQ24, the lane
        //      subtraction wraps and corrupts lane 1.
        tbuf[0] = 0xffffffff;
        uint256[] memory acc2 = new uint256[](64);
        macSubCT1Lazy(acc2, c, tPtr);
        assertTrue(8380416 * 0xffffffff > E2E_KQ24, "premise: product exceeds the lane offset");
        assertTrue((acc2[0] >> 64) & type(uint64).max != E2E_KQ24, "lane 1 corrupted by borrow");

        // (iii) the A*z MAC likewise: four column MACs with a 2^32-1 A field and a
        //       canonical z lane overrun the documented per-lane budget of < 2^49.
        uint256[] memory z = new uint256[](64);
        z[0] = 8380416;
        uint256[] memory abuf = new uint256[](32);
        abuf[0] = 0xffffffff;
        uint256 aPtr;
        assembly ("memory-safe") {
            aPtr := add(abuf, 0x20)
        }
        uint256[] memory acc3 = new uint256[](64);
        macCompactLazy(acc3, aPtr, z);
        macCompactLazy(acc3, aPtr, z);
        macCompactLazy(acc3, aPtr, z);
        macCompactLazy(acc3, aPtr, z);
        uint256 laneA = acc3[0] & type(uint64).max;
        assertEq(laneA, 4 * 8380416 * 0xffffffff, "four column MACs accumulate in lane 0");
        assertTrue(laneA > (1 << 49), "lane exceeds the documented < 2^49 invariant");
    }
}
