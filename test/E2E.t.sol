// SPDX-License-Identifier: MIT
// FILE: test/E2E.t.sol
//
// End-to-end acceptance, differential and gas tests for the shipped verifier
// (src/MLDSA44Verifier.sol) against the in-tree reference verifier
// (test/ZZZ_E2ERef.sol), on the SAME FFI-generated and NIST-KAT vectors, in
// the SAME call:
//   * FFI-signed vectors (two independent keys) verify TRUE in both, with
//     identical verdicts
//   * the NIST KAT vector verifies TRUE in both
//   * single-bit flips in c_tilde / z / h / message verify FALSE, with
//     identical verdicts
//   * the committed Keccak-f[1600] helper artifact (helpers/f1600_170.hex)
//     hashes to the verifier's pinned F1600_CODEHASH
//   * the real key-registration program (prepare/prepare.py) produces exactly
//     the blob the verifier accepts signatures against
//
// NOTE on the Keccak helper: ZZZ_E2ERef uses the vm.etch-only 25,357-byte
// f1600 build (44,750 gas/permutation) at the fixed _F1600_AT, while
// MLDSA44Verifier uses the EIP-170-deployable 21,622-byte batched build
// (tools/build_f1600_batch.py) deployed by real CREATE, whose one-call
// SHAKE256 entry point the verifier uses for mu and the final hash. The A/B
// numbers below therefore differ slightly from the helper choice alone; this
// is expected and is not corrected for.
pragma solidity ^0.8.25;

import {Test, console2} from "forge-std/Test.sol";
import {Constants} from "./seed.sol";
import {PythonSigner} from "./vendor/ZKNOX_PythonSigner.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {ZZZ_E2ERef, E2E_PK_SIZE} from "./ZZZ_E2ERef.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

contract E2ETest is Test {
    string constant PY = "pythonref/myenv/bin/python";
    string constant PKGEN = "tools/fixtures/e2e_pk.py";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant PREPARE = "prepare/prepare.py";
    string constant FFI_MSG_STR = "0x1111222233334444111122223333444411112222333344441111222233334444";
    bytes constant FFI_MSG = hex"1111222233334444111122223333444411112222333344441111222233334444";
    string constant SEED2 = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";

    /// keccak256 of helpers/f1600_170.hex (decoded); must equal the
    /// F1600_CODEHASH constant pinned inside src/MLDSA44Verifier.sol.
    bytes32 constant HELPER_CODEHASH = 0x4afb4435879cdf8e50474c7aab2bc3a679caed432550ad6dba64f509309a817b;

    /// THE PUBLISHED HEADLINE GAS FIGURE, and the only mechanical guard on it.
    /// It is the first number in README.md and appears five times in
    /// docs/EXPLAINER.md. Without this constant the only check would be
    /// VERIFY_GAS_CEILING below — 39% above the real value, so a 38%
    /// regression would leave every check green and the README silently
    /// false. `formal/hypotheses.py` re-derives the documents' number
    /// FROM THIS CONSTANT (`authoritative_counts()['verify_gas']`), and
    /// test_e2e_10 asserts THIS CONSTANT against the EVM, so the chain runs
    /// documents -> this line -> the measured artefact with nothing typed twice.
    ///
    /// Measured: 1,226,311 on forge 1.4.2-nightly c808c4cd, solc 0.8.30, evm
    /// osaka.
    uint256 constant VERIFY_GAS_MEASURED = 1_226_311;

    /// The band the assertion allows, in basis points of VERIFY_GAS_MEASURED.
    /// +-0.5% absorbs solc/EVM version drift (which moves this number by tens of
    /// gas, not by tens of thousands) and still fails on any real regression:
    /// the 38% one the loose ceiling would have admitted misses by 75x.
    uint256 constant VERIFY_GAS_BAND_BP = 50;

    /// Outer regression ceiling, kept as a second, coarser net so a failure
    /// says which kind of drift it is.
    uint256 constant VERIFY_GAS_CEILING = 1_700_000;

    // standard 1312-byte FIPS 204 ML-DSA-44 public key, NIST KAT count 0
    // (pythonref/assets/PQCsignKAT_Dilithium2.rsp — the key vecgen.py `kat`
    // signs under; also embedded in test/ZZZ_e2eref.t.sol)
    bytes constant KAT_PK =
        hex"dc7bc9a2e0b6dc66823ae4fbde971c0cfc46f9d96bbfbeebb3470ae0a5a0139fdd6a6ce5bc76e94faa9e9250abd4cee02cf1ee46a8e99ce12d7395781fa7519021273da3365519724efbe279add6c35f92c9d42b032832f1bf29ebbecd3ec87a3af3da33c611f7f35fa35acab174024f118979e23bf2fe069269a2ec45fbc1b9c1fb0e1f05486a6a833eb48adc2960641d9af6eb8b7381b1ec55d889f26b084ddfa1c9ed9b962d342694cede83825309d9db6bd6ba7582132534861e44a04388a694242411761d34e7c085d282b723c65948a2ac764d9702bd8ed7fe9931d7d8704a39e6508844f3f84843c305594fe6e5404e08f18ed039ac6563cbaa34b0ca38320299d6256ec0f78d421f088159d49dc439cbc539a55884a3eb4efc9cf190b42f713441cb97004245d41437a39b7b77fc602fbbfd619a42363714b265173cae68fd8a1b3ca2bd30ae60c53e5604577a4a3b1f1506e697c37432dbd883553aac8d382a3d250cf5b29e4d1be2cbcd531ff0e07e89c1f7dbc8d4529aeebe55b5ce4d0214bfdec69e080bd3ef36cca6a54933f1ef2f37867c0d38fd5865b87929115808c7e2595458e993bacc6c5a3b9f5025001e9b41447708bfbaa0462efa63876c42f769908b432f5485508a393224960551d77eadfaf4411cbc49fdff46f2f155ddd6ec30867905b709888ca0f30f935fb8d7f4803cfc7a5f7790ca181d99ca21f2621d69a5c6d49c76b4969da62740a378470332b30947ab31ccdb9ba0c7b625879eec4bd81f0200ba23504a7dc3b118bc2ab1145df13af3c8cc39f577873b84911b3d85fbbf4cb19e4d36b10a938eeb78b599dc86615fd6cec6eb7b8f7afa5f6d6be19ea81630d36ccfb2f487de50d0cf46da8d3fe3512812043c0e3ef2d7231fb0b0a35a0fb283be30a1247780f30ae0294e8b6f5897383edb895595f577524df54593cdf927b4967616ee3913e4d6b29b0dbd7c33a2a45e4ef1b1954ea5d91ce37efc1302e7ce02a97395565da2a5c5d3fdb0d87684e9b1c0ad07ec33df2dfad528e2ea0966d2a47dd5ee88e77d653c0d004fab0165f0757c4da40af327e7192536c79947a80a827aa2107dacfae3debfc8fad3d6e08076d938c510a276bdf6721a1f087cb169515028ad5ce27a1047abd92809934ca63b893f71f9a34a99c0fd30310c47e9aa37394d0ab73b254d3ca69d9c5549c9479aae24264ac5ea64d3fd821c3962ec77e709f9d30bc7b65a52e48c16e80603558caca1811411c3155d1f949fc9cf9aa9385a7199e99be77a66fad7eed91258de55b2c4c83f9a050adebea5f09758f40dac4a1c394ee8d687879150d26426895ab1938e14ae11b376254c91fc6130436996f8ed43bd27be20ec9067111c116ec94cc2b06cc91a13c5d10bbd7eecea4792f17b2b77631ef145e9fb41a83eaa11c2b72a48fb90fdbd88644c4edf8ab20dce3118364b276ac1237b36c8926e346aab5a111aa0bf341c518b7bff9e9dbb8bcb4728601b3760663e67650331e6fb54ac82fc414cb8ddfc160a25311ec5272de46217fef8b992ff89754fbee351f21bb90b6c97078b510c983350681266c8fed1f0583c5151e7b8fe3b7292319699687cc6b641fdbd689428543bc0fa1facc109de65b62784c2d985ab15d77d3af12af6d03e8d1859a553688584d75ef673a1de74093ee108c761fff32c217c231b0e2953daf521429264c0963bc8a5cdeddc617a7285b934ea51ddb5cdab23bcede86be36e001bc65c65e9a1c94baff4fab8eb5f8ed42ec377423633fe00049142467c47c5d58a7202c8e9104841c1f7f380145a6a0a828c570235e507ae5868a6062f722bb98ff6be";

    ZZZ_E2ERef ref;
    MLDSA44Verifier opt;
    PythonSigner pythonSigner;
    address f1600;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        f1600 = deployF1600_170();
        ref = new ZZZ_E2ERef();
        opt = new MLDSA44Verifier(f1600);
        pythonSigner = new PythonSigner();
    }

    // ------------------------------------------------------------------ utils

    function _deployData(bytes memory data) internal returns (address ptr) {
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "pk data contract deploy failed");
    }

    /// pk data contract for the reference verifier: the raw 20,544-byte payload
    function _deployRefPk(bytes memory blob) internal returns (address) {
        return _deployData(blob);
    }

    /// pk data contract for the shipped verifier: 0x00 (EIP-3541 prefix) || payload
    function _deployOptPk(bytes memory blob) internal returns (address) {
        return _deployData(bytes.concat(hex"00", blob));
    }

    function _pkBlob(string memory mode, string memory hexArg) internal returns (bytes memory blob) {
        string[] memory cmds = new string[](4);
        cmds[0] = PY;
        cmds[1] = PKGEN;
        cmds[2] = mode;
        cmds[3] = hexArg;
        blob = vm.ffi(cmds);
        assertEq(blob.length, E2E_PK_SIZE, "pk blob size");
    }

    /// FFI fixture: pk blob + fresh deterministic NIST-mode signature for `seed`
    function _seedFixture(string memory seedStr)
        internal
        returns (bytes memory blob, bytes memory sig)
    {
        blob = _pkBlob("seed", seedStr);
        (bytes memory cTilde, bytes memory z, bytes memory hh) =
            pythonSigner.sign("pythonref", FFI_MSG_STR, "NIST", seedStr);
        sig = abi.encodePacked(cTilde, z, hh);
        assertEq(sig.length, 2420, "sig length");
    }

    /// (sig, pkBlob, msg) fixture from tools/fixtures/vecgen.py
    function _vecgen(string memory mode, string memory seedHex, string memory msgHex)
        internal
        returns (bytes memory sig, bytes memory blob, bytes memory msg_)
    {
        bool isKat = keccak256(bytes(mode)) == keccak256("kat");
        string[] memory cmds = new string[](isKat ? 3 : 5);
        cmds[0] = PY;
        cmds[1] = VECGEN;
        cmds[2] = mode;
        if (!isKat) {
            cmds[3] = seedHex;
            cmds[4] = msgHex;
        }
        (sig, blob, msg_) = abi.decode(vm.ffi(cmds), (bytes, bytes, bytes));
        assertEq(sig.length, 2420, "vecgen sig length");
        assertEq(blob.length, E2E_PK_SIZE, "vecgen blob length");
    }

    function _flip(bytes memory b, uint256 i) internal pure returns (bytes memory c) {
        c = bytes.concat(b);
        c[i] = bytes1(uint8(c[i]) ^ 0x01);
    }

    // ================================================== acceptance + A/B gas

    /// FFI-signed vector must verify TRUE in both verifiers; the shipped
    /// verifier's end-to-end verify() gas is measured on the same external-call
    /// bracket as the reference and bounded by VERIFY_GAS_CEILING.
    function test_e2e_10_seed_vector_accepts_and_gas() public {
        (bytes memory blob, bytes memory sig) = _seedFixture(Constants.SEED_POSTQUANTUM_STR);
        address refPk = _deployRefPk(blob);
        address optPk = _deployOptPk(blob);

        uint256 g0 = gasleft();
        bool okRef = ref.verify(refPk, FFI_MSG, sig);
        uint256 gRef = g0 - gasleft();

        g0 = gasleft();
        bool okOpt = opt.verify(optPk, FFI_MSG, sig);
        uint256 gOpt = g0 - gasleft();

        assertTrue(okRef, "reference verifier must accept the FFI vector");
        assertTrue(okOpt, "shipped verifier must accept the FFI vector");
        console2.log("E2E gas, ZZZ_E2ERef.verify()     :", gRef);
        console2.log("E2E gas, MLDSA44Verifier.verify():", gOpt);
        assertLt(gOpt, VERIFY_GAS_CEILING, "shipped verify() gas above the regression ceiling");

        // ... and the PUBLISHED figure, within +-0.5%. README.md and
        // docs/EXPLAINER.md quote VERIFY_GAS_MEASURED; this is what makes that
        // quote a measurement rather than a memory.
        uint256 slack = (VERIFY_GAS_MEASURED * VERIFY_GAS_BAND_BP) / 10_000;
        assertGe(gOpt, VERIFY_GAS_MEASURED - slack, "shipped verify() gas below the published figure's band");
        assertLe(gOpt, VERIFY_GAS_MEASURED + slack, "shipped verify() gas above the published figure's band");
    }

    /// NIST KAT vector (vecgen.py `kat`, PQCsignKAT_Dilithium2.rsp count 0)
    /// must verify TRUE in both verifiers.
    function test_e2e_11_nist_kat_vector_accepts() public {
        (bytes memory sig, bytes memory blob, bytes memory msg_) = _vecgen("kat", "", "");
        bool okRef = ref.verify(_deployRefPk(blob), msg_, sig);
        bool okOpt = opt.verify(_deployOptPk(blob), msg_, sig);
        assertTrue(okRef, "reference verifier must accept the NIST KAT vector");
        assertTrue(okOpt, "shipped verifier must accept the NIST KAT vector");
    }

    /// generic (sig, pkBlob, msg) vector from vecgen.py `seed`: cross-checks
    /// the vecgen signer against both verifiers on a second key.
    function test_e2e_12_vecgen_seed_vector_accepts() public {
        (bytes memory sig, bytes memory blob, bytes memory msg_) = _vecgen("seed", SEED2, FFI_MSG_STR);
        assertEq(keccak256(msg_), keccak256(FFI_MSG), "vecgen must echo the message");
        assertTrue(opt.verify(_deployOptPk(blob), msg_, sig), "shipped verifier must accept the vecgen vector");
        assertTrue(ref.verify(_deployRefPk(blob), msg_, sig), "reference disagrees on the vecgen vector");
    }

    /// |M| = 734 makes the mu preimage exactly 800 bytes — the one length the
    /// helper's batched SHAKE256 entry point cannot express (an 800-byte
    /// calldata is dispatched as a raw permutation). The verifier must take
    /// the lane-level-sponge fallback and still accept; the neighbouring
    /// lengths 733/735 exercise the batched path right at the boundary.
    function test_e2e_14_mu_batch_boundary_734B_message() public {
        for (uint256 n = 733; n <= 735; n++) {
            bytes memory m = new bytes(n);
            for (uint256 i = 0; i < n; i++) {
                m[i] = keccak256(abi.encode("mu-boundary", n, i / 32))[i % 32];
            }
            (bytes memory sig, bytes memory blob, bytes memory msg_) =
                _vecgen("seed", SEED2, vm.toString(m));
            assertEq(keccak256(msg_), keccak256(m), "vecgen must echo the message");
            assertTrue(
                opt.verify(_deployOptPk(blob), msg_, sig),
                "shipped verifier must accept at the mu batch boundary"
            );
            assertTrue(
                ref.verify(_deployRefPk(blob), msg_, sig),
                "reference disagrees at the mu batch boundary"
            );
        }
    }

    /// a second, independent key signed through the Python reference signer:
    /// catches anything accidentally specialised to the first blob.
    function test_e2e_13_second_key_accepts() public {
        (bytes memory blob, bytes memory sig) = _seedFixture(SEED2);
        assertTrue(opt.verify(_deployOptPk(blob), FFI_MSG, sig), "second-key vector must verify TRUE");
        assertTrue(ref.verify(_deployRefPk(blob), FFI_MSG, sig), "reference disagrees on the second key");
    }

    // ======================================================== negative tests

    /// single-bit flips in c_tilde / z / h and in the message must be rejected,
    /// and the two verifiers must agree on every verdict; malformed inputs
    /// (wrong signature length, code-less pk pointer) must be rejected too.
    function test_e2e_20_negative_mutations() public {
        (bytes memory blob, bytes memory sig) = _seedFixture(Constants.SEED_POSTQUANTUM_STR);
        address refPk = _deployRefPk(blob);
        address optPk = _deployOptPk(blob);

        // byte 0 = c_tilde, byte 100 = z, byte 2400 = h
        uint256[3] memory pos = [uint256(0), 100, 2400];
        for (uint256 k = 0; k < 3; ++k) {
            bytes memory bad = _flip(sig, pos[k]);
            bool a = ref.verify(refPk, FFI_MSG, bad);
            bool b = opt.verify(optPk, FFI_MSG, bad);
            assertFalse(b, "shipped verifier accepted a bit-flipped signature");
            assertEq(a, b, "verdicts diverged on a bit-flipped signature");
        }

        bytes memory badMsg = _flip(FFI_MSG, 3);
        assertFalse(opt.verify(optPk, badMsg, sig), "accepted a modified message");
        assertEq(
            ref.verify(refPk, badMsg, sig),
            opt.verify(optPk, badMsg, sig),
            "verdicts diverged on a modified message"
        );

        // wrong signature length and a code-less pk pointer both reject
        assertFalse(opt.verify(optPk, FFI_MSG, bytes.concat(sig, hex"00")), "accepted a 2421-byte signature");
        assertFalse(opt.verify(address(0xdead), FFI_MSG, sig), "accepted a code-less pk pointer");
    }

    // ================================================= deployment artifacts

    /// Binds the committed helper artifact to the verifier's pin: the decoded
    /// helpers/f1600_170.hex must hash to F1600_CODEHASH (the constant the
    /// MLDSA44Verifier constructor and every verify() call check), and the
    /// helper deployed by the test harness must carry exactly that code.
    function test_helper_hex_matches_pin() public {
        string[] memory cmds = new string[](2);
        cmds[0] = "/bin/cat";
        cmds[1] = "helpers/f1600_170.hex";
        bytes memory runtime = vm.ffi(cmds); // ffi hex-decodes the file content
        assertEq(runtime.length, 21622, "helper runtime size");
        assertEq(keccak256(runtime), HELPER_CODEHASH, "committed helper hex does not hash to the pin");
        assertEq(f1600.codehash, HELPER_CODEHASH, "deployed helper code hash does not match the pin");
        assertEq(keccak256(f1600.code), keccak256(runtime), "deployed helper differs from the committed hex");
    }

    /// Runs the REAL key-registration program (prepare/prepare.py) on the raw
    /// 1312-byte NIST KAT public key and checks that
    ///   * its output is exactly 0x00 || the e2e_pk.py payload (the layout the
    ///     verifier documents), and
    ///   * a data contract deployed verbatim from its output makes the shipped
    ///     verifier accept the KAT signature.
    function test_prepare_program_builds_accepted_blob() public {
        // prepare.py: 1312-byte pk in, 20,545-byte deployable blob out
        string[] memory cmds = new string[](3);
        cmds[0] = PY;
        cmds[1] = PREPARE;
        cmds[2] = vm.toString(KAT_PK);
        bytes memory blob = vm.ffi(cmds);
        assertEq(blob.length, E2E_PK_SIZE + 1, "prepare.py blob size (0x00 prefix + payload)");

        // byte-identical to the e2e_pk.py payload with the EIP-3541 prefix
        bytes memory payload = _pkBlob("pk", vm.toString(KAT_PK));
        assertEq(
            keccak256(blob),
            keccak256(bytes.concat(hex"00", payload)),
            "prepare.py output != 0x00 || e2e_pk.py payload"
        );

        // ... and to the payload vecgen.py derives for the same KAT key
        (bytes memory sig, bytes memory vblob, bytes memory msg_) = _vecgen("kat", "", "");
        assertEq(keccak256(vblob), keccak256(payload), "vecgen KAT payload != e2e_pk.py payload");

        // deploy prepare.py's output verbatim and verify the KAT vector
        address pkAddr = _deployData(blob);
        assertTrue(opt.verify(pkAddr, msg_, sig), "shipped verifier must accept the KAT vector on prepare.py's blob");
    }
}
