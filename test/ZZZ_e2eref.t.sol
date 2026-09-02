// SPDX-License-Identifier: MIT
// FILE: test/ZZZ_e2eref.t.sol
// End-to-end checks + gas measurement for the in-tree REFERENCE ML-DSA-44
// verifier (test/ZZZ_E2ERef.sol). Checks:
//   1. FFI-signed vector (pythonref sig_sol.py, NIST mode, SEED_POSTQUANTUM) verifies TRUE
//   2. NIST KAT vector (pk/tr/sig/msg from PQCsignKAT_Dilithium2.rsp count 0) verifies TRUE
//   3. single-bit flips in c_tilde / z / h / message each verify FALSE
// plus kernel-level checks: SampleInBall equivalence vs
// test/vendor/ZKNOX_SampleInBall.sol, strict-vs-upstream unpackZ agreement on
// a real signature, and canonical handling of z == 0 coefficients (which the
// upstream kernels encode as q, not 0).
// pk blobs are produced by tools/fixtures/e2e_pk.py via vm.ffi and deployed
// as raw data contracts (tr || t1hat_compact || Ahat_compact, 20544 bytes).
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {Constants} from "./seed.sol";
import {PythonSigner} from "./vendor/ZKNOX_PythonSigner.sol";
import {sampleInBallNist} from "./vendor/ZKNOX_SampleInBall.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {unpackZFast2} from "./ZZZ_decode2.t.sol";
import {nttFwV3, nttFwTable} from "./ZZZ_NttVariants.sol";
import {nttInvV3, iunpackCoeffs, nttInvTable} from "./ZZZ_InvNtt.sol";
import {
    ZZZ_E2ERef,
    unpackZStrict,
    sampleInBallE2E,
    packFromFlat,
    E2E_Q,
    E2E_PK_SIZE
} from "./ZZZ_E2ERef.sol";

contract E2ERefTest is Test {
    ZZZ_E2ERef verifier;
    PythonSigner pythonSigner;

    // Both paths are REPO-RELATIVE: vm.ffi runs with cwd = the foundry project
    // root. The pk-blob generator lives in the repo at
    // tools/fixtures/e2e_pk.py (CLI + output ABI: tools/fixtures/README.md).
    string constant PY = "pythonref/myenv/bin/python";
    string constant PKGEN = "tools/fixtures/e2e_pk.py";

    string constant FFI_MSG_STR = "0x1111222233334444111122223333444411112222333344441111222233334444";
    bytes constant FFI_MSG = hex"1111222233334444111122223333444411112222333344441111222233334444";

    // ---- NIST KAT vector (pythonref/assets/PQCsignKAT_Dilithium2.rsp, count 0) ----
    bytes constant KAT_PK =
        hex"dc7bc9a2e0b6dc66823ae4fbde971c0cfc46f9d96bbfbeebb3470ae0a5a0139fdd6a6ce5bc76e94faa9e9250abd4cee02cf1ee46a8e99ce12d7395781fa7519021273da3365519724efbe279add6c35f92c9d42b032832f1bf29ebbecd3ec87a3af3da33c611f7f35fa35acab174024f118979e23bf2fe069269a2ec45fbc1b9c1fb0e1f05486a6a833eb48adc2960641d9af6eb8b7381b1ec55d889f26b084ddfa1c9ed9b962d342694cede83825309d9db6bd6ba7582132534861e44a04388a694242411761d34e7c085d282b723c65948a2ac764d9702bd8ed7fe9931d7d8704a39e6508844f3f84843c305594fe6e5404e08f18ed039ac6563cbaa34b0ca38320299d6256ec0f78d421f088159d49dc439cbc539a55884a3eb4efc9cf190b42f713441cb97004245d41437a39b7b77fc602fbbfd619a42363714b265173cae68fd8a1b3ca2bd30ae60c53e5604577a4a3b1f1506e697c37432dbd883553aac8d382a3d250cf5b29e4d1be2cbcd531ff0e07e89c1f7dbc8d4529aeebe55b5ce4d0214bfdec69e080bd3ef36cca6a54933f1ef2f37867c0d38fd5865b87929115808c7e2595458e993bacc6c5a3b9f5025001e9b41447708bfbaa0462efa63876c42f769908b432f5485508a393224960551d77eadfaf4411cbc49fdff46f2f155ddd6ec30867905b709888ca0f30f935fb8d7f4803cfc7a5f7790ca181d99ca21f2621d69a5c6d49c76b4969da62740a378470332b30947ab31ccdb9ba0c7b625879eec4bd81f0200ba23504a7dc3b118bc2ab1145df13af3c8cc39f577873b84911b3d85fbbf4cb19e4d36b10a938eeb78b599dc86615fd6cec6eb7b8f7afa5f6d6be19ea81630d36ccfb2f487de50d0cf46da8d3fe3512812043c0e3ef2d7231fb0b0a35a0fb283be30a1247780f30ae0294e8b6f5897383edb895595f577524df54593cdf927b4967616ee3913e4d6b29b0dbd7c33a2a45e4ef1b1954ea5d91ce37efc1302e7ce02a97395565da2a5c5d3fdb0d87684e9b1c0ad07ec33df2dfad528e2ea0966d2a47dd5ee88e77d653c0d004fab0165f0757c4da40af327e7192536c79947a80a827aa2107dacfae3debfc8fad3d6e08076d938c510a276bdf6721a1f087cb169515028ad5ce27a1047abd92809934ca63b893f71f9a34a99c0fd30310c47e9aa37394d0ab73b254d3ca69d9c5549c9479aae24264ac5ea64d3fd821c3962ec77e709f9d30bc7b65a52e48c16e80603558caca1811411c3155d1f949fc9cf9aa9385a7199e99be77a66fad7eed91258de55b2c4c83f9a050adebea5f09758f40dac4a1c394ee8d687879150d26426895ab1938e14ae11b376254c91fc6130436996f8ed43bd27be20ec9067111c116ec94cc2b06cc91a13c5d10bbd7eecea4792f17b2b77631ef145e9fb41a83eaa11c2b72a48fb90fdbd88644c4edf8ab20dce3118364b276ac1237b36c8926e346aab5a111aa0bf341c518b7bff9e9dbb8bcb4728601b3760663e67650331e6fb54ac82fc414cb8ddfc160a25311ec5272de46217fef8b992ff89754fbee351f21bb90b6c97078b510c983350681266c8fed1f0583c5151e7b8fe3b7292319699687cc6b641fdbd689428543bc0fa1facc109de65b62784c2d985ab15d77d3af12af6d03e8d1859a553688584d75ef673a1de74093ee108c761fff32c217c231b0e2953daf521429264c0963bc8a5cdeddc617a7285b934ea51ddb5cdab23bcede86be36e001bc65c65e9a1c94baff4fab8eb5f8ed42ec377423633fe00049142467c47c5d58a7202c8e9104841c1f7f380145a6a0a828c570235e507ae5868a6062f722bb98ff6be";
    bytes constant KAT_TR =
        hex"2ef757da47649d9f63fa03f1bf6fe6bc7c62971a98a2bd9d36eb0ec43ad4e9d940df3bb5874f5c92192aa31e0535d3cf70950bba858d11a688eaf854f63ecfc5";
    bytes constant KAT_MSG = hex"d81c4d8d734fcbfbeade3d3f8a039faa2a2c9957e835ad55b22e75bf57bb556ac8";
    bytes constant KAT_SIG =
        hex"66af1f4837b08a2d04be10bf5d5337d9bcc8973840cbb5f63cfafa528db58821bf24c1038c54ff2acacfa9997f33eb234155eb3506e52907aca0af8eaa946d4c5aa162cfa72197691f4a71c71556003707e3cac85c3f162cc60795ab42ff6f4a0abf2a6cee57db3302985cf6a3e701c687a9984b4bedbc6508ae8e2feb0b7a8a1731373c3c5246f8c3d940cb5737c3ef170a73f63b06a765b5f7fe45e4dc5fa65e4398473540d54274b5b97934e2fbbd77a00316e27619b5ea2a18ad4542d75fbb57d906cc0694d39e8590aab94dc6513b635ce51ef186d5a69f20edc76479f437ba1f676d49529ff19909d9750ffb0568bd137299747816d4f07a9bda579b56f9054cbe583266141c33b3153f25b12fdcadead75090903d0c029d4e4b4763c42ac3819f55a79e3e288da0803835424acffb1bb55fa7da0855b455d0447bce46b444e72a056f4e889860c936bcbe1bf2978ed2833b71ed722e1d15095b1317a9fcdd17865dcf84c4747c3c4b33b94da8ac6ab479bfeddbd2cb404b13ce580f0c55c6b8782de192cabcfe1e211d04d5f38ae9516be5910fd725d30dc145b8c0baa091c4a11fe44d62eb72851fe9986f58dbf466d4b2f36509a8189a946a6eba4d0634a777425721bd736f777adbb8cd02db21b9c6df9c69f9575fbbdf0a67d765f2f2371cd8538a107c2d8de9726f034be0417a5c054493c9e671717ad6ade55ee17e4e6d2c1693d1f019b4f4212dddc9133a4038c3367d026e8e000c1a465a0e737ef504937bfa645f63aa81b3945c9ba91b2cbb6e96a7fee850de61e314f772592b52cf493d51202311eeb49171739d807ce3ab405ec845a63ffb6a3bb46a5711432b2f367124bbecfa64404fe065ebe60864c0148f7850152e80c760d01bbc57e7dbef9de65927c24be17faed82bec1b6973d557b8267ca41a850616a6998b0750357dc330ec40447c5170ee751ba8c2101e4f29bf21db14dcf661526479a947c60c28c7874f76b9e99699cf9df71a5005622630601b7781cd0e7557a2d6bd0b771a423391c4480b0e8e8ac0ce4f68db7cc5eea3524923498685d7c9c45ac9d7b0c3827641c9f257ca6d3acaf04c59fde7d3b15d24989d76355e319c433b82e78883dadfa4a5a95fd861d1b6114c583f4915b948c72ba66ffc2ab4713aa05544b23ae7c83c75ab5549994a077086c71a2d7fa3088c8c8c0e0a27f85277a620bcf7a9360af6964eacd6c44a96c63581e9d576158c406c714ecf7285849ca3265e0857eef43dbb95546d0cbde2881725d5e0bebd45cbaaf80173d2aa96240fe337ac86578538c37510c79fcbf1043d263f167177d723e9d5abdf56fdbb51b4f578749c3a77e4ab60ca032015968b9bf0d469d73ba4bd66929fdaac294b910db9d58d49ddd2d1e7ef9c4eb81361eae786d839cf2e95e4f9614192a249253c919ce2391022db95a598ba6bf01a2c7cd0f1609e7ffde0f87d12faccd822e0eef8de1e0ea0ac1230363eec1633081af9905e87c3e56a214a601418fd5c3910d6ad9cc121ed0ede6fca0909ddd0cc26d528004a707923d3ac6fef0110a09d3e329b6f93bc3cdd7d6cd7d62b811d8fac3848a8969b778fa77dc416b18a7878040cfd4b1d8db530c7e7f5c859cc56570cd3ca8b4d18358ad737d6b902b24493c33ff9ed6eb2ddc06c928e3e7b790acad77bc1fe9eed09d7948c4a5d338408b361b10eaee9dbcf50ba8867a5f108019f58a0813e6ade68ded0638493631ee40c8049c34150d91ed3734731777502238e55f01cd88caaaa25e8abddbdbb4bc6554d5a373d610bbcdb05af600d9c1d9ef1b3d43720f043c106ee93a102ee7f5333c6fd0040add9e9d7faf952fff2a718d01e45028f228355eac6a92e626b63521c4990f7fab6cd2e8fcb74f359ca299af447fadd9fa5006088a4f041cccdac2579df3b8983257f711245e85539f9d14c4b99d0627fb41543c75b6f76b87f1dc1b6a141de13be4cfe133074cba338063cf76f8647ed5e5482456e6cb3fcedb9cfe7a762b16182c5408c8f5f13c29cf88772f13feb8f9e0e051307af2ea46f37a069275465ad5576887d06cbdf5ac9b9bdbd6895839bee685de8b24890b848409a21b38bbdd29c441782bf3a603306153c47345e5f58e8b3b236266a3f215269aa90a59ca2d5efab60fd662ebea0130bb0f6fb1cabc604eb70515bceabfb4f17abf40964e527f85eaaa632775dee85a31cb18d63c8d550596c72fe94e8cd55df95c2fd10c4cfcf8811a3204c8f5c57204bccfb457fcdd0f7569c147b416ece6cfa813de0f8b7b48f885162fc067ee6e609158607e1843bd5559c3383cd920f833995c5a85f98b6f6bd152b83fd112353c5a97cb6fca54ea56ce75abe92df29531a6118cd31d7e58f3f1b298eae463035b098d288e314a5a315308da372bde335e9e363486b2ce7195f25588fbc3a6c358dff1bab71cfc9f82a68de8afcf95931bcd8e4c2115bd8d237eb56a3d57bb4c51641c4b5198bb9b65aadbe16063bdb3a67b13b32b6cc13e914e2281724f76a35422e3448e8c3d244c681dc72fc65cf38ed647e40bca73d01a8f23274cc0619ee9a6ce49dfd8dd639a246b72564aafc0177ae46bcc3d0829f3f24816bfe809af5c1286a089369f59606f95f0f27e8800f9dc8effeb055731cf75f01533b2508b88a4b628936f021ca20276dc46c677cc22eee6ae22245a2616db14e0d84ce4f58b0e81c51ac330ff5925b5e5ea75d753a34d6da010ddb5874787fcc02c9ae4eea39fe47268b04af9b57c50c7dd03008a4c9bff3973e51a5cd1cfd970c6da8438d1d9ba3cd197a0029ff94d02157391ca4da1ebd3ac11ad701c71ceff7b0dc245c2d9eca1c27c55816ca5740d688f92e4f64147c32d6eb6ff2a54b1d1995a31c8c81a0cb709fb760b184392a48991d3f80d69a272a7aa8f829c12244f4a5418ef36d40fbc6bea4e33a1aaaa6d2361e03d2487aaffe6bbe42b56befe78c35f2a8367ad83a67ee99316c496f94cf17d3d35b0fb371868c19c991b721f59de6641880a59045e2ffb182e0f51c9e536d7c72cec698975a0d06187c0ef38b716aaa71ba701678a3cf51d8aa33c944c767ed07249b894699a650f57b7ca56b6d77ce4c79496acbe340f7792ca4116f7cce12bcc0aec3642de421aa91860ba042d4dae4dccfbdc3cd2c72abee2b005307565ff4b33cec2f112dc83b509ae88d31a421aba7830f1a1e2b3df212a550890d469827acfdc6020c91234d2d18a6b266262e689689e268d4617b59b11f3842506fc5eaf53dc80172f0911b284855a1a3a4aaaeb0b1e2e6fc1f3045484b5960728c93b2c5dce8ff0e1e3138415890aeb8cc122529737a898fa5a9acdaebeef1f200000000000000000000000000000000000000000000000000000e1d2736";

    function setUp() public {
        verifier = new ZZZ_E2ERef();
        pythonSigner = new PythonSigner();
        // pre-deploy the Keccak-f[1600] helper so its (one-time) deployment is
        // outside every gas bracket; the account is still COLD inside each
        // measured top-level call, so the 2600-gas cold access is included.
        vm.etch(_F1600_AT, _F1600_CODE);
    }

    // ------------------------------------------------------------------ utils

    /// deploy `data` as a raw data contract (no prefix): initcode
    /// PUSH2 len PUSH1 0x0e PUSH1 0 CODECOPY PUSH2 len PUSH1 0 RETURN || data
    function _deployData(bytes memory data) internal returns (address ptr) {
        require(data.length < 24576, "data too large for EIP-170");
        bytes memory initCode = abi.encodePacked(
            bytes1(0x61), uint16(data.length), hex"600e600039", bytes1(0x61), uint16(data.length), hex"6000f3", data
        );
        assembly ("memory-safe") {
            ptr := create(0, add(initCode, 32), mload(initCode))
        }
        require(ptr != address(0), "pk data contract deploy failed");
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

    /// FFI fixture: pk data contract for SEED_POSTQUANTUM + a fresh NIST-mode signature.
    function _ffiFixture() internal returns (address pkAddr, bytes memory sig) {
        pkAddr = _deployData(_pkBlob("seed", Constants.SEED_POSTQUANTUM_STR));
        (bytes memory cTilde, bytes memory z, bytes memory h) =
            pythonSigner.sign("pythonref", FFI_MSG_STR, "NIST", Constants.SEED_POSTQUANTUM_STR);
        sig = abi.encodePacked(cTilde, z, h);
        assertEq(sig.length, 2420, "sig length");
    }

    function _clone(bytes memory b) internal pure returns (bytes memory) {
        return bytes.concat(b);
    }

    // ------------------------------------------------ CHECK 1 + gas measurement

    function test_e2eref_gate1_ffi_vector_and_gas() public {
        (address pkAddr, bytes memory sig) = _ffiFixture();

        uint256 g0 = gasleft();
        bool ok = verifier.verify(pkAddr, FFI_MSG, sig);
        uint256 used = g0 - gasleft();
        assertTrue(ok, "CHECK 1: FFI-signed vector must verify TRUE");
        console.log("E2E gas, external verify() call (FFI vector):", used);

        // coarse internal stage split (separate, unmeasured call)
        (bool ok2, uint256[10] memory p) = verifier.verifyProfiled(pkAddr, FFI_MSG, sig);
        assertTrue(ok2);
        console.log("  stage pk-load + sig decode (z,h):", p[0] - p[1]);
        console.log("  stage mu = SHAKE256(tr||M', 64):", p[1] - p[2]);
        console.log("  stage SampleInBall + pack + cNTT:", p[2] - p[3]);
        console.log("  stage z pack + fwd NTT x4:", p[3] - p[4]);
        console.log("  stage matvec + c*t1 + inv NTT x4:", p[4] - p[5]);
        console.log("  stage UseHint + w1Encode:", p[5] - p[6]);
        console.log("  stage final SHAKE256(mu||w1, 32):", p[6] - p[7]);
        console.log("  internal stage sum:", p[0] - p[7]);

        // strict unpackZ agrees with the audited repo kernel on a real
        // signature, modulo the canonical q -> 0 mapping.
        bytes memory zB = new bytes(2304);
        for (uint256 i = 0; i < 2304; ++i) {
            zB[i] = sig[32 + i];
        }
        (uint256[] memory zs, bool okS) = unpackZStrict(zB);
        (uint256[] memory zf, bool okF) = unpackZFast2(zB);
        assertTrue(okS && okF, "norm");
        for (uint256 i = 0; i < 1024; ++i) {
            uint256 expect = zf[i] == E2E_Q ? 0 : zf[i];
            assertEq(zs[i], expect, "strict vs repo unpackZ");
        }
    }

    // ------------------------------------------------------------ CHECK 2: KAT

    function test_e2eref_gate2_nist_kat() public {
        bytes memory blob = _pkBlob("pk", vm.toString(KAT_PK));

        // cross-check: tr recomputed by the helper == tr constant of the KAT test
        bytes memory trGot = new bytes(64);
        assembly ("memory-safe") {
            mcopy(add(trGot, 32), add(blob, 32), 64)
        }
        assertEq(keccak256(trGot), keccak256(KAT_TR), "tr mismatch vs the NIST KAT tr");

        address pkAddr = _deployData(blob);
        uint256 g0 = gasleft();
        bool ok = verifier.verify(pkAddr, KAT_MSG, KAT_SIG);
        uint256 used = g0 - gasleft();
        assertTrue(ok, "CHECK 2: NIST KAT vector must verify TRUE");
        console.log("E2E gas, external verify() call (KAT vector, 33-byte msg):", used);
    }

    // ---------------------------------------------------- CHECK 3: bit flips

    function test_e2eref_gate3_negative_bitflips() public {
        (address pkAddr, bytes memory sig) = _ffiFixture();
        assertTrue(verifier.verify(pkAddr, FFI_MSG, sig), "sanity");

        bytes memory s = _clone(sig); // flip one bit in c_tilde
        s[0] = bytes1(uint8(s[0]) ^ 0x01);
        assertFalse(verifier.verify(pkAddr, FFI_MSG, s), "c_tilde bit flip must fail");

        s = _clone(sig); // flip one bit in z
        s[100] = bytes1(uint8(s[100]) ^ 0x01);
        assertFalse(verifier.verify(pkAddr, FFI_MSG, s), "z bit flip must fail");

        s = _clone(sig); // flip one bit in h
        s[2336] = bytes1(uint8(s[2336]) ^ 0x01);
        assertFalse(verifier.verify(pkAddr, FFI_MSG, s), "h bit flip must fail");

        bytes memory m = _clone(FFI_MSG); // flip one bit in the message
        m[0] = bytes1(uint8(m[0]) ^ 0x01);
        assertFalse(verifier.verify(pkAddr, m, sig), "message bit flip must fail");
    }

    // ------------------------------------------- kernel-level component checks

    /// SampleInBall equivalence vs the vendored upstream NIST implementation across several
    /// challenge values (identical XOF stream consumption incl. sign bits).
    function test_e2eref_sampleinball_matches_repo() public view {
        for (uint256 k = 0; k < 8; ++k) {
            bytes32 ct = k == 0
                ? bytes32(hex"cc501e9f471a004d2d3f60894d12aad3114e8abf62e413a800b7e7987ec5100b")
                : keccak256(abi.encodePacked("e2e-sib", k));
            uint256[] memory a = sampleInBallE2E(ct);
            uint256[] memory b = sampleInBallNist(abi.encodePacked(ct), 39, E2E_Q);
            for (uint256 i = 0; i < 256; ++i) {
                assertEq(a[i], b[i], "SampleInBall mismatch");
            }
        }
    }

    /// z == 0 coefficients: the repo kernels (unpackZ / unpackZFast2) decode the
    /// packed field v == gamma1 == 131072 (i.e. z == 0) to the NON-canonical
    /// value q. The strict kernel must yield canonical 0 (the packed V3 NTTs'
    /// verified lane bounds require inputs < q), and the packed NTT round-trip
    /// must be exact on polynomials containing zeros. (A valid FFI signature
    /// containing a zero z coefficient occurs w.p. ~0.4%/signature, so this is
    /// exercised at kernel level rather than with a signed vector.)
    function test_e2eref_zero_z_coefficient_canonical() public view {
        uint256[] memory v = new uint256[](1024);
        for (uint256 t = 0; t < 1024; ++t) {
            // sprinkle exact zeros (v == 131072) among small +/- values
            if (t % 5 == 0) v[t] = 131072; // z == 0
            else if (t % 5 == 1) v[t] = 79; // z == +130993 (max strict-valid)
            else if (t % 5 == 2) v[t] = 262065; // z == -130993 (min strict-valid)
            else v[t] = 131072 - (t % 1000) - 1; // small positive z
        }
        bytes memory zB = _encodeZ(v);
        (uint256[] memory zs, bool okS) = unpackZStrict(zB);
        assertTrue(okS, "strict norm must pass");
        (uint256[] memory zf, bool okF) = unpackZFast2(zB);
        assertTrue(okF, "repo norm must pass");
        for (uint256 t = 0; t < 1024; ++t) {
            uint256 z = v[t] < 131072 ? 131072 - v[t] : E2E_Q + 131072 - v[t]; // repo map
            if (v[t] == 131072) {
                assertEq(zf[t], E2E_Q, "repo kernel encodes z==0 as q");
                assertEq(zs[t], 0, "strict kernel must canonicalize z==0 to 0");
            } else {
                assertEq(zs[t], z, "strict kernel value");
                assertEq(zf[t], z, "repo kernel value");
            }
            assertTrue(zs[t] < E2E_Q, "strict output canonical");
        }
        // packed NTT round-trip stays exact with zero coefficients present
        uint256[] memory prof = new uint256[](10);
        for (uint256 j = 0; j < 4; ++j) {
            uint256[] memory w = packFromFlat(zs, j << 8);
            w = nttInvV3(nttFwV3(w, prof, nttFwTable()), prof, nttInvTable());
            uint256[] memory back = iunpackCoeffs(w);
            for (uint256 i = 0; i < 256; ++i) {
                assertEq(back[i], zs[(j << 8) + i], "NTT round-trip with zeros");
            }
        }
    }

    /// strict norm boundary: |z| == gamma1 - beta == 130994 (v == 78 / 262066)
    /// is rejected by the strict kernel (FIPS 204: require ||z||inf < gamma1-beta)
    /// but was accepted by the repo kernels.
    function test_e2eref_strict_norm_boundary() public pure {
        uint256[] memory v = new uint256[](1024);
        for (uint256 t = 0; t < 1024; ++t) {
            v[t] = 131072;
        }
        v[3] = 78; // z == +130994 == gamma1 - beta
        (, bool okS) = unpackZStrict(_encodeZ(v));
        assertFalse(okS, "strict kernel must reject |z| == gamma1-beta");
        (, bool okF) = unpackZFast2(_encodeZ(v));
        assertTrue(okF, "repo kernel accepted the boundary (documented)");
        v[3] = 262066; // z == -(gamma1 - beta)
        (, bool okS2) = unpackZStrict(_encodeZ(v));
        assertFalse(okS2, "strict kernel must reject -(gamma1-beta)");
        v[3] = 79; // z == +130993, last strictly valid value
        (, bool okS3) = unpackZStrict(_encodeZ(v));
        assertTrue(okS3, "strict kernel must accept |z| == gamma1-beta-1");
    }

    /// FIPS 204 18-bit little-endian bit packing of 1024 raw fields (test-only).
    function _encodeZ(uint256[] memory v) internal pure returns (bytes memory zB) {
        zB = new bytes(2304);
        assembly ("memory-safe") {
            let d := add(zB, 32)
            for { let t := 0 } lt(t, 1024) { t := add(t, 1) } {
                let bitOff := mul(t, 18)
                let p := add(d, shr(3, bitOff))
                // read-modify-write 32 bytes big-endian: OR the field into the
                // top bits (big-endian bit order within the little-endian byte
                // stream: byte b, bit k  <=>  LE bit 8b+k)
                let sh := and(bitOff, 7)
                let cur := mload(p)
                // assemble 3 little-endian bytes locally
                let fld := shl(sh, and(mload(add(add(v, 32), shl(5, t))), 0x3ffff))
                let b0 := and(fld, 0xff)
                let b1 := and(shr(8, fld), 0xff)
                let b2 := and(shr(16, fld), 0xff)
                let b3 := and(shr(24, fld), 0xff)
                cur := or(cur, shl(248, b0))
                cur := or(cur, shl(240, b1))
                cur := or(cur, shl(232, b2))
                cur := or(cur, shl(224, b3))
                mstore(p, cur)
            }
        }
    }
}
