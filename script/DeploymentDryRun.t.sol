// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: script/DeploymentDryRun.t.sol
//
// Dry run of the whole deployment, inside `forge test`, with no network.
//
// It drives the three deployment scripts in order -- DeployHelper,
// DeployPkBlob, DeployVerifier -- and then verifies a real FIPS 204 ML-DSA-44
// signature through the contracts those scripts just deployed. If this passes,
// the deployment path works.
//
//   forge test --match-path 'script/*' -vv
//
// The signature is NIST KAT count 0 (pythonref/assets/PQCsignKAT_Dilithium2.rsp,
// the same vector test/E2E.t.sol uses), pinned here as constants so the dry run
// needs no signing tools. The public-key blob comes from running the real
// prepare/prepare.py, which is standard library only, so `python3` on PATH is
// the only external dependency; the virtualenv the rest of the suite needs is
// not required here.
//
// WHY THE SCRIPTS ARE DRIVEN THROUGH deploy(...) AND NOT run(). run() reads its
// inputs from environment variables, and environment variables are global to the
// forge process while test functions run in parallel, so a test that set them
// would race with its neighbours. Each script therefore has a deploy(...) entry
// point taking the same values explicitly, and run() is a one-line wrapper that
// reads the environment and calls it. Everything load-bearing -- the initcode
// wrappers, the size and code-hash assertions, the constructor, verify() -- is
// below deploy(). The environment and file-reading half of run() is covered by
// actually running `forge script` under FOUNDRY_PROFILE=script.
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {DeployHelper} from "./DeployHelper.s.sol";
import {DeployPkBlob} from "./DeployPkBlob.s.sol";
import {DeployVerifier} from "./DeployVerifier.s.sol";
import {DeployAll} from "./DeployAll.s.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

/// @dev arbitrary code whose EXTCODEHASH is not the helper's.
contract NotTheHelper {
    function noop() external pure returns (uint256) {
        return 42;
    }
}

contract DeploymentDryRunTest is Test {
    string constant HELPER_HEX_PATH = "helpers/f1600_170.hex";
    uint256 constant F1600_RUNTIME_SIZE = 21_622;
    uint256 constant PK_BLOB_SIZE = 20_545;
    bytes32 constant F1600_CODEHASH =
        0x4afb4435879cdf8e50474c7aab2bc3a679caed432550ad6dba64f509309a817b;

    /// standard 1,312-byte FIPS 204 ML-DSA-44 public key, NIST KAT count 0.
    bytes constant KAT_PK =
        hex"dc7bc9a2e0b6dc66823ae4fbde971c0cfc46f9d96bbfbeebb3470ae0a5a0139fdd6a6ce5bc76e94faa9e9250abd4cee02cf1ee46a8e99ce12d739578"
        hex"1fa7519021273da3365519724efbe279add6c35f92c9d42b032832f1bf29ebbecd3ec87a3af3da33c611f7f35fa35acab174024f118979e23bf2fe06"
        hex"9269a2ec45fbc1b9c1fb0e1f05486a6a833eb48adc2960641d9af6eb8b7381b1ec55d889f26b084ddfa1c9ed9b962d342694cede83825309d9db6bd6"
        hex"ba7582132534861e44a04388a694242411761d34e7c085d282b723c65948a2ac764d9702bd8ed7fe9931d7d8704a39e6508844f3f84843c305594fe6"
        hex"e5404e08f18ed039ac6563cbaa34b0ca38320299d6256ec0f78d421f088159d49dc439cbc539a55884a3eb4efc9cf190b42f713441cb97004245d414"
        hex"37a39b7b77fc602fbbfd619a42363714b265173cae68fd8a1b3ca2bd30ae60c53e5604577a4a3b1f1506e697c37432dbd883553aac8d382a3d250cf5"
        hex"b29e4d1be2cbcd531ff0e07e89c1f7dbc8d4529aeebe55b5ce4d0214bfdec69e080bd3ef36cca6a54933f1ef2f37867c0d38fd5865b87929115808c7"
        hex"e2595458e993bacc6c5a3b9f5025001e9b41447708bfbaa0462efa63876c42f769908b432f5485508a393224960551d77eadfaf4411cbc49fdff46f2"
        hex"f155ddd6ec30867905b709888ca0f30f935fb8d7f4803cfc7a5f7790ca181d99ca21f2621d69a5c6d49c76b4969da62740a378470332b30947ab31cc"
        hex"db9ba0c7b625879eec4bd81f0200ba23504a7dc3b118bc2ab1145df13af3c8cc39f577873b84911b3d85fbbf4cb19e4d36b10a938eeb78b599dc8661"
        hex"5fd6cec6eb7b8f7afa5f6d6be19ea81630d36ccfb2f487de50d0cf46da8d3fe3512812043c0e3ef2d7231fb0b0a35a0fb283be30a1247780f30ae029"
        hex"4e8b6f5897383edb895595f577524df54593cdf927b4967616ee3913e4d6b29b0dbd7c33a2a45e4ef1b1954ea5d91ce37efc1302e7ce02a97395565d"
        hex"a2a5c5d3fdb0d87684e9b1c0ad07ec33df2dfad528e2ea0966d2a47dd5ee88e77d653c0d004fab0165f0757c4da40af327e7192536c79947a80a827a"
        hex"a2107dacfae3debfc8fad3d6e08076d938c510a276bdf6721a1f087cb169515028ad5ce27a1047abd92809934ca63b893f71f9a34a99c0fd30310c47"
        hex"e9aa37394d0ab73b254d3ca69d9c5549c9479aae24264ac5ea64d3fd821c3962ec77e709f9d30bc7b65a52e48c16e80603558caca1811411c3155d1f"
        hex"949fc9cf9aa9385a7199e99be77a66fad7eed91258de55b2c4c83f9a050adebea5f09758f40dac4a1c394ee8d687879150d26426895ab1938e14ae11"
        hex"b376254c91fc6130436996f8ed43bd27be20ec9067111c116ec94cc2b06cc91a13c5d10bbd7eecea4792f17b2b77631ef145e9fb41a83eaa11c2b72a"
        hex"48fb90fdbd88644c4edf8ab20dce3118364b276ac1237b36c8926e346aab5a111aa0bf341c518b7bff9e9dbb8bcb4728601b3760663e67650331e6fb"
        hex"54ac82fc414cb8ddfc160a25311ec5272de46217fef8b992ff89754fbee351f21bb90b6c97078b510c983350681266c8fed1f0583c5151e7b8fe3b72"
        hex"92319699687cc6b641fdbd689428543bc0fa1facc109de65b62784c2d985ab15d77d3af12af6d03e8d1859a553688584d75ef673a1de74093ee108c7"
        hex"61fff32c217c231b0e2953daf521429264c0963bc8a5cdeddc617a7285b934ea51ddb5cdab23bcede86be36e001bc65c65e9a1c94baff4fab8eb5f8e"
        hex"d42ec377423633fe00049142467c47c5d58a7202c8e9104841c1f7f380145a6a0a828c570235e507ae5868a6062f722bb98ff6be";

    /// the 2,420-byte signature for KAT_MSG under KAT_PK.
    bytes constant KAT_SIG =
        hex"66af1f4837b08a2d04be10bf5d5337d9bcc8973840cbb5f63cfafa528db58821bf24c1038c54ff2acacfa9997f33eb234155eb3506e52907aca0af8e"
        hex"aa946d4c5aa162cfa72197691f4a71c71556003707e3cac85c3f162cc60795ab42ff6f4a0abf2a6cee57db3302985cf6a3e701c687a9984b4bedbc65"
        hex"08ae8e2feb0b7a8a1731373c3c5246f8c3d940cb5737c3ef170a73f63b06a765b5f7fe45e4dc5fa65e4398473540d54274b5b97934e2fbbd77a00316"
        hex"e27619b5ea2a18ad4542d75fbb57d906cc0694d39e8590aab94dc6513b635ce51ef186d5a69f20edc76479f437ba1f676d49529ff19909d9750ffb05"
        hex"68bd137299747816d4f07a9bda579b56f9054cbe583266141c33b3153f25b12fdcadead75090903d0c029d4e4b4763c42ac3819f55a79e3e288da080"
        hex"3835424acffb1bb55fa7da0855b455d0447bce46b444e72a056f4e889860c936bcbe1bf2978ed2833b71ed722e1d15095b1317a9fcdd17865dcf84c4"
        hex"747c3c4b33b94da8ac6ab479bfeddbd2cb404b13ce580f0c55c6b8782de192cabcfe1e211d04d5f38ae9516be5910fd725d30dc145b8c0baa091c4a1"
        hex"1fe44d62eb72851fe9986f58dbf466d4b2f36509a8189a946a6eba4d0634a777425721bd736f777adbb8cd02db21b9c6df9c69f9575fbbdf0a67d765"
        hex"f2f2371cd8538a107c2d8de9726f034be0417a5c054493c9e671717ad6ade55ee17e4e6d2c1693d1f019b4f4212dddc9133a4038c3367d026e8e000c"
        hex"1a465a0e737ef504937bfa645f63aa81b3945c9ba91b2cbb6e96a7fee850de61e314f772592b52cf493d51202311eeb49171739d807ce3ab405ec845"
        hex"a63ffb6a3bb46a5711432b2f367124bbecfa64404fe065ebe60864c0148f7850152e80c760d01bbc57e7dbef9de65927c24be17faed82bec1b6973d5"
        hex"57b8267ca41a850616a6998b0750357dc330ec40447c5170ee751ba8c2101e4f29bf21db14dcf661526479a947c60c28c7874f76b9e99699cf9df71a"
        hex"5005622630601b7781cd0e7557a2d6bd0b771a423391c4480b0e8e8ac0ce4f68db7cc5eea3524923498685d7c9c45ac9d7b0c3827641c9f257ca6d3a"
        hex"caf04c59fde7d3b15d24989d76355e319c433b82e78883dadfa4a5a95fd861d1b6114c583f4915b948c72ba66ffc2ab4713aa05544b23ae7c83c75ab"
        hex"5549994a077086c71a2d7fa3088c8c8c0e0a27f85277a620bcf7a9360af6964eacd6c44a96c63581e9d576158c406c714ecf7285849ca3265e0857ee"
        hex"f43dbb95546d0cbde2881725d5e0bebd45cbaaf80173d2aa96240fe337ac86578538c37510c79fcbf1043d263f167177d723e9d5abdf56fdbb51b4f5"
        hex"78749c3a77e4ab60ca032015968b9bf0d469d73ba4bd66929fdaac294b910db9d58d49ddd2d1e7ef9c4eb81361eae786d839cf2e95e4f9614192a249"
        hex"253c919ce2391022db95a598ba6bf01a2c7cd0f1609e7ffde0f87d12faccd822e0eef8de1e0ea0ac1230363eec1633081af9905e87c3e56a214a6014"
        hex"18fd5c3910d6ad9cc121ed0ede6fca0909ddd0cc26d528004a707923d3ac6fef0110a09d3e329b6f93bc3cdd7d6cd7d62b811d8fac3848a8969b778f"
        hex"a77dc416b18a7878040cfd4b1d8db530c7e7f5c859cc56570cd3ca8b4d18358ad737d6b902b24493c33ff9ed6eb2ddc06c928e3e7b790acad77bc1fe"
        hex"9eed09d7948c4a5d338408b361b10eaee9dbcf50ba8867a5f108019f58a0813e6ade68ded0638493631ee40c8049c34150d91ed3734731777502238e"
        hex"55f01cd88caaaa25e8abddbdbb4bc6554d5a373d610bbcdb05af600d9c1d9ef1b3d43720f043c106ee93a102ee7f5333c6fd0040add9e9d7faf952ff"
        hex"f2a718d01e45028f228355eac6a92e626b63521c4990f7fab6cd2e8fcb74f359ca299af447fadd9fa5006088a4f041cccdac2579df3b8983257f7112"
        hex"45e85539f9d14c4b99d0627fb41543c75b6f76b87f1dc1b6a141de13be4cfe133074cba338063cf76f8647ed5e5482456e6cb3fcedb9cfe7a762b161"
        hex"82c5408c8f5f13c29cf88772f13feb8f9e0e051307af2ea46f37a069275465ad5576887d06cbdf5ac9b9bdbd6895839bee685de8b24890b848409a21"
        hex"b38bbdd29c441782bf3a603306153c47345e5f58e8b3b236266a3f215269aa90a59ca2d5efab60fd662ebea0130bb0f6fb1cabc604eb70515bceabfb"
        hex"4f17abf40964e527f85eaaa632775dee85a31cb18d63c8d550596c72fe94e8cd55df95c2fd10c4cfcf8811a3204c8f5c57204bccfb457fcdd0f7569c"
        hex"147b416ece6cfa813de0f8b7b48f885162fc067ee6e609158607e1843bd5559c3383cd920f833995c5a85f98b6f6bd152b83fd112353c5a97cb6fca5"
        hex"4ea56ce75abe92df29531a6118cd31d7e58f3f1b298eae463035b098d288e314a5a315308da372bde335e9e363486b2ce7195f25588fbc3a6c358dff"
        hex"1bab71cfc9f82a68de8afcf95931bcd8e4c2115bd8d237eb56a3d57bb4c51641c4b5198bb9b65aadbe16063bdb3a67b13b32b6cc13e914e2281724f7"
        hex"6a35422e3448e8c3d244c681dc72fc65cf38ed647e40bca73d01a8f23274cc0619ee9a6ce49dfd8dd639a246b72564aafc0177ae46bcc3d0829f3f24"
        hex"816bfe809af5c1286a089369f59606f95f0f27e8800f9dc8effeb055731cf75f01533b2508b88a4b628936f021ca20276dc46c677cc22eee6ae22245"
        hex"a2616db14e0d84ce4f58b0e81c51ac330ff5925b5e5ea75d753a34d6da010ddb5874787fcc02c9ae4eea39fe47268b04af9b57c50c7dd03008a4c9bf"
        hex"f3973e51a5cd1cfd970c6da8438d1d9ba3cd197a0029ff94d02157391ca4da1ebd3ac11ad701c71ceff7b0dc245c2d9eca1c27c55816ca5740d688f9"
        hex"2e4f64147c32d6eb6ff2a54b1d1995a31c8c81a0cb709fb760b184392a48991d3f80d69a272a7aa8f829c12244f4a5418ef36d40fbc6bea4e33a1aaa"
        hex"a6d2361e03d2487aaffe6bbe42b56befe78c35f2a8367ad83a67ee99316c496f94cf17d3d35b0fb371868c19c991b721f59de6641880a59045e2ffb1"
        hex"82e0f51c9e536d7c72cec698975a0d06187c0ef38b716aaa71ba701678a3cf51d8aa33c944c767ed07249b894699a650f57b7ca56b6d77ce4c79496a"
        hex"cbe340f7792ca4116f7cce12bcc0aec3642de421aa91860ba042d4dae4dccfbdc3cd2c72abee2b005307565ff4b33cec2f112dc83b509ae88d31a421"
        hex"aba7830f1a1e2b3df212a550890d469827acfdc6020c91234d2d18a6b266262e689689e268d4617b59b11f3842506fc5eaf53dc80172f0911b284855"
        hex"a1a3a4aaaeb0b1e2e6fc1f3045484b5960728c93b2c5dce8ff0e1e3138415890aeb8cc122529737a898fa5a9acdaebeef1f200000000000000000000"
        hex"000000000000000000000000000000000e1d2736";

    /// the 33-byte KAT message.
    bytes constant KAT_MSG =
        hex"d81c4d8d734fcbfbeade3d3f8a039faa2a2c9957e835ad55b22e75bf57bb556ac8";

    bytes helperRuntime;
    bytes pkBlobBytes;

    function setUp() public {
        // The two artifacts a deployer starts from.
        helperRuntime = _catHex(HELPER_HEX_PATH);
        assertEq(helperRuntime.length, F1600_RUNTIME_SIZE, "helper runtime size");
        assertEq(
            keccak256(helperRuntime), F1600_CODEHASH, "committed helper hex does not match the pin"
        );

        pkBlobBytes = _prepare(KAT_PK);
        assertEq(pkBlobBytes.length, PK_BLOB_SIZE, "prepare.py blob size");
        assertEq(pkBlobBytes[0], bytes1(0x00), "prepare.py must emit the EIP-3541 prefix byte");
    }

    // ------------------------------------------------------------- fixtures

    /// Read a hex artifact without fs_permissions; vm.ffi hex-decodes stdout.
    /// Same trick as test/E2E.t.sol:test_helper_hex_matches_pin().
    function _catHex(string memory path) internal returns (bytes memory) {
        string[] memory cmds = new string[](2);
        cmds[0] = "/bin/cat";
        cmds[1] = path;
        return vm.ffi(cmds);
    }

    /// Run the REAL key-registration program on a standard 1,312-byte public key.
    function _prepare(bytes memory pk) internal returns (bytes memory) {
        string[] memory cmds = new string[](3);
        cmds[0] = "python3";
        cmds[1] = "prepare/prepare.py";
        cmds[2] = vm.toString(pk);
        return vm.ffi(cmds);
    }

    // ================================================== the dry run itself ===

    /// The documented three-command deployment, then a real signature through
    /// the contracts it produced.
    function test_dryrun_three_steps_then_verify_a_real_signature() public {
        // step 1 -- the Keccak-f[1600] helper
        address helper = new DeployHelper().deploy(helperRuntime);
        assertEq(helper.code.length, F1600_RUNTIME_SIZE, "helper code size");
        assertEq(helper.codehash, F1600_CODEHASH, "helper code hash must match the verifier's pin");

        // step 2 -- one public key
        address pkBlob = new DeployPkBlob().deploy(pkBlobBytes);
        assertEq(pkBlob.code.length, PK_BLOB_SIZE, "pk blob code size");

        // step 3 -- the verifier. constructor(address f1600Helper)
        MLDSA44Verifier verifier = new DeployVerifier().deploy(helper);

        // the payoff: a genuine signature verifies through all three
        assertTrue(verifier.verify(pkBlob, KAT_MSG, KAT_SIG), "KAT signature must verify TRUE");

        // and a one-bit change to the message does not
        bytes memory tampered = bytes.concat(KAT_MSG);
        tampered[0] = bytes1(uint8(tampered[0]) ^ 0x01);
        assertFalse(
            verifier.verify(pkBlob, tampered, KAT_SIG), "tampered message must verify FALSE"
        );
    }

    /// The same through the one-command DeployAll path.
    function test_dryrun_deploy_all_in_one_run() public {
        (address helper, address pkBlob, address verifier) =
            new DeployAll().deploy(helperRuntime, pkBlobBytes, address(0));

        assertEq(helper.codehash, F1600_CODEHASH, "helper code hash");
        assertEq(pkBlob.code.length, PK_BLOB_SIZE, "pk blob code size");
        assertTrue(
            MLDSA44Verifier(verifier).verify(pkBlob, KAT_MSG, KAT_SIG),
            "KAT signature must verify TRUE through DeployAll"
        );
    }

    /// One helper serves any number of verifiers, and a second helper deployed
    /// from the same bytes lands at a different address with the same code hash.
    /// This is what makes step 1 a once-per-chain job.
    function test_dryrun_one_helper_serves_many_verifiers() public {
        address helper = new DeployHelper().deploy(helperRuntime);
        address pkBlob = new DeployPkBlob().deploy(pkBlobBytes);

        MLDSA44Verifier a = new DeployVerifier().deploy(helper);
        MLDSA44Verifier b = new DeployVerifier().deploy(helper);
        assertTrue(address(a) != address(b), "two distinct verifiers");
        assertTrue(a.verify(pkBlob, KAT_MSG, KAT_SIG), "first verifier accepts");
        assertTrue(b.verify(pkBlob, KAT_MSG, KAT_SIG), "second verifier accepts");

        address helper2 = new DeployHelper().deploy(helperRuntime);
        assertTrue(helper2 != helper, "second helper at a different address");
        assertEq(helper2.codehash, helper.codehash, "identical code hash");
        assertTrue(
            new DeployVerifier().deploy(helper2).verify(pkBlob, KAT_MSG, KAT_SIG),
            "a verifier on the second helper accepts the same signature"
        );
    }

    // ============================================== the loud failure modes ===

    /// A blob of the wrong size is refused before anything is deployed. This is
    /// the failure a deployer would otherwise not notice: the verifier's
    /// extcodesize check makes a wrong-size blob return FALSE for every
    /// signature rather than revert, so the key would look like it was
    /// registered and then reject everything.
    function test_pk_blob_missing_the_prefix_byte_is_refused() public {
        // the payload without prepare.py's leading 0x00 byte: 20,544 bytes
        bytes memory short_ = new bytes(PK_BLOB_SIZE - 1);
        for (uint256 i = 0; i < PK_BLOB_SIZE - 1; ++i) {
            short_[i] = pkBlobBytes[i + 1];
        }
        DeployPkBlob s = new DeployPkBlob();
        vm.expectRevert();
        s.deploy(short_);
    }

    /// One byte too many is refused as well.
    function test_pk_blob_one_byte_too_long_is_refused() public {
        DeployPkBlob s = new DeployPkBlob();
        vm.expectRevert();
        s.deploy(bytes.concat(pkBlobBytes, hex"00"));
    }

    /// The raw 1,312-byte public key, handed over without running prepare.py.
    function test_raw_public_key_instead_of_a_blob_is_refused() public {
        DeployPkBlob s = new DeployPkBlob();
        vm.expectRevert();
        s.deploy(KAT_PK);
    }

    /// A truncated or otherwise wrong helper runtime never reaches the chain:
    /// the hash is checked against the verifier's pin first.
    function test_wrong_helper_runtime_is_refused() public {
        bytes memory truncated = new bytes(F1600_RUNTIME_SIZE - 1);
        for (uint256 i = 0; i < F1600_RUNTIME_SIZE - 1; ++i) {
            truncated[i] = helperRuntime[i];
        }
        DeployHelper s = new DeployHelper();
        vm.expectRevert();
        s.deploy(truncated);
    }

    /// A right-size helper runtime with one byte flipped fails the hash check.
    function test_corrupted_helper_runtime_is_refused() public {
        bytes memory corrupted = bytes.concat(helperRuntime);
        corrupted[1000] = bytes1(uint8(corrupted[1000]) ^ 0x01);
        DeployHelper s = new DeployHelper();
        vm.expectRevert();
        s.deploy(corrupted);
    }

    /// A helper address that does not carry the pinned code is refused before
    /// the constructor gets a chance to revert with BadHelper().
    function test_verifier_refuses_a_helper_with_the_wrong_code() public {
        DeployVerifier s = new DeployVerifier();
        address wrong = address(new NotTheHelper());
        vm.expectRevert();
        s.deploy(wrong);
    }

    /// A codeless helper address is refused too.
    function test_verifier_refuses_a_codeless_helper() public {
        DeployVerifier s = new DeployVerifier();
        vm.expectRevert();
        s.deploy(address(0xdead));
    }
}
