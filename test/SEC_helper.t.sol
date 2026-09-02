// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC_helper.t.sol
//
// Security tests for the Keccak-f[1600] helper binding of the shipped
// MLDSA44Verifier.
//
// The permutation lives in a SEPARATE contract (helpers/f1600_170.hex, deployed
// by deployF1600_170()) and every sponge call is
//     staticcall(gas(), helper, st, 800, st, 800)   with returndatasize()==800.
// The verifier binds that helper by CONTENT: its constructor and every verify()
// call assert
//     helper.codehash == F1600_CODEHASH
// so the code at the helper address is authenticated, not merely its location.
//
// What is tested here:
//   * a hostile helper (any code whose hash differs) is rejected at construction;
//   * a codeless helper address is rejected at construction;
//   * replacing the helper's code AFTER deployment (metamorphic substitution) is
//     caught on the next verify() — even when the replacement computes the
//     permutation correctly, because the pin is by content, not behaviour;
//   * the pin is content-addressed: the identical runtime at a DIFFERENT address
//     is accepted;
//   * the sponge itself fails closed when the helper is missing, reverting, or
//     returns the wrong number of bytes (the returndatasize()==800 check);
//   * a genuine (pk, message, signature) triple verifies TRUE with the honest
//     helper (control).
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";
import {f1600Fast170} from "../src/FastKeccak170.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {_F1600_CODE} from "./ZZZ_FastKeccak.sol";

/// @dev arbitrary non-helper code (its EXTCODEHASH is not F1600_CODEHASH).
contract SECDummy {
    function noop() external pure returns (uint256) {
        return 42;
    }
}

/// @dev a helper that returns the WRONG number of bytes (799, not 800).
contract SECShortHelper {
    fallback() external {
        assembly {
            return(0, 799)
        }
    }
}

/// @dev a helper that reverts on every call.
contract SECRevertHelper {
    fallback() external {
        assembly {
            revert(0, 0)
        }
    }
}

/// @dev thin wrapper so a reverting f1600Fast170 can be observed across an
///      external call boundary (vm.expectRevert needs an external target).
contract SpongeProbe {
    function perm(address helper) external view {
        uint256[25] memory st;
        f1600Fast170(st, helper);
    }
}

contract SECHelperTest is Test {
    // vm.ffi runs with cwd = the foundry project root.
    string constant PY = "pythonref/myenv/bin/python";
    string constant VECGEN = "tools/fixtures/vecgen.py";
    string constant SEED = "cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe";
    string constant MSG1_HEX = "0x1111222233334444111122223333444411112222333344441111222233334444";

    bytes32 constant F1600_CODEHASH = 0x4afb4435879cdf8e50474c7aab2bc3a679caed432550ad6dba64f509309a817b;

    address f1600;
    MLDSA44Verifier shipped;

    bytes sig;
    bytes msg_;
    address shipPk;

    function setUp() public {
        f1600 = deployF1600_170();
        shipped = new MLDSA44Verifier(f1600);
        bytes memory pkBlob;
        (sig, pkBlob, msg_) = _vec(SEED, MSG1_HEX);
        shipPk = _deployData(bytes.concat(hex"00", pkBlob));
    }

    // --------------------------------------------------------------- fixtures

    function _vec(string memory seedHex, string memory msgHex)
        internal
        returns (bytes memory s, bytes memory pkBlob, bytes memory m)
    {
        string[] memory cmds = new string[](5);
        cmds[0] = PY;
        cmds[1] = VECGEN;
        cmds[2] = "seed";
        cmds[3] = seedHex;
        cmds[4] = msgHex;
        (s, pkBlob, m) = abi.decode(vm.ffi(cmds), (bytes, bytes, bytes));
    }

    /// deploy `data` verbatim as contract code via a real CREATE.
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

    // ================================================= honest control =======

    function test_honest_helper_verifies_a_valid_tuple() public view {
        assertEq(f1600.codehash, F1600_CODEHASH, "helper bound by content hash");
        assertTrue(shipped.verify(shipPk, msg_, sig), "genuine tuple must verify TRUE");
    }

    // ============================================= constructor rejection =====

    /// a helper whose code hash differs is rejected at construction.
    function test_constructor_rejects_hostile_helper() public {
        address hostile = address(new SECDummy());
        assertTrue(hostile.codehash != F1600_CODEHASH, "hostile code hash differs");
        vm.expectRevert(MLDSA44Verifier.BadHelper.selector);
        new MLDSA44Verifier(hostile);
    }

    /// a codeless address (EXTCODEHASH == 0) is rejected at construction.
    function test_constructor_rejects_codeless_helper() public {
        address empty = address(0xdead);
        assertEq(empty.code.length, 0, "precondition: codeless");
        vm.expectRevert(MLDSA44Verifier.BadHelper.selector);
        new MLDSA44Verifier(empty);
    }

    // =============================================== content-addressed pin ===

    /// the binding is by CONTENT, not address: the identical runtime deployed at
    /// a fresh address is accepted and verifies the same tuple.
    function test_pin_is_content_based_not_address_based() public {
        address f2 = deployF1600_170();
        assertTrue(f2 != f1600, "second helper at a different address");
        assertEq(f2.codehash, f1600.codehash, "identical code hash");

        MLDSA44Verifier v2 = new MLDSA44Verifier(f2);
        assertTrue(v2.verify(shipPk, msg_, sig), "same-bytes helper at a new address verifies");
    }

    // ======================================= metamorphic substitution ========

    /// replacing the helper's code after deployment is caught on the next
    /// verify(), even when the replacement is a byte-for-byte DIFFERENT but
    /// functionally CORRECT permutation. This closes the hostile-helper
    /// message-substitution vector: no helper the verifier did not commit to can
    /// ever be used, stealthy or not.
    function test_metamorphic_substitution_is_caught_even_if_functionally_correct() public {
        // sanity: honest helper accepts
        assertTrue(shipped.verify(shipPk, msg_, sig), "sanity with the committed helper");

        // _F1600_CODE is an independent, byte-different Keccak-f[1600] build that
        // computes the SAME permutation. Installing it at the helper address
        // yields correct sponge outputs but a different code hash.
        vm.etch(f1600, _F1600_CODE);
        assertTrue(f1600.codehash != F1600_CODEHASH, "substituted code hash differs");

        vm.expectRevert(MLDSA44Verifier.BadHelper.selector);
        shipped.verify(shipPk, msg_, sig);
    }

    /// the same, with an arbitrary (non-permutation) replacement.
    function test_helper_code_replaced_after_deploy_reverts() public {
        vm.etch(f1600, address(new SECDummy()).code);
        vm.expectRevert(MLDSA44Verifier.BadHelper.selector);
        shipped.verify(shipPk, msg_, sig);
    }

    /// erasing the helper account's code is likewise caught (EXTCODEHASH == 0).
    function test_helper_erased_after_deploy_reverts() public {
        vm.etch(f1600, "");
        assertEq(f1600.code.length, 0, "helper erased");
        vm.expectRevert(MLDSA44Verifier.BadHelper.selector);
        shipped.verify(shipPk, msg_, sig);
    }

    // ==================================== sponge fail-closed on bad helper ===

    /// f1600Fast170's returndatasize()==800 check makes a missing, reverting or
    /// wrong-size helper fail closed (revert), never a silent wrong result.
    function test_sponge_fails_closed_on_bad_helper() public {
        SpongeProbe probe = new SpongeProbe();
        address shortH = address(new SECShortHelper());
        address revH = address(new SECRevertHelper());

        // codeless account: STATICCALL succeeds with 0 return bytes; the size
        // check rejects it -> require() reverts.
        vm.expectRevert();
        probe.perm(address(0xdead));

        // wrong-size return (799 bytes)
        vm.expectRevert();
        probe.perm(shortH);

        // reverting helper
        vm.expectRevert();
        probe.perm(revH);

        // positive control: the genuine helper permutes without reverting
        probe.perm(f1600);
    }
}
