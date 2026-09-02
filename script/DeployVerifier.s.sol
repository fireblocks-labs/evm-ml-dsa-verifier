// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: script/DeployVerifier.s.sol
//
// Step 3 of 3: deploy the verifier.
//
//   constructor(address f1600Helper)
//
// That is the whole constructor. The argument is the address from step 1. The
// constructor asserts f1600Helper.codehash == F1600_CODEHASH and reverts with
// BadHelper() otherwise, so it cannot be pointed at an arbitrary account. The
// verifier stores the address in an immutable and re-checks that hash on every
// verify() call, which is what makes a helper replaced after deployment fail
// closed rather than be trusted.
//
//   FOUNDRY_PROFILE=script F1600_HELPER=0x... \
//     forge script script/DeployVerifier.s.sol:DeployVerifier \
//     --rpc-url "$RPC_URL" --broadcast
//
// Environment:
//   F1600_HELPER  address of the helper deployed in step 1. Required.
//
// The verifier has no owner, no storage and no keys: it is one immutable address
// plus code. Deploying several verifiers against the same helper is fine.
pragma solidity ^0.8.25;

import {DeployBase} from "./DeployBase.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

contract DeployVerifier is DeployBase {
    /// @notice Environment-driven entry point.
    function run() external returns (MLDSA44Verifier verifier) {
        return deploy(vm.envAddress("F1600_HELPER"));
    }

    /// @notice Explicit-argument entry point, for other scripts and for
    ///         script/DeploymentDryRun.t.sol.
    function deploy(address helper) public returns (MLDSA44Verifier verifier) {
        checkHelper(helper);

        vm.startBroadcast();
        verifier = new MLDSA44Verifier(helper);
        vm.stopBroadcast();

        logVerifier(address(verifier), helper);
        return verifier;
    }

    /// @notice Reproduce the constructor's check up front, so a wrong address
    ///         produces a message instead of a bare BadHelper() revert.
    function checkHelper(address helper) internal view {
        require(helper != address(0), "F1600_HELPER is the zero address");
        require(
            helper.code.length != 0,
            string.concat(
                "F1600_HELPER ",
                vm.toString(helper),
                " has no code on this chain -- run script/DeployHelper.s.sol first"
            )
        );
        require(
            helper.code.length == F1600_RUNTIME_SIZE,
            string.concat(
                "F1600_HELPER ",
                vm.toString(helper),
                " holds ",
                vm.toString(helper.code.length),
                " bytes, not the helper's ",
                vm.toString(F1600_RUNTIME_SIZE)
            )
        );
        require(
            helper.codehash == F1600_CODEHASH,
            string.concat(
                "F1600_HELPER ",
                vm.toString(helper),
                " has code hash ",
                vm.toString(helper.codehash),
                " but the verifier pins ",
                vm.toString(F1600_CODEHASH),
                " -- the constructor would revert with BadHelper()"
            )
        );
    }
}
