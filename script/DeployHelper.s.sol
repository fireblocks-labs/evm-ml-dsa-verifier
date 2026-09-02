// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: script/DeployHelper.s.sol
//
// Step 1 of 3: deploy the Keccak-f[1600] helper.
//
// helpers/f1600_170.hex is 21,622 bytes of RAW RUNTIME CODE, not a compiled
// contract, so it is deployed through an initcode stub that returns those bytes
// verbatim (see script/DeployBase.sol for the stub and its provenance). The
// deployed account's EXTCODEHASH must equal the F1600_CODEHASH constant in
// src/MLDSA44Verifier.sol; if it does not, the verifier's constructor reverts
// with BadHelper(). This script asserts the hash before and after deployment.
//
// The helper is stateless, immutable, permissionless and content-addressed, so
// ONE deployment per chain is enough: any number of verifiers, from any number
// of deployers, can point at the same helper address.
//
//   FOUNDRY_PROFILE=script forge script script/DeployHelper.s.sol:DeployHelper \
//     --rpc-url "$RPC_URL" --broadcast
//
// Environment:
//   F1600_RUNTIME_PATH  path to the runtime hex. Default helpers/f1600_170.hex.
//   F1600_RUNTIME_HEX   the runtime as an inline hex string. Takes precedence
//                       over F1600_RUNTIME_PATH; useful where fs_permissions
//                       are not granted.
pragma solidity ^0.8.25;

import {DeployBase} from "./DeployBase.sol";
import {console2} from "forge-std/Script.sol";

contract DeployHelper is DeployBase {
    /// @notice Environment-driven entry point.
    function run() external returns (address helper) {
        // loadHelperRuntime() checks the size and the code hash here, before a
        // broadcast is opened; deploy() checks the deployed account again.
        return deploy(loadHelperRuntime());
    }

    /// @notice Explicit-argument entry point, for other scripts and for
    ///         script/DeploymentDryRun.t.sol.
    function deploy(bytes memory runtime) public returns (address helper) {
        vm.startBroadcast();
        helper = deployHelperRuntime(runtime);
        vm.stopBroadcast();

        logHelper(helper);
        console2.log("  next: F1600_HELPER=<the address above> forge script DeployVerifier");
        return helper;
    }
}
