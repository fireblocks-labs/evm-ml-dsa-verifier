// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: script/DeployAll.s.sol
//
// All three steps in one run, for a chain that has nothing deployed yet.
// Equivalent to DeployHelper, then DeployPkBlob, then DeployVerifier, without
// copying the helper address between commands.
//
//   FOUNDRY_PROFILE=script PK_BLOB_PATH=deployments/mykey.hex \
//     forge script script/DeployAll.s.sol:DeployAll \
//     --rpc-url "$RPC_URL" --broadcast
//
// Environment:
//   PK_BLOB_PATH / PK_BLOB_HEX  optional. Omit both to deploy only the helper
//                               and the verifier and register keys later.
//   F1600_HELPER                optional. Set it to an already-deployed helper
//                               to skip step 1 and reuse that address.
//   F1600_RUNTIME_PATH / _HEX   as in DeployHelper.
pragma solidity ^0.8.25;

import {DeployBase} from "./DeployBase.sol";
import {console2} from "forge-std/Script.sol";
import {MLDSA44Verifier} from "../src/MLDSA44Verifier.sol";

contract DeployAll is DeployBase {
    /// @notice Environment-driven entry point.
    function run() external returns (address helper, address pkBlob, address verifier) {
        address existing = vm.envOr("F1600_HELPER", address(0));

        bytes memory runtime;
        if (existing == address(0)) runtime = loadHelperRuntime();

        bool withKey = bytes(vm.envOr("PK_BLOB_PATH", string(""))).length != 0
            || bytes(vm.envOr("PK_BLOB_HEX", string(""))).length != 0;
        bytes memory blob;
        if (withKey) blob = loadPkBlobBytes();

        return deploy(runtime, blob, existing);
    }

    /// @notice Explicit-argument entry point, for script/DeploymentDryRun.t.sol.
    /// @param runtime  helper runtime bytes; ignored when `existingHelper` is set.
    /// @param blob     prepare.py output, or empty to skip key registration.
    /// @param existingHelper  an already-deployed helper, or address(0) to deploy one.
    function deploy(bytes memory runtime, bytes memory blob, address existingHelper)
        public
        returns (address helper, address pkBlob, address verifier)
    {
        if (existingHelper != address(0)) {
            require(
                existingHelper.codehash == F1600_CODEHASH,
                "F1600_HELPER does not carry the code the verifier pins"
            );
        }

        vm.startBroadcast();
        helper = existingHelper == address(0) ? deployHelperRuntime(runtime) : existingHelper;
        if (blob.length != 0) pkBlob = deployPkBlob(blob);
        verifier = address(new MLDSA44Verifier(helper));
        vm.stopBroadcast();

        logHelper(helper);
        if (pkBlob != address(0)) logPkBlob(pkBlob);
        else console2.log("pk blob: skipped (PK_BLOB_PATH / PK_BLOB_HEX not set)");
        logVerifier(verifier, helper);
        return (helper, pkBlob, verifier);
    }
}
