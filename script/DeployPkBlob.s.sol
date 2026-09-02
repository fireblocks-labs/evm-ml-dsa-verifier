// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: script/DeployPkBlob.s.sol
//
// Step 2 of 3: deploy one public key.
//
// prepare/prepare.py turns a standard 1,312-byte FIPS 204 ML-DSA-44 public key
// into a 20,545-byte blob (0x00 || tr || t1hat || Ahat) that is deployed as raw
// runtime code. src/MLDSA44Verifier.sol reads it with EXTCODECOPY from offset 1,
// and the resulting address is the `pkBlob` argument to verify().
//
//   python3 prepare/prepare.py "$PUBLIC_KEY_HEX" > deployments/mykey.hex
//   FOUNDRY_PROFILE=script PK_BLOB_PATH=deployments/mykey.hex \
//     forge script script/DeployPkBlob.s.sol:DeployPkBlob \
//     --rpc-url "$RPC_URL" --broadcast
//
// Environment (one of the two is required):
//   PK_BLOB_PATH  path to a file holding prepare.py's hex output.
//   PK_BLOB_HEX   prepare.py's hex output inline. Takes precedence.
//
// One blob per key; a blob is public data and holds no secret. It is NOT
// self-validating: on-chain the verifier checks only that the code is 20,545
// bytes long, so whoever registers a key must establish off-chain that the blob
// really is this program's output on a genuine, non-degenerate public key. See
// docs/SAFETY.md section 3.
pragma solidity ^0.8.25;

import {DeployBase} from "./DeployBase.sol";

contract DeployPkBlob is DeployBase {
    /// @notice Environment-driven entry point.
    function run() external returns (address pkBlob) {
        // loadPkBlobBytes() rejects anything that is not exactly 20,545 bytes
        // before a broadcast is opened; deploy() checks it again, and checks the
        // deployed code length afterwards.
        return deploy(loadPkBlobBytes());
    }

    /// @notice Explicit-argument entry point, for other scripts and for
    ///         script/DeploymentDryRun.t.sol.
    function deploy(bytes memory blob) public returns (address pkBlob) {
        vm.startBroadcast();
        pkBlob = deployPkBlob(blob);
        vm.stopBroadcast();

        logPkBlob(pkBlob);
        return pkBlob;
    }
}
