// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: script/DeployBase.sol
//
// Shared primitives for the three deployment steps. Nothing here is specific to
// a script: DeployHelper, DeployPkBlob, DeployVerifier and the dry-run test in
// script/DeploymentDryRun.t.sol all go through these functions, so the test
// exercises the same code the scripts do.
//
// PROVENANCE OF THE TWO INIT STUBS. Both artifacts (the Keccak helper runtime
// and the public-key blob) are RAW RUNTIME CODE, not compiled contracts, so they
// need an initcode wrapper that copies them out of the initcode and RETURNs
// them. The two wrappers below are copied byte-for-byte from the ones the test
// suite already deploys with, because the verifier pins the helper by
// EXTCODEHASH and any difference in the deployed bytes changes that hash:
//
//   * deployHelperRuntime() -- the 11-byte stub from
//     test/ZZZ_FastKeccak170.sol:deployF1600_170(), which is what every test
//     that constructs an MLDSA44Verifier uses (test/E2E.t.sol,
//     test/SEC_helper.t.sol, test/SEC_pkcache.t.sol, ...).
//
//   * deployDataContract() -- the 14-byte stub from
//     test/E2E.t.sol:_deployData(), duplicated verbatim in
//     test/SEC_helper.t.sol and test/SEC_pkcache.t.sol, which is what those
//     tests deploy public-key blobs with.
//
// Both stubs return the payload verbatim, so the deployed code -- and therefore
// the EXTCODEHASH -- is exactly keccak256(payload) either way. They are kept
// separate only so each deployment path is byte-identical to the tested one.
pragma solidity ^0.8.25;

import {Script, console2} from "forge-std/Script.sol";

abstract contract DeployBase is Script {
    // ------------------------------------------------------------- constants

    /// keccak256 of the 21,622-byte Keccak-f[1600] helper runtime. This MUST
    /// equal the private F1600_CODEHASH constant in src/MLDSA44Verifier.sol or
    /// the verifier's constructor reverts with BadHelper(). Recompute with:
    ///   cast keccak "0x$(tr -d '\n' < helpers/f1600_170.hex)"
    bytes32 internal constant F1600_CODEHASH =
        0x4afb4435879cdf8e50474c7aab2bc3a679caed432550ad6dba64f509309a817b;

    /// Size of the helper runtime in helpers/f1600_170.hex.
    uint256 internal constant F1600_RUNTIME_SIZE = 21_622;

    /// Size of prepare/prepare.py's output: the 0x00 EIP-3541 prefix byte plus
    /// the 20,544-byte payload the verifier EXTCODECOPYs from code offset 1.
    /// src/MLDSA44Verifier.sol accepts a pk pointer only when
    /// extcodesize(pkBlob) == PK_SIZE + 1 == 20545; any other size makes
    /// verify() return false rather than revert.
    uint256 internal constant PK_BLOB_SIZE = 20_545;

    /// EIP-170 runtime code size limit. Both artifacts must stay under it.
    uint256 internal constant EIP170_MAX_CODE_SIZE = 24_576;

    string internal constant DEFAULT_F1600_RUNTIME_PATH = "helpers/f1600_170.hex";

    // -------------------------------------------------- raw-code deployment

    /// @notice Deploy the Keccak-f[1600] helper runtime and assert its code hash
    ///         against the verifier's pin.
    /// @dev Init stub, byte-for-byte test/ZZZ_FastKeccak170.sol:deployF1600_170():
    ///      PUSH2 len; DUP1; PUSH2 0x000b; PUSH0; CODECOPY; PUSH0; RETURN.
    ///      NOTE: this stub uses PUSH0 (EIP-3855), so it needs a Shanghai or
    ///      later chain. On an older chain use deployDataContract() instead,
    ///      which only uses PUSH1/PUSH2 and produces identical deployed code.
    function deployHelperRuntime(bytes memory runtime) internal returns (address helper) {
        require(
            runtime.length == F1600_RUNTIME_SIZE,
            string.concat(
                "f1600 helper: runtime must be ",
                vm.toString(F1600_RUNTIME_SIZE),
                " bytes, got ",
                vm.toString(runtime.length)
            )
        );
        require(
            keccak256(runtime) == F1600_CODEHASH,
            string.concat(
                "f1600 helper: runtime hashes to ",
                vm.toString(keccak256(runtime)),
                " but MLDSA44Verifier pins ",
                vm.toString(F1600_CODEHASH),
                " -- wrong or corrupted helpers/f1600_170.hex"
            )
        );

        bytes memory initCode =
            abi.encodePacked(hex"61", uint16(runtime.length), hex"8061000b5f395ff3", runtime);
        assembly ("memory-safe") {
            helper := create(0, add(initCode, 32), mload(initCode))
        }
        require(helper != address(0), "f1600 helper: CREATE failed");
        require(
            helper.codehash == F1600_CODEHASH,
            "f1600 helper: deployed code hash does not match the verifier's pin"
        );
        return helper;
    }

    /// @notice Deploy `data` verbatim as contract code.
    /// @dev Init stub, byte-for-byte test/E2E.t.sol:_deployData():
    ///      PUSH2 len; PUSH1 0x0e; PUSH1 0x00; CODECOPY; PUSH2 len; PUSH1 0x00;
    ///      RETURN. No PUSH0, so this works on pre-Shanghai chains too.
    function deployDataContract(bytes memory data) internal returns (address at) {
        require(data.length != 0, "data contract: empty payload");
        require(
            data.length < EIP170_MAX_CODE_SIZE,
            string.concat(
                "data contract: ",
                vm.toString(data.length),
                " bytes exceeds the EIP-170 limit of ",
                vm.toString(EIP170_MAX_CODE_SIZE)
            )
        );
        // EIP-3541: deployed code may not begin with 0xEF.
        require(data[0] != 0xEF, "data contract: payload starts with 0xEF (EIP-3541)");

        bytes memory initCode = abi.encodePacked(
            bytes1(0x61),
            uint16(data.length),
            hex"600e600039",
            bytes1(0x61),
            uint16(data.length),
            hex"6000f3",
            data
        );
        assembly ("memory-safe") {
            at := create(0, add(initCode, 32), mload(initCode))
        }
        require(at != address(0), "data contract: CREATE failed");
        require(at.code.length == data.length, "data contract: deployed size mismatch");
        return at;
    }

    /// @notice Deploy a prepare.py public-key blob as a data contract.
    /// @dev Fails before spending gas if the blob is not exactly what
    ///      src/MLDSA44Verifier.sol will accept. A blob of the wrong size does
    ///      not revert inside verify(): the size check makes verify() return
    ///      FALSE for every signature, so a wrong-size blob deploys a key that
    ///      silently rejects everything. Catch it here instead.
    function deployPkBlob(bytes memory blob) internal returns (address pkBlob) {
        require(
            blob.length == PK_BLOB_SIZE,
            string.concat(
                "pk blob: must be exactly ",
                vm.toString(PK_BLOB_SIZE),
                " bytes (prepare/prepare.py output), got ",
                vm.toString(blob.length),
                blob.length == PK_BLOB_SIZE - 1
                    ? " -- this looks like the payload without prepare.py's leading 0x00 byte"
                    : ""
            )
        );
        require(
            blob[0] == 0x00,
            "pk blob: first byte must be 0x00 (the EIP-3541 prefix prepare.py emits; the verifier reads the payload from code offset 1)"
        );

        pkBlob = deployDataContract(blob);
        require(
            pkBlob.code.length == PK_BLOB_SIZE,
            "pk blob: deployed code length is not the 20545 bytes the verifier requires"
        );
        return pkBlob;
    }

    // ------------------------------------------------------ artifact loading

    /// @notice Read a file of ASCII hex (with or without a 0x prefix, whitespace
    ///         and newlines ignored) and return the decoded bytes.
    function readHexArtifact(string memory path) internal view returns (bytes memory) {
        string memory raw;
        try vm.readFile(path) returns (string memory contents) {
            raw = contents;
        } catch {
            // Two causes, and the cheatcode's own message is printed just above
            // this one in the trace, so name both rather than guess.
            revert(
                string.concat(
                    "cannot read '",
                    path,
                    "': either the file is not there, or fs_permissions do not cover it. The default foundry profile grants no fs_permissions at all -- run with FOUNDRY_PROFILE=script and keep the file under helpers/ or deployments/, or skip files entirely and pass the hex inline via PK_BLOB_HEX / F1600_RUNTIME_HEX."
                )
            );
        }
        require(bytes(raw).length != 0, string.concat("'", path, "' is empty"));
        return parseHexString(raw);
    }

    /// @notice Decode an ASCII hex string, tolerating an optional 0x prefix and
    ///         any surrounding whitespace.
    function parseHexString(string memory s) internal pure returns (bytes memory) {
        return vm.parseBytes(string.concat("0x", _cleanHex(s)));
    }

    /// @notice Resolve the Keccak helper runtime from F1600_RUNTIME_HEX (inline)
    ///         or F1600_RUNTIME_PATH (file, default helpers/f1600_170.hex), and
    ///         check its size and hash before any broadcast is opened.
    function loadHelperRuntime() internal view returns (bytes memory runtime) {
        string memory inlineHex = vm.envOr("F1600_RUNTIME_HEX", string(""));
        if (bytes(inlineHex).length != 0) {
            runtime = parseHexString(inlineHex);
        } else {
            string memory path = vm.envOr("F1600_RUNTIME_PATH", DEFAULT_F1600_RUNTIME_PATH);
            runtime = readHexArtifact(path);
        }

        require(
            runtime.length == F1600_RUNTIME_SIZE,
            string.concat(
                "f1600 helper: runtime must be ",
                vm.toString(F1600_RUNTIME_SIZE),
                " bytes, got ",
                vm.toString(runtime.length)
            )
        );
        require(
            keccak256(runtime) == F1600_CODEHASH,
            string.concat(
                "f1600 helper: runtime hashes to ",
                vm.toString(keccak256(runtime)),
                " but MLDSA44Verifier pins ",
                vm.toString(F1600_CODEHASH)
            )
        );
        return runtime;
    }

    /// @notice Resolve a prepare.py public-key blob from PK_BLOB_HEX (inline) or
    ///         PK_BLOB_PATH (file), and check its size before any broadcast is
    ///         opened.
    /// @dev A wrong-size blob is the dangerous failure mode: the verifier's
    ///      `extcodesize(pkBlob) == 20545` test makes verify() return FALSE
    ///      rather than revert, so a short or long blob deploys a key that
    ///      rejects every signature with no error to distinguish it from a bad
    ///      signature. Refuse it here.
    function loadPkBlobBytes() internal view returns (bytes memory blob) {
        string memory inlineHex = vm.envOr("PK_BLOB_HEX", string(""));
        if (bytes(inlineHex).length != 0) {
            blob = parseHexString(inlineHex);
        } else {
            string memory path = vm.envOr("PK_BLOB_PATH", string(""));
            require(
                bytes(path).length != 0,
                "set PK_BLOB_PATH=<file with prepare/prepare.py output> or PK_BLOB_HEX=<that hex inline>"
            );
            blob = readHexArtifact(path);
        }

        require(
            blob.length == PK_BLOB_SIZE,
            string.concat(
                "pk blob: must be exactly ",
                vm.toString(PK_BLOB_SIZE),
                " bytes, got ",
                vm.toString(blob.length),
                blob.length == 1312
                    ? " -- that is the RAW public key; run it through prepare/prepare.py first"
                    : ""
            )
        );
        return blob;
    }

    /// @dev Strip whitespace and one optional leading 0x, then check that what
    ///      is left is an even-length run of hex digits, so a malformed file
    ///      produces a message that says what is wrong with it.
    function _cleanHex(string memory s) private pure returns (string memory) {
        bytes memory b = bytes(s);
        bytes memory out = new bytes(b.length);
        uint256 n = 0;
        for (uint256 i = 0; i < b.length; ++i) {
            uint8 c = uint8(b[i]);
            if (c == 0x20 || c == 0x09 || c == 0x0a || c == 0x0d) continue; // space, tab, LF, CR
            if (n == 0 && c == 0x30 && i + 1 < b.length) {
                uint8 nxt = uint8(b[i + 1]);
                if (nxt == 0x78 || nxt == 0x58) {
                    // "0x" / "0X"
                    ++i;
                    continue;
                }
            }
            bool isHexDigit =
                (c >= 0x30 && c <= 0x39) || (c >= 0x61 && c <= 0x66) || (c >= 0x41 && c <= 0x46);
            require(isHexDigit, "hex artifact contains a character that is not a hex digit");
            out[n] = b[i];
            ++n;
        }
        require(n != 0, "hex artifact contains no hex digits");
        require(n % 2 == 0, "hex artifact has an odd number of hex digits");
        assembly ("memory-safe") {
            mstore(out, n)
        }
        return string(out);
    }

    // -------------------------------------------------------------- logging

    function logHelper(address helper) internal view {
        console2.log("f1600 helper");
        console2.log("  address     ", helper);
        console2.log("  code size   ", helper.code.length);
        console2.log("  EXTCODEHASH ", vm.toString(helper.codehash));
    }

    function logPkBlob(address pkBlob) internal view {
        console2.log("pk blob");
        console2.log("  address     ", pkBlob);
        console2.log("  code size   ", pkBlob.code.length);
        console2.log("  pass this address as the pkBlob argument to verify()");
        console2.log(
            "  REMINDER: the verifier cannot tell whether this blob came from a genuine,"
        );
        console2.log(
            "  non-degenerate 1312-byte public key. Validate that off-chain at registration"
        );
        console2.log("  time -- see docs/SAFETY.md section 3.");
    }

    function logVerifier(address verifier, address helper) internal view {
        console2.log("MLDSA44Verifier");
        console2.log("  address     ", verifier);
        console2.log("  code size   ", verifier.code.length);
        console2.log("  f1600Helper ", helper);
    }
}
