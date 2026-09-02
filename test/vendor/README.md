# `test/vendor/` — the vendored ZKNoxHQ/ETHDILITHIUM oracle

FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE

These seven files are **third-party code, vendored verbatim** from
[ZKNoxHQ/ETHDILITHIUM](https://github.com/ZKNoxHQ/ETHDILITHIUM) (MIT; the
copyright headers are the upstream ones). They are the **differential oracle**:
this repository's kernels are asserted equal to *these* implementations, so
they are deliberately **not** cleaned up, reformatted, optimised or partially
deleted. A "tidied" oracle is a different oracle.

Nothing here is deployed. `src/MLDSA44Verifier.sol` imports nothing from this
directory, and no file under `src/` references it.

The test suite does not run every function in these files. One number that
gets quoted about this code was **not measured in this repository**. Both are
stated below.

## What is live

18 functions are entry points the suite calls directly, and 24 of the 37 are
reachable once their internal callees are included:

| file | entry points the suite calls |
|---|---|
| `ZKNOX_NTT_dilithium.sol` | `nttFw`, `nttInv` — the NTT oracle for `test/ZZZ_nttvariants.t.sol`, `test/ZZZ_invntt.t.sol` |
| `ZKNOX_dilithium_core.sol` | `unpackZ`, `unpackH` — the decoder oracle for the differential and mutation tests (mutant **M39** mutates `unpackH` here on purpose, to prove the oracle is exercised) |
| `ZKNOX_hint.sol` | `decompose`, `useHint`, `useHintDilithium`, `calls` — the UseHint / Decompose oracle |
| `ZKNOX_shake.sol` | `f1600`, `shakeInit`, `shakeUpdate`, `shakeDigest` — the SHAKE oracle and the Keccak-f[1600] baseline the fast helper is measured against |
| `ZKNOX_SampleInBall.sol` | `sampleInBallNist` — the SampleInBall oracle |
| `ZKNOX_dilithium_utils.sol` | `compact`, `slice`, `expandMat`, `expandVec` |
| `ZKNOX_PythonSigner.sol` | `sign` — the `vm.ffi` bridge to `pythonref/sig_sol.py` |

## What is dead

13 of the 37 functions are unreachable from every test in this repository, and
they stay because the files are kept verbatim:

```
ZKNOX_dilithium_core.sol   dilithiumCore1, dilithiumCore2
ZKNOX_dilithium_utils.sol  matVecProduct, matVecProductDilithium, scalarProduct,
                           vecAddMod, vecMulMod, vecSubMod, vecSubMulMod
ZKNOX_shake.sol            rol64, shakePad
ZKNOX_PythonSigner.sol     bytesToString, getPubKey
```

Two of those deserve a sentence each:

* **`dilithiumCore1` / `dilithiumCore2` are the upstream verifier's own entry
  points, and nothing in this repository runs them.** The comparison in
  `README.md` and `docs/EXPLAINER.md` is against a *reproduced* baseline; see
  the next section.
* **`getPubKey`** shells out to `pythonref/prepare_pk_for_deployment.py`, which
  this repository no longer contains (it was an unused duplicate of the shipped
  `prepare/prepare.py`). `getPubKey` was already unreachable when it was
  removed; `sign`, the entry point the suite does use, is unaffected.

## The 8,094,831-gas baseline was measured elsewhere

The published comparison, **8,094,831 gas** for ZKNoxHQ/ETHDILITHIUM against
1,226,311 here, is **not produced by any test in this repository**. It was
measured in a larger working tree that instantiated the upstream verifier end
to end (`dilithiumCore1` / `dilithiumCore2` above) on the same toolchain, with
the upstream sources unmodified. Re-deriving it needs that harness, not this
directory: what is vendored here are the *kernels* the differential tests
compare against, not the assembled upstream verifier.

The **per-NTT** figure *is* reproducible here, and the numbers this repository
prints are these: `testGasV1Baseline` in `test/ZZZ_nttvariants.t.sol` calls the
vendored `nttFw` directly on a fresh-memory polynomial and prints **182,470**
gas; `testGasV3` in the same file, same condition, prints **45,701** for
`nttFwV3`, the packed-SWAR replacement (the `test/ZZZ_NttVariants.sol` mirror of
the shipped `src/Ntt.sol`). That is the like-for-like ratio, **4.0×**, and
both sides of it are compiled by the same code generator: `foundry.toml` sets
`via_ir = true` for the whole tree, so the vendored kernels are built through
the IR pipeline here too. A legacy-codegen measurement of this same vendored
`nttFw` is about 7% higher. That is where the ~195.6K figure quoted elsewhere
for it comes from, and it is not what this tree reproduces.

`test/ZZZ_nttvariants.t.sol` is the only suite that brackets the vendored
`nttFw` for gas. `test/ZZZ_invntt.t.sol` imports it too, but uses it to build
inputs and brackets the vendored **`nttInv`** instead: `testGasInvV1Baseline`
prints **215,899** against `testGasInvV3`'s **54,419**, also 4.0×.
`test/NttMicro.t.sol` profiles the shipped transforms only and imports nothing
from this directory.

## Provenance

Upstream repository: <https://github.com/ZKNoxHQ/ETHDILITHIUM> (MIT).
The files carry their upstream `// Copyright (C) 2026 - ZKNOX` headers. Their
bytes are not modified by this repository; the mutation campaign patches
*copies* in a disposable workspace and never edits the tree
(see `formal/mutation/RESULTS.md`).
