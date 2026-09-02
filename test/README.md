# The test tree

39 suites, 320 tests. `forge test` runs all of them.

The filenames carry prefixes. Several are pinned by name from `formal/`, so
renaming one is a tree-wide change, not a cosmetic one.

| Prefix | What lives there |
|---|---|
| `ACVP_`, `KAT_` | Official NIST vectors: the ACVP corpus (valid and must-reject) and the 100-key `PQCsignKAT` breadth suite |
| `SEC2_Wycheproof` | The Wycheproof ML-DSA-44 corpus, sharded by failure class |
| `E2E`, `Stages` | Whole-verification tests, and the stage-by-stage gas brackets behind the published breakdown |
| `FUZZ_` | Randomised inputs against the Python reference over `vm.ffi` |
| `SEC_`, `SEC2_`, `SEC3_` | Security properties: helper substitution, memory safety, purity, the FIPS 204 checks, hint-padding, public-key caching |
| `FV_`, `FV2_`, `FV3_`, `FV4_`, `FV6_` | Support for the formal work — halmos harnesses, and tests that re-derive in EVM semantics what `formal/` proves about a model |
| `MUT_` | The mutation campaign's attribution checks: every `test_MUT_M<nn>_*` names the mutant it kills, and `formal/hypotheses.py` checks that claim against the artifact |
| `PROFILE_`, `GasCalibration`, `NttMicro`, `Kernels` | Measurement rather than assertion — the numbers `docs/EXPLAINER.md` quotes |
| `ZZZ_` | Independent reference implementations and variant kernel copies used as differential oracles, plus the tests that exercise them |
| `ZZZR_`, `ZZZR2_`, `ZZZR3_` | Probes and adversarial cases layered on top of those oracles |

Two things that trip people up:

- **The digits are grouping suffixes, not versions.** `FV2_Barrett.sol` and
  `FV2_AcvpKeyGen.t.sol` are unrelated subjects that happen to share a group,
  and there is no `FV5_`.
- **`ZZZ_*.sol` files without `.t.` are libraries, not suites.** Several of
  them (`ZZZ_E2ERef.sol`, `ZZZ_NttVariants.sol`, `ZZZ_InvNtt.sol`,
  `ZZZ_FastKeccak170.sol`) exist to be imported by other tests as oracles. They
  are deliberately *not* the shipped code. `docs/FORMAL_VERIFICATION.md`
  explains where each is and is not an oracle.

`test/vendor/` holds upstream ZKNoxHQ/ETHDILITHIUM sources, unmodified, used as
differential oracles only. See [`vendor/README.md`](vendor/README.md).

`test/fixtures/` and `test/vectors/` are data. `fixtures/` is gitignored and
rebuilt on first `forge test` from the committed, digest-verified corpora under
`tools/fixtures/`; see [`../tools/fixtures/README.md`](../tools/fixtures/README.md).
