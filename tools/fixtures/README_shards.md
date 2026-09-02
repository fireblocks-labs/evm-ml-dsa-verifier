# Fixture shards for the ACVP / fuzz / SHAKE / Wycheproof suites

Five Solidity suites read their corpora as ABI-encoded "shards" through
`vm.ffi`. The shards are regenerable (~45 MB of hex text in total), so they
are not committed: they are produced on demand by the builders in this
directory (plus `formal/acvp/keygen_build.py`) and cached under
`test/fixtures/` (git-ignored).

| suite | builder | shards |
|---|---|---|
| `test/ACVP_MLDSA44.t.sol` | `acvp_build.py` | `ah_0..5.hex`, `at_0..3.hex` |
| `test/KAT_MLDSA44.t.sol` | `kat_build.py` | `kat_0..3.hex` |
| `test/FUZZ_MLDSA44.t.sol` | `fuzz_build.py` | `fs_0..12.hex`, `fm_0..22.hex` |
| `test/FUZZ_Shake.t.sol` | `shake_build.py` | `sk_0..3.hex`, `sr_0..2.hex` |
| `test/SEC2_Wycheproof.t.sol` | `wycheproof_build.py` | `wp_0..3.hex`, `wpc_*.hex` |
| `test/FV2_AcvpKeyGen.t.sol` | `../../formal/acvp/keygen_build.py` | `kg_acvp_0..4.hex` |

`tools/fixtures/fx_common.py` holds the shared plumbing: the distilled ACVP
corpora, the on-chain public-key payload encoding, the reference oracle
wrappers, the ABI shard encoders and the flock-protected shard cache.

Every ML-DSA case is fed to BOTH in-tree subjects: the reference verifier
`test/ZZZ_E2ERef.sol` and the shipped `src/MLDSA44Verifier.sol`. There is a
single expected-verdict column. Both implement pure ML-DSA-44 with an empty
context, so their required verdicts coincide; any divergence between the two
implementations fails the suite.

## Regeneration

All commands are run from the repository root (which is also the cwd `vm.ffi`
gives the builders, so every path below is repo-relative).

```sh
# rebuild one family
pythonref/myenv/bin/python tools/fixtures/acvp_build.py       --build
pythonref/myenv/bin/python tools/fixtures/kat_build.py        --build
pythonref/myenv/bin/python tools/fixtures/fuzz_build.py       --build   # ~45 s
pythonref/myenv/bin/python tools/fixtures/shake_build.py      --build
pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py --build
pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py --audit   # census, no writes
pythonref/myenv/bin/python formal/acvp/keygen_build.py        --stats

# print one shard (this is exactly what the tests do)
pythonref/myenv/bin/python tools/fixtures/acvp_build.py ah_1.hex

# force a full rebuild
rm -rf test/fixtures && pythonref/myenv/bin/python tools/fixtures/fuzz_build.py --build
```

Each builder is *self-healing*: a test that asks for a missing shard causes the
whole family to be built (under `test/fixtures/.build.lock`, so parallel forge
workers build it exactly once) and then served. Everything is deterministic.
All pseudo-randomness comes from `fx_common.rnd()`, a SHAKE-256 expansion of a
fixed domain string, so a rebuild reproduces the corpus bit-for-bit, offline,
from the committed source vectors.

## Provenance of the source vectors

The upstream ACVP files named in the suite headers are fetched once over HTTPS
(certificate verification on) from `usnistgov/ACVP-Server`, distilled down to
the subset the suites use, and written to `tools/fixtures/acvp_data/`
(**committed**, so later regenerations need no network). Each upstream URL is
pinned by SHA-256 in `ACVP_FILES` (`fx_common.py`) and the digest is **checked
on fetch**. A projection that moved upstream aborts the build naming both
digests. The digest actually seen is also recorded under the `_provenance` key
of the distilled JSON.

| upstream file (`gen-val/json-files/<name>/internalProjection.json`) | distilled to | kept |
|---|---|---|
| `ML-DSA-sigVer-FIPS204` | `acvp_data/mldsa44.json` | ML-DSA-44 `external/pure` (tgId 1, tcId 1–15) and `external/preHash` (15 cases) |
| `ML-DSA-sigGen-FIPS204` | `acvp_data/mldsa44.json` | ML-DSA-44 `external/pure` (30 cases, deterministic + hedged) and `external/preHash` (30 cases) |
| `ML-DSA-sigGen-FIPS204-tr1` | `acvp_data/mldsa44.json` (`tr1` bucket) | ML-DSA-44 `external/pure` (60 cases) and `external/preHash` (60 cases), across both `keyFormat` presentations (`seed` / `expanded`) and both `deterministic` modes — **120 keys disjoint from every other corpus here** |
| `SHAKE-256-FIPS202` | `acvp_data/shake256.json` | the 41 byte-aligned cases of the 237 AFT vectors |
| `SHAKE-256-1.0` | `acvp_data/shake256.json` | the 143 byte-aligned AFT + 67 byte-aligned VOT cases |

The `internal` and `externalMu` ML-DSA groups are not kept: the verifiers under
test implement the external (`M' = 0x00 ‖ 0x00 ‖ M`, empty-context) interface.
The 1646 bit-oriented SHAKE cases (`len % 8 != 0` or `outLen % 8 != 0`) and the
single MCT group are not expressible by a byte-oriented EVM XOF and are skipped;
41 + 143 + 67 = **251** vectors remain, every one of them re-derived with
`hashlib.shake_256` before it is kept.

Two further committed corpora feed their own suites:

* `test/vectors/wycheproof/mldsa_44_verify_test.json` — Project Wycheproof
  ML-DSA-44 verify vectors (URL, SHA-256, date and flag census in the sibling
  `provenance.txt`; the builder re-checks the SHA-256 on every run).
* `formal/acvp/data/mldsa_keygen.json` — the ACVP ML-DSA-keyGen corpus
  (SHA-256 in the sibling `provenance.json`, verified on every run).

## Case-category taxonomy

### ACVP suite — 165 cases (`ah_*`)

| tag | n | source | verdict |
|---|---|---|---|
| `SV<tc>` | 15 | sigVer ML-DSA-44 external/pure, tcId 1–15 | ACVP `testPassed` **AND** empty ctx — which is **must-reject for all 15**: see below |
| `SG<tc>` | 30 | sigGen ML-DSA-44 external/pure | valid |
| `PH<tc>` | 45 | HashML-DSA (preHash): 15 sigVer + 30 sigGen | **must reject** as pure ML-DSA |
| `DV<tc>` | 15 | the official sigVer `(sk, message)` re-signed with `ctx=""` | valid |
| `DV<tc>:{msg,ctilde,z,hint}` | 60 | the four ACVP mutation classes applied to each `DV<tc>` | **must reject** |

`:ctxbind` is appended to the label whenever the official case carries a
non-empty context: the verifiers implement ML-DSA with an empty context only
(`M' = 0x00 ‖ 0x00 ‖ M`), so such a signature must not be accepted.

**The official sigVer corpus contributes ZERO must-accept coverage to this
verifier, and the SV row above must not be read as though it did.** Its
`testPassed` distribution is 3 valid / 12 invalid, but all three valid cases
(tcId 3, 11, 15) carry a non-empty context, so `exp = testPassed and not ctx`
makes every one of the 15 a **must-reject**, three of them (`:ctxbind`) for
context binding rather than for signature validity. Exactly one sigVer case has
an empty context (tcId 10) and it is `testPassed: false`.

The 18 must-accept cases in `ah_*` are therefore **3 sigGen** cases (tcId 5, 8,
189, the only external/pure sigGen vectors with an empty context) plus the
**15 `DV<tc>` cases, which are repo-derived**: the official `(sk, message)`
pairs re-signed by the Python reference with `ctx = b""`. That is third-party
KEY MATERIAL under our own signer, not a third-party answer. If you need "NIST
says this signature verifies" as a must-accept, this corpus does not provide it
at this interface; the `kg_acvp_*` keyGen shards are the ACVP data whose
expected values are checked positively.

Every verdict is taken from ACVP's own `testPassed` where ACVP has one, and
*every* case is independently reproduced with the `dilithium_py` oracle before
it is emitted; a disagreement aborts the build. For the 45 `PH` cases the
oracle additionally confirms that each one **does** verify inside its own
preHash domain (`M' = 0x01 ‖ |ctx| ‖ ctx ‖ OID ‖ PH(M)`), so their rejection
as pure ML-DSA is domain separation, not a broken vector.

Sharding is **round-robin** (`case i -> shard i % nshards`): every category is
present in every shard, and sigVer tcId 14 (the one official ML-DSA-44 key
whose `tr[0]` is `0xEF`) lands together with its `DV14` case in `ah_1`, which
`test_acvp_eip3541_pk_prefix` is built around (the raw payload is
EIP-3541-undeployable; the shipped verifier's `0x00`-prefixed layout deploys
and verifies it).

### ACVP FIPS204-tr1 suite — 120 cases (`at_*`)

The technical-corrigendum-1 sigGen projection, on **120 official keys that
appear nowhere else in this tree** (`acvp_build.build_tr1_corpus` asserts the
key sets are disjoint, and asserts the must-accept count, so a re-pin that
turned this into a second copy of the corpus above would fail the build).

| tag | n | source | verdict |
|---|---|---|---|
| `TP<tc>:<keyFormat>` | 5 | `external/pure`, **empty context** | **must accept** |
| `TP<tc>:<keyFormat>:ctxbind` | 55 | `external/pure`, non-empty context | **must reject** (context binding) |
| `TH<tc>:<keyFormat>` | 60 | `external/preHash` | **must reject** (pure/preHash domain separation) |

`<keyFormat>` is `seed` or `expanded`. tr1 presents every group in both key
presentations. It is a key-GENERATION distinction: both hand a verifier the
same 1,312-byte public key, so it is carried as a label and never branched on.

**These 5 are the only official-answer must-accepts this verifier has outside
the keyGen shards.** Every `testPassed: true` case in the official sigVer set
carries a non-empty context (see the note above), so at an empty-context
interface it must be rejected; tr1 is the corpus where NIST says "accept" and
this verifier accepts.

### 100-key KAT breadth suite — 100 cases (`kat_*`)

Every record of `pythonref/assets/PQCsignKAT_Dilithium2.rsp`: 100 distinct
ML-DSA-44 keys, 100 distinct 33-byte messages, **all must-accept**. Exactly one
of the 100 is read anywhere else in the tree (record 0, for its `mlen` field
alone, in `vecgen.py`), so this suite is the only thing that exercises the
other 99.

| tag | n | source | verdict |
|---|---|---|---|
| `KAT<i>` | 100 | `pythonref/assets/PQCsignKAT_Dilithium2.rsp`, record *i* | **must accept** |

**Cite this as BREADTH, not as NIST authority.** The file is in the NIST PQC
KAT format and its seeds and messages ARE the NIST harness's DRBG stream
(`kat_build.py` replays `AES256_CTR_DRBG(bytes(range(48)))` and asserts them
byte for byte), but the keys and signatures were generated in-tree by
`dilithium_py` under FIPS 204. Evidentially it is a differential check against
a third-party Python implementation at scale (the same class as `fs_*`), not
an official answer. Full statement, with the digests that separate this file
from the NIST PQC Round 3 upstream file of the same name, in
`pythonref/assets/provenance.txt`.

The builder aborts unless all 100 records replay from the DRBG, the 100 keys
are pairwise distinct, none of them occurs in the ACVP corpora, and the
pythonref oracle accepts every triple at an empty context.

### Fuzz suite — 2180 cases (`fs_*`, `fm_*`)

* **Battery A** (`fs_*`, 800 must-accept): 40 derived keys × 20 message lengths
  `{0,1,2,31,32,33,63,64,65,69,70,71,135,136,137,206,272,342,500,8192}`.
  Label `A:k<key>:len<n>`.
* **Battery B** (`fm_*`, 1380 must-reject): 60 base signatures × 23
  sigma mutations. Label `B:base<j>:<class>`; the 23 classes are
  `flip.ctilde`, `flip.z`, `flip.h`, `flip.multi3`, `z.plus1`,
  `z.boundary.g1mb`, `z.inrange.g1mb1`, `z.gamma1`, `z.maxfield`, `z.rowswap`,
  `h.count.gt.omega`, `h.nonmonotone.idx`, `h.nonmonotone.cnt`,
  `h.nonzero.pad`, `h.allzero`, `sig.trunc2419`, `sig.ext2421`, `sig.empty`,
  `sig.random`, `msg.swap`, `pk.swap`, `ctilde.zero`, `ctilde.other`.
  The `h.*` classes exercise the FIPS 204 HintBitUnpack (Algorithm 21)
  validity conditions on the `hEncode(h)` region of the 2420-byte signature.

Battery A is key-major and battery B base-major with contiguous sharding, so a
shard only ever touches 3–4 public keys, which keeps the per-shard pk-blob
overhead down. Shards carry at most 62 cases each because every case costs
two on-chain verifications (several million gas each) and a shard must fit
the default per-test gas ceiling.

Every case is oracle-checked (`dilithium_py`) before emission: battery A must
verify, and every battery-B mutation must be rejected *and* must actually
differ from its base.

### SHAKE suite — 656 vectors (`sk_*`, `sr_*`)

* `sk_0..3` — the 251 official byte-aligned ACVP SHAKE-256 KATs
  (63/63/63/62). Labels `ACVP:<file>/<testType>:tc<n>`.
  Inputs up to 8126 B, outputs up to 512 B.
* `sr_0..2` — 405 oracle vectors (135/135/135): a 19 × 15 grid of input ×
  output lengths straddling the 136-byte rate and the 3rd/4th block boundary
  (285 cases), plus 120 uniformly random `(inLen ≤ 4096, outLen ≤ 2048)` pairs.
  Labels `RND:grid:<in>-><out>` / `RND:rand<i>:<in>-><out>`.

### Wycheproof suite — 180 cases (`wp_*`, `wpc_*`)

176 representable cases in `wp_0..3` (round-robin), plus per-flag class shards
that deliberately overlap them (`wpc_hints`, `wpc_zeropk`, `wpc_norm`,
`wpc_bound`, `wpc_many`, `wpc_siglen`, `wpc_ctx`) and the 4
IncorrectPublicKeyLength registration-layer cases in `wpc_pklen.hex`.
See the long header of `wycheproof_build.py` and of
`test/SEC2_Wycheproof.t.sol` for the verdict policy, the known
`dilithium_py` repeated-hint-index divergence (tcId 18, CVE-2026-24850 class)
and the pk-length canonicalisation finding (tcId 65).

### ACVP keyGen suite — 25 cases (`kg_acvp_*`)

The 25 official ML-DSA-44 keyGen key pairs, re-signed offline over a fixed
per-seed message; all must-accept through both subjects. Built by
`formal/acvp/keygen_build.py` (5 shards of 5).

## Wire formats

The shard structs are ABI tuples whose field order matches the Solidity
`struct` declarations verbatim (`abi.decode` is positional). See the
`SHARD_T` / `COMBO_T` / `PKLEN_T` constants in each builder and
`fx_common.SHAKE_SHARD_T`.

The ML-DSA shards all carry the same public-key encoding: the **20,544-byte
pk payload** of `tools/fixtures/e2e_pk.py` / `prepare/prepare.py`
(`tr(64) ‖ t1hat rows 0..3 (4096) ‖ Ahat 16 polys row-major (16384)`, each
poly 32 words of 8 × 32-bit coefficient fields, serialised big-endian). The
tests place it twice:

* **reference verifier** (`test/ZZZ_E2ERef.sol`) — the payload verbatim as
  account code (`vm.etch`; `code == blob`, 20,544 B).
* **shipped verifier** (`src/MLDSA44Verifier.sol`) — `0x00 ‖ payload`
  (20,545 B), deployed with a plain raw CREATE; the `0x00` prefix satisfies
  EIP-3541 for every key.

## Shard inventory

Totals (~45 MB of hex text on disk):

| family | shards | cases / vectors | must-accept | must-reject | hex bytes |
|---|---|---|---|---|---|
| `ah_*` ACVP | 6 (28,28,28,27,27,27) | 165 | 18 | 147 | 7,843,328 |
| `at_*` ACVP FIPS204-tr1 | 4 (30 each) | 120 | 5 | 115 | 6,573,248 |
| `kat_*` 100-key KAT breadth | 4 (25 each) | 100 | 100 | 0 | 5,005,440 |
| `fs_*` fuzz battery A | 13 (62×7, 61×6) | 800 | 800 | 0 | 7,366,208 |
| `fm_*` fuzz battery B | 23 (60 each) | 1380 | 0 | 1380 | 10,914,496 |
| `sk_*` SHAKE ACVP KAT | 4 (63,63,63,62) | 251 | — | — | 458,432 |
| `sr_*` SHAKE random | 3 (135 each) | 405 | — | — | 1,431,872 |
| `wp_*` Wycheproof corpus | 4 (44 each) | 176 | 75 | 101 | 2,263,680 |
| `wpc_*` Wycheproof classes | 8 | 205 (overlapping) | — | — | 2,357,440 |
| `kg_acvp_*` ACVP keyGen | 5 (5 each) | 25 | 25 | 0 | 1,167,680 |

Every ML-DSA case is verified by both subjects, so the ACVP + fuzz + keyGen +
Wycheproof rows amount to 2,546 distinct cases and 5,092+ on-chain
verifications per full run.

Regenerating the whole set from scratch takes about a minute
(`fuzz_build.py` ≈ 45 s dominates); a `forge test` run that finds a shard
missing pays that cost once inside `vm.ffi` and every later run is a plain
file read.
