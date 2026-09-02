# `tools/fixtures/` — vm.ffi fixture generators

Deterministic, offline generators that the Solidity test suite drives through
`vm.ffi`. They live in the repo so the test tree is self-contained: no test
references a path outside this repository.

**All paths in the `.t.sol` files are repo-relative.** `vm.ffi` runs with
`cwd` = the foundry project root (the repository root), so the tests use
`"pythonref/myenv/bin/python"` and `"tools/fixtures/<script>.py"`.

Requirements: the `pythonref/myenv` virtualenv (provides `eth_abi` and
`pycryptodome`), plus `pythonref/dilithium_py` (added to `sys.path` by each
script from its own location). No network access after the one-time corpus
vendoring, no writes outside `test/fixtures/`, no randomness. Every script is
a pure function of its arguments.

The FIPS 204 public-side math (pkDecode, ExpandA, NTT, tr) comes from
`prepare/mldsa_min.py`, loaded **by absolute path** so the fixtures are always
produced by the very module that `prepare/prepare.py` ships with.

---

## The pk payload (shared by every generator)

**20,544 bytes**, byte-identical to `prepare/prepare.py` output minus its
leading `0x00`:

| offset | size | content |
| --- | --- | --- |
| `0` | 64 | `tr = SHAKE256(pk, 64)` |
| `64` | 4,096 | `t1hat = NTT((t1 << 13) mod q)`, 4 polys, 32 words each |
| `4160` | 16,384 | `Ahat = ExpandA(rho)` (NTT domain), 16 polys row-major `i*4 + j`, 32 words each |

Word packing (`compact_256(32)`): word `w` of a poly holds coefficients
`8w..8w+7`, coefficient `8w+s` at bit offset `32*s` (LSB-first), serialised
big-endian so a Solidity `mload()` of the word returns exactly that value.

The two in-tree verifiers consume the same payload in two placements:

* **reference** (`test/ZZZ_E2ERef.sol`) — the payload verbatim as account
  code (`code == blob`, 20,544 B; tests place it with `vm.etch` because a
  payload whose `tr[0]` is `0xEF` (~1/256 of keys) is EIP-3541-undeployable).
* **shipped** (`src/MLDSA44Verifier.sol`) — `0x00 ‖ payload` (20,545 B),
  deployed as a raw-CREATE data contract; the `0x00` prefix satisfies
  EIP-3541 for every key.

Key derivation is always the `"NIST"` mode of `pythonref/sig_sol.py`:
`Dilithium2.key_derive(seed, _xof=shake256, _xof2=shake128)`, and signing is
`Dilithium2.sign(sk, m, deterministic=True, _xof=shake256, _xof2=shake128)`
(`rnd = 0^32`, `ctx = b""`).

---

## `vecgen.py`

Single (signature, pk payload, message) vectors for the end-to-end tests.

```
vecgen.py seed <seed_hex_64_chars_no_0x> <msg_hex_with_0x_prefix>
vecgen.py kat
```

* `seed` — derive the key pair from `seed`, sign `msg` deterministically.
* `kat` — reproduce, bit-exactly, the KAT vector: provenance
  `pythonref/dilithium_py/generate_KAT_example.py` — AES-256-CTR-DRBG seeded
  with `bytes(range(48))`, a 48-byte seed then a 33-byte message drawn from it,
  `Dilithium2.set_drbg_seed(seed)` + `keygen()` + `sign(sk, msg)`, count 0 of
  `pythonref/assets/PQCsignKAT_Dilithium2.rsp`. The other **99** records of that
  file are wired in as `kat_*` shards by `kat_build.py`; read
  `pythonref/assets/provenance.txt` before citing them. The DRBG stream is
  NIST's, the keys and signatures are `dilithium_py`'s, so they are third-party
  BREADTH and not a NIST answer.

**stdout** (hex, no `0x`): `abi.encode(bytes sig, bytes pkBlob, bytes msg)`.
`sig` 2,420 B, `pkBlob` the 20,544-byte payload, `msg` the raw message.

```sh
pythonref/myenv/bin/python tools/fixtures/vecgen.py seed \
  cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe \
  0x1111222233334444111122223333444411112222333344441111222233334444
pythonref/myenv/bin/python tools/fixtures/vecgen.py kat
```

---

## `e2e_pk.py`

pk payloads on their own.

```
e2e_pk.py seed <seed_hex_64_chars_no_0x>
e2e_pk.py pk   <pk_hex_with_0x_prefix>
```

**stdout** (hex, no `0x`): the RAW 20,544-byte payload, *not* abi-encoded,
and *without* the leading `0x00` byte that `prepare/prepare.py` prepends
(tests deploying for the shipped verifier prepend it; tests for the reference
verifier deploy these bytes verbatim and assert
`blob.length == E2E_PK_SIZE == 20544`).

```sh
pythonref/myenv/bin/python tools/fixtures/e2e_pk.py seed \
  cafecafecafecafecafecafecafecafecafecafecafecafecafecafecafecafe
pythonref/myenv/bin/python tools/fixtures/e2e_pk.py pk 0x<1312-byte pk hex>
```

---

## `degen.py`

The degenerate-key fixture: the public key `pk = rho || pkEncode(t1 = 0)`,
for which a signature can be forged with no secret key (`z = 0`, `h = 0`).
This is ML-DSA's known lack of key-substitution / exclusive-ownership
robustness, **not** a bug in the EVM verifiers. The reference FIPS 204
verifier accepts the same sigma, and the fixture reports that verdict as a
**measured** boolean, never hardcoded. Consequence: the registration-time pk
validator must re-derive the cache from a standard pk, and it must REJECT
degenerate keys (`t1 = 0` and friends); see docs/SAFETY.md. The script
docstring has the exact CLI and output ABI.

---

## `degen2.py`

The three fixtures that pin the degeneracy guidance of
`docs/SAFETY.md` §3.1, one mode each:

* `witness <t1_value> <seed> <msg>` — **no proof about the secret key rejects
  degenerate keys**, not even a proof of knowledge of `(s1, s2)`. The class has
  publicly computable, norm-conforming, exact secret keys: `(0, 0, 0)` for
  `t1 = 0` and `(0, -1, 0)` for `t1 = 1023` (because `1023 * 2^13 == q - 1`
  exactly, so `Power2Round(q-1, 13) = (1023, 0)` and `||s2||inf = 1 <= eta = 2`).
  The mode builds the FIPS 204 secret key from the witness and **signs with the
  reference signer**, which genuinely uses `s1`, `s2` and `t0`; it reports the
  measured norms, an independent re-derivation of the key relation over all
  1,024 coefficients, and the reference verifier's own verdict.
* `maxdegen <seed> <msg>` — the **maximal** degenerate key, `t1 = 1023` in all
  1,024 coefficients (every `pkEncode` byte `0xff`), key-free forgeable by the
  same `z = 0, h = 0` construction because `lift(1023) = -1`.
* `fatsig <seed> <msg>` — the same key-free forgery under `t1 = 0` with an
  **ordinary-looking** signature: `||z||inf` just under `gamma1 - beta` and 60
  real hint bits, which defeats "reject conspicuous responses" as a hardening.

Consumed by `test/SEC_pkcache.t.sol`. Every verdict is measured, never
hardcoded; the script docstring has the exact CLI and output ABI.

---

## Shard builders

`acvp_build.py`, `fuzz_build.py`, `shake_build.py` and `wycheproof_build.py`
(plus `formal/acvp/keygen_build.py`) produce the multi-case ABI shard
fixtures for `test/ACVP_MLDSA44.t.sol`, `test/FUZZ_MLDSA44.t.sol`,
`test/FUZZ_Shake.t.sol`, `test/SEC2_Wycheproof.t.sol` and
`test/FV2_AcvpKeyGen.t.sol`. Shards are cached under `test/fixtures/`
(git-ignored, self-healing on first use) and every expected verdict is either
an official corpus verdict, a `dilithium_py` oracle verdict, or both, never
hand-asserted.

See **README_shards.md** for the family list, provenance (URLs + SHA-256 of
the official NIST ACVP and Project Wycheproof source vectors), the case
taxonomy and the regeneration commands.
