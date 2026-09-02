# Efficient EVM ML-DSA verification

An Ethereum smart contract that verifies ML-DSA-44 signatures, the
post-quantum scheme in NIST's
[FIPS 204](https://csrc.nist.gov/pubs/fips/204/final) (previously
CRYSTALS-Dilithium).

One verification costs **1,226,311 gas**. The best previously published
implementation costs 8,094,831 gas, so this is about 6.6x cheaper. The contract
is [`src/MLDSA44Verifier.sol`](src/MLDSA44Verifier.sol).

> This is research code. **It has not been audited.**

## Using it

```solidity
function verify(address pkBlob, bytes calldata message, bytes calldata signature)
    external view returns (bool accepted);
```

`signature` is an ordinary 2,420-byte FIPS 204 signature.

A public key needs preparing once before this verifier can use it. Run
[`prepare/prepare.py`](prepare/prepare.py) on the standard 1,312-byte key and
deploy the output as its own contract. That contract's address is the `pkBlob`
argument. The verifier reads the key straight out of its bytecode. The script
takes hex on stdin and returns hex on stdout; `python3
prepare/prepare.py --help` covers the rest.

You also need one shared helper contract on-chain, a Keccak permutation
([`helpers/f1600_170.hex`](helpers/f1600_170.hex)). It computes SHAKE-256,
which the EVM's own hashing opcode cannot produce.

### What does the gas figure include?

It covers the work inside `verify()` and nothing else. A real transaction also
pays Ethereum's 21,000 gas base cost, plus the cost of sending the signature as
calldata.

Publishing a key is separate and happens once per key, at about 4.11M gas,
because the prepared key is 20,545 bytes of contract code. That is more than
three verifications. The design pays that cost once per key, then verifies
cheaply.

## Deploying it

Three deployments in order: the shared Keccak helper, one blob per public key,
then the verifier. The scripts read files, so they need the `script` profile.

```bash
export FOUNDRY_PROFILE=script

forge script script/DeployHelper.s.sol:DeployHelper --rpc-url "$RPC_URL" --broadcast
PK_BLOB_PATH=mykey.hex forge script script/DeployPkBlob.s.sol:DeployPkBlob --rpc-url "$RPC_URL" --broadcast
F1600_HELPER=0x... forge script script/DeployVerifier.s.sol:DeployVerifier --rpc-url "$RPC_URL" --broadcast
```

`script/DeployAll.s.sol` does all three at once. The constructor is
`constructor(address f1600Helper)`. One helper is enough for every verifier on
a chain, because the binding is by code hash rather than by address.

`forge test --match-path 'script/*'` runs the whole sequence locally and
verifies a real signature through the contracts it just deployed.

## Why it is cheap

| Component | Baseline | Here |
|---|---:|---:|
| SHAKE-256 (9 permutations, batched sponge) | 3,001k | ~399k |
| NTT (9 transforms) | 1,850k | ~440k |
| Matrix multiply + `c·t1` | 852k | ~221k |
| Expanded-key loading | 1,030k | ~5k |
| Signature decode (`z`, hints) | 941k | ~86k |
| UseHint + `w1` encoding | 359k | ~72k |
| Memory expansion (quadratic) | ~1,800k | ~7k |
| **Total (measured end-to-end)** | **8,094,831** | **1,226,311** |

The baseline column is a per-stage profile, so its rows sum to more than its
total: memory expansion is a global cost, counted both on its own line and
inside the stages that allocate. Only the totals are directly comparable. Full
derivation in [docs/EXPLAINER.md](docs/EXPLAINER.md).

**SHAKE-256.** ML-DSA hashes with SHAKE, and `KECCAK256` cannot compute it.
The permutation is the same, the padding is not, and the opcode only ever
returns 32 bytes. So Keccak-f[1600] has to run in ordinary opcodes. A Solidity
loop over a memory array costs 153,267 gas per permutation. Here the 24 rounds
are straight-line bytecode, rotation amounts and round constants are
immediates, and the 25 lanes sit at fixed offsets, so a load is `mload(0x40)`
rather than `mload(add(base, 0x40))`. The unrolled permutation is ~21KB, past
the EIP-170 contract limit, which is why it lives in a separate helper.

The EVM has no rotate opcode. Rotating a 64-bit lane normally takes a shift
left, a shift right, an OR, and a mask to clear the bits the left shift spilled
upward. Keccak does that 29 times per round. Holding the lane as four copies
(`v || v || v || v`) makes the spill land in the next copy of the same value,
which is the wraparound a rotate wants, so the mask disappears entirely.
**153,267 → 41,664 gas per permutation**, both measured here
(`test_gas_f1600_reference`, and the batched stage profile).

**Packed arithmetic.** Coefficients are 23 bits, and an EVM multiply costs the
same whether it uses 23 bits of the word or all 256. Four coefficients ride in
one word and one multiply does all four. Sums stay unreduced across NTT layers,
growing but staying inside their 64-bit lanes; reduction happens only at
multiplies, as two Barrett steps. The growth bounds are proved in Z3 and Lean
rather than argued. One forward transform drops from **182,470 gas to 45,701**
at fresh memory, both printed by `test/ZZZ_nttvariants.t.sol`. Inside
`verify()`, where the twiddle table is built once per call rather than once per
transform, it costs 44,931.

Baseline figures here are what the vendored ZKNox kernels cost *in this tree*.
`foundry.toml` applies solc's IR pipeline to everything, so both sides of every
comparison come out of one compiler invocation. The same kernels under legacy
codegen run 7 to 9 percent higher, which is why figures published elsewhere for
them are larger.

**Expanded key.** Verification needs the expanded matrix and the NTT of `t1`,
not the 1,312-byte wire key. Both implementations store that blob as a data
contract, but the baseline then unpacks it to one coefficient per word (128KB)
and `abi.decode`s nested arrays. Here `prepare.py` writes the packed layout the
arithmetic already reads, and `EXTCODECOPY` streams it one row at a time into a
reused 5KB scratch, so the expanded key never sits in memory. Moving expansion
off-chain is ZKNoxHQ's idea; the storage format is the difference.

**Decode.** `z` is 1,024 coefficients in 18-bit fields. Four fields are 72
bits, exactly nine bytes, so they come out of a single load, get split on the
stack, and land in one packed word already in the layout the NTT reads. The
hint vector marks at most 80 of those coefficients and arrives as 84 bytes of
indices. The baseline expanded it into a 1,024-word array. Here it becomes
four 256-bit masks.

**Memory.** The EVM prices memory quadratically in the highest address a call
touches. The baseline peaks at 953KB and pays ~1.8M gas for that alone. Packed
layouts, streaming the key, decoding straight into position, and fusing NTT
layers keep the peak near 41KB.

None of this bends the standard. The verifier restores two FIPS 204 checks the
baseline omits.

## Running it

You need Foundry on the nightly channel and Python 3.10. `foundry.toml`
requires a recent EVM version that stable releases do not know yet.

```bash
# the exact build the published gas figures were measured on
foundryup -i nightly-c808c4cd6d104514204e77654e000929ca878b90

forge build

# one-time: the tests compare against a Python reference implementation
python3.10 -m venv pythonref/myenv
pythonref/myenv/bin/pip install -r pythonref/requirements.txt

forge test                              # 320 tests
forge test --match-test test_e2e_10 -vv # prints the gas figure itself
```

A different nightly may shift the gas numbers by a few hundred. The first
`forge test` in a fresh clone spends a couple of extra minutes generating test
fixtures.

One thing that looks like a bug and is not: `forge build --sizes` reports a
failure on purpose, because one test file contains deliberately oversized
contracts to probe Ethereum's contract size limit. The check that matters is on
the verifier itself, which is 24,032 bytes against a limit of 24,576.

The proofs need [`elan`](https://github.com/leanprover/elan) for Lean:

```bash
elan toolchain install $(cat formal/lean/lean-toolchain)
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh
```

## What has been checked

There are 320 tests. They cover NIST's official ACVP vectors, both the valid
cases and the ones that must be rejected. They also cover a 100-key
known-answer suite, Google's Wycheproof corpus, fuzzing, and a comparison
against a Python reference implementation.

Beyond the tests, 62 properties of the arithmetic are proved mechanically in
Z3. There are also 64 Lean 4 theorems, with no unproved steps and no external
maths library.

The repository runs a 50-mutant campaign as well. Fifty deliberate bugs were
injected one at a time. All 45 that change behaviour were caught by some test,
and the other five are provably equivalent to the original.

What has not been done: an audit, and an independent cryptographic review. The
proofs cover the arithmetic and the encoding rather than the verifier end to
end. [docs/FORMAL_VERIFICATION.md](docs/FORMAL_VERIFICATION.md) states
where proof ends and testing begins.

## Repository layout

| Path | What |
|------|------|
| `src/` | the verifier and its arithmetic |
| `helpers/` | the Keccak helper contract, and [what about it is not reproducible](helpers/README.md) |
| `prepare/` | the script that prepares a public key |
| `test/` | the tests, with [`test/README.md`](test/README.md) explaining the filenames |
| `pythonref/` | the Python reference implementation used for comparison |
| `formal/` | the machine-checked proofs and the mutation campaign |
| `docs/` | how it works, what is verified, and what a deployment must do |

## Credits

Baseline and benchmark:
[ZKNoxHQ/ETHDILITHIUM](https://github.com/ZKNoxHQ/ETHDILITHIUM).
Keccak cross-check:
[ethereum-optimism/lib-keccak](https://github.com/ethereum-optimism/lib-keccak).
Reference implementation:
[GiacomoPope/dilithium-py](https://github.com/GiacomoPope/dilithium-py).

MIT licensed. See [LICENSE](LICENSE).
