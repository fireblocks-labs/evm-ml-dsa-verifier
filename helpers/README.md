# The Keccak-f[1600] helper runtime

Two hex blobs, deployed as contract code. The verifier calls
`f1600_170.hex` and checks it by `EXTCODEHASH` on every call, so substituting a
different helper is rejected rather than trusted.

| File | Bytes | What it is |
|---|---|---|
| `f1600_core.hex` | 19,617 | The bare Keccak-f[1600] permutation, fully unrolled |
| `f1600_170.hex` | 21,622 | What ships: the core plus a calldatasize dispatcher that runs a whole SHAKE-256 sponge in one `staticcall` |

`f1600_170.hex` is **reproducible**:

```bash
python3 tools/build_f1600_batch.py --check
```

That rebuilds it from `f1600_core.hex` by applying three mechanical patches
(round-1 state reads relocated from calldata to memory so the permutation is
in-place and therefore loopable; five iota constants that solc left as 15-gas
`SHL`/`SUB` reconstructions patched to 3-gas `PUSH8`s; the trailing `RETURN`
removed) and wrapping the result in the dispatcher. The check fails if the
committed bytes differ.

**`f1600_core.hex` is not reproducible from anything in this repository.** The
generator that emitted it was not preserved. This is the one shipped artifact
without a rebuild path. What stands in its place:

- its SHA-256 is pinned, so it cannot change unnoticed;
- `f1600_170.hex`, the blob that actually executes, *is* rebuilt from it and
  checked byte-for-byte;
- it is differentially tested against an independent Keccak implementation
  (`test/ZZZ_LibKeccak_OP.sol`, from ethereum-optimism/lib-keccak) and against
  251 SHAKE KATs, so a wrong permutation would have to be wrong in a way that
  agrees with a separate implementation on every vector.

That is behavioural evidence, not provenance. `docs/FORMAL_VERIFICATION.md`
states the same limitation.
