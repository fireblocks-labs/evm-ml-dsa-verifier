#!/usr/bin/env python3
"""
prepare.py — public-key blob builder for the MLDSA44Verifier contract.

  input : hex of the standard 1312-byte FIPS 204 ML-DSA-44 public key, taken
          from stdin by default, or from --in FILE, or as the one positional
          argument
  output: hex of the 20,545-byte blob to deploy as a data contract, written to
          stdout by default, or to --out FILE

Run "prepare.py --help" for usage. Deterministic, offline, standard library
only (see prepare/mldsa_min.py).

The blob is deployed ONCE per key as a plain data contract; the verifier reads
it with EXTCODECOPY. See docs/SAFETY.md section 3: the deployment MUST validate
at registration time that a pk blob is the output of this program on a genuine,
non-degenerate 1312-byte public key — the verifier cannot check that on-chain.

BLOB LAYOUT — one leading 0x00 byte (EIP-3541: deployed code must not start with
0xEF and the payload starts with the hash tr), then the bytes the verifier
EXTCODECOPYs from code offset 1 in a single stream:
  [    0 ..     1)  0x00
  [    1 ..    65)  tr    = SHAKE256(pk, 64)
  [   65 ..  4161)  t1hat = NTT(2^d * t1), 4 polys, 32 words each
  [ 4161 .. 20545)  Ahat  = ExpandA(rho) (NTT domain), 16 polys row-major i*4+j,
                    32 words each
Word packing ("compact_256(32)"): word w of a poly holds coefficients 8w..8w+7,
coefficient (8w+s) at bit offset 32*s (LSB-first), serialised big-endian so a
Solidity mload() of the word returns exactly that value.
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import mldsa_min as M  # noqa: E402

BLOB_SIZE = 20545

# The input size this program accepts, checked here so that a wrong-sized key
# produces a readable message instead of the exception mldsa_min.pk_decode
# would raise. Same number as the check in pk_decode.
PK_SIZE = 1312

PROG = "prepare.py"
_HEX_DIGITS = frozenset("0123456789abcdefABCDEF")


def compact32(coeffs):
    """32 words of 8 x 32-bit coefficient fields, big-endian serialised."""
    out = bytearray()
    for w in range(32):
        word = 0
        for s in range(8):
            word |= int(coeffs[8 * w + s]) << (32 * s)
        out += word.to_bytes(32, "big")
    return bytes(out)


def build(pk):
    rho, t1 = M.pk_decode(pk)
    a_hat = M.expand_a(rho)
    t1_hat = [M.ntt([(c << M.D) % M.Q for c in row]) for row in t1]

    blob = bytearray(b"\x00")
    blob += M.tr_of(pk)
    for i in range(4):
        blob += compact32(t1_hat[i])
    for i in range(4):
        for j in range(4):
            blob += compact32(a_hat[i][j])
    assert len(blob) == BLOB_SIZE, len(blob)
    return bytes(blob)


# ------------------------------------------------------------- command line
#
# Everything below is input handling and reporting only. It does not touch the
# layout above, and for a valid 1312-byte key the bytes written to stdout are
# the same as they have always been: build(pk).hex(), with no trailing newline,
# because test/E2E.t.sol feeds that stdout straight into vm.ffi().


def _fail(message):
    """Report a mistake in the input on one line and stop. No traceback."""
    sys.stderr.write("%s: error: %s\n" % (PROG, message))
    raise SystemExit(2)


def _expected():
    return "expected %d hex characters (%d bytes) of ML-DSA-44 public key" % (
        2 * PK_SIZE,
        PK_SIZE,
    )


def _read_text(in_path):
    """The input text: from the named file, or from stdin when none was named."""
    if in_path is None:
        if sys.stdin.isatty():
            _fail(
                "no input. Give the public key hex on stdin, with --in FILE, "
                "or as the single positional argument. See --help."
            )
        return sys.stdin.read()
    try:
        with open(in_path, "r") as handle:
            return handle.read()
    except OSError as exc:
        _fail("cannot read %s: %s" % (in_path, exc.strerror or exc))


def _decode_pk(text, source):
    """The 1312 raw key bytes, or a one-line message saying what was wrong."""
    # Whitespace anywhere is dropped so that a hex file with line breaks or a
    # trailing newline is accepted, as it always has been.
    cleaned = "".join(text.split())
    if cleaned[:2] in ("0x", "0X"):
        cleaned = cleaned[2:]

    if not cleaned:
        _fail("%s held no data; %s." % (source, _expected()))

    for i, char in enumerate(cleaned):
        if char not in _HEX_DIGITS:
            _fail(
                "%s is not hex: character %r at position %d; %s."
                % (source, char, i, _expected())
            )

    if len(cleaned) % 2:
        _fail(
            "%s held an odd number of hex characters (%d), so it is not a whole "
            "number of bytes; %s." % (source, len(cleaned), _expected())
        )

    pk = bytes.fromhex(cleaned)
    if len(pk) != PK_SIZE:
        _fail(
            "%s held %d bytes (%d hex characters); %s. A 1312-byte key is the "
            "standard FIPS 204 ML-DSA-44 pkEncode output: 32 bytes of rho "
            "followed by 1280 bytes of t1."
            % (source, len(pk), len(cleaned), _expected())
        )
    return pk


def _write_hex(blob_hex, out_path):
    """The blob hex to the named file, or to stdout when none was named."""
    if out_path is None:
        sys.stdout.write(blob_hex)
        return
    try:
        with open(out_path, "w") as handle:
            handle.write(blob_hex)
    except OSError as exc:
        _fail("cannot write %s: %s" % (out_path, exc.strerror or exc))


def build_parser():
    parser = argparse.ArgumentParser(
        prog=PROG,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description="""\
Build the deployable public-key blob for the MLDSA44Verifier contract.

Reads the hex of one standard 1312-byte FIPS 204 ML-DSA-44 public key and
writes the hex of the 20,545-byte blob to deploy as a plain data contract. The
verifier reads that contract with EXTCODECOPY. The expansion (SHAKE256, ExpandA
and the NTT of t1) is deterministic, offline and uses the standard library
only, so the same key always gives the same blob.

The default is a pipeline: hex in on stdin, hex out on stdout. Output is 41,090
hex characters, which is 20,545 bytes, with no trailing newline.

Blob layout. One leading 0x00 byte, required because EIP-3541 forbids deployed
code starting with 0xEF, then the bytes the verifier copies from code offset 1:

  [    0 ..     1)  0x00
  [    1 ..    65)  tr    = SHAKE256(pk, 64)
  [   65 ..  4161)  t1hat = NTT(2^d * t1), 4 polys, 32 words each
  [ 4161 .. 20545)  Ahat  = ExpandA(rho) in the NTT domain, 16 polys
                    row-major i*4+j, 32 words each

Deploy a blob only after checking off-chain that the key behind it is genuine,
non-degenerate and exactly 1312 bytes. The verifier cannot check any of that
on-chain. See docs/SAFETY.md section 3.""",
        epilog="""\
examples (the file is not marked executable, so call it through python3):
  # the default: hex on stdin, hex on stdout
  python3 prepare/prepare.py < pk.hex > pkblob.hex

  # the same thing with file arguments instead of shell redirection
  python3 prepare/prepare.py --in pk.hex --out pkblob.hex

  # the key on the command line, with or without a leading 0x
  python3 prepare/prepare.py 0xdb9ac67708f2ba0f...802f9be8 > pkblob.hex

input format:
  Hex only, upper or lower case, with an optional 0x prefix. Whitespace and
  line breaks are ignored, so a wrapped hex file is fine. Raw binary keys are
  not accepted; convert one first, for example with `xxd -p key.bin`.

exit status:
  0  a blob was written
  2  bad usage, an unreadable or unwritable file, input that is not hex, or a
     key that is not exactly 1312 bytes""",
    )
    source = parser.add_mutually_exclusive_group()
    source.add_argument(
        "pk_hex",
        nargs="?",
        metavar="PK_HEX",
        help="the public key as a hex string, instead of reading stdin",
    )
    source.add_argument(
        "--in",
        dest="in_path",
        metavar="FILE",
        help="read the public key hex from FILE instead of stdin",
    )
    parser.add_argument(
        "--out",
        dest="out_path",
        metavar="FILE",
        help="write the blob hex to FILE instead of stdout",
    )
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)
    if args.pk_hex is not None:
        text, source = args.pk_hex, "the PK_HEX argument"
    else:
        text = _read_text(args.in_path)
        source = args.in_path if args.in_path is not None else "stdin"
    _write_hex(build(_decode_pk(text, source)).hex(), args.out_path)


if __name__ == "__main__":
    main()
