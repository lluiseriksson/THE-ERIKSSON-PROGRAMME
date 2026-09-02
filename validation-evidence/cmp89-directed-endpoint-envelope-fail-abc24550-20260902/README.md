# CMP89 directed endpoint envelope diagnostic — FAIL

- Source checkpoint: `abc24550519829f7e2c276e2510afbb277f0ec4b`
- Runner checkpoint: `779e4089897d5ddb8a153063a46ce21945770ac2`
- Notebook checkpoint: `7ff0b58d53ebbfaeecc4b1108ef3899b972f0cca`
- Runtime: Colab Pro+ CPU, 50.99 GiB RAM
- First failing stage: `directed_endpoint_phase_focal`
- Focal exit: `1` after `1019.689` seconds
- Evidence JSON SHA-256: `ce06e8f16966d77c2bf5f19af4c2ef323bfcfdb8b6ba9f0187c017506e4649f9`
- Evidence archive SHA-256: `880195bdde528447a07b4a573c6aab3e541ef172bca51b400528d6fad093dd83`

The runner stopped before the phase audit and before both source-envelope
stages. Lean reported four elaboration failures in the first module:

1. nonexistent constant `Complex.neg_mul_re` at line 45;
2. a redundant phase-imaginary rewrite after the norm theorem had already
   expanded the phase at line 63;
3. an unnormalized difference of two finite sums at line 84;
4. an unnormalized real-to-complex cast of an endpoint difference at line
   103.

The archive was exposed from the retained runtime as a local `data:` link,
materialized byte-for-byte, checked against the SHA printed inside Colab,
and accepted by
`tmp/audit_cmp89_eq246_directed_endpoint_envelope_evidence.py`. The runtime
was then disconnected and deleted. This is diagnostic FAIL evidence only:
all four modules remain PRE-VALIDATION, no field is discharged, `20/41` is
unchanged, and `TermSource = 0` remains exact.
