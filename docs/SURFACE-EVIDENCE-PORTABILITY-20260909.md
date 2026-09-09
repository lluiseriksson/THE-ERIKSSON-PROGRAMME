# Surface evidence portability repair

The [historical CI baseline](PHYSICAL-REFLECTION-CI-BASELINE-20260906.md)
reported nine failures and 695 passes. The same failures occurred on the
9 September literature PR and on its merge. They include representation and
path-resolution failures before dependent Surface audits can complete.

## Byte representation

Historical Windows runs recorded CRLF SHA-256 values while GitHub's Linux
checkout supplies LF text. The affected bulk, lambda-three and near/far
relay validators now reuse `surface_eol_hashes.sha256_variants`: the saved
digest must still identify exactly the original text, allowing only the
existing LF/CRLF equivalence. The historical constants are unchanged.

Production and replay must still be byte-identical to each other. Dependency
sets, source-commit blobs, canonical LF hashes, exact domains, row counts,
adjacency and numerical inequalities retain their checks. Returned raw hashes
describe the bytes actually read; the bulk result exposes its historical
recorded hash separately. The sixth-head test pins both known raw encodings
and the same canonical LF digest instead of requiring CRLF on every platform.

## Historical paths and frozen identity

Thirty admissible units contain Windows-style output paths such as
`scripts\surface_scaled_bulk_87_87p5.txt`. Treating the backslash as a literal
POSIX filename loses these units and leaves a gap between beta 87 and 401/4.

The G2 reader now resolves both separator styles inside the repository.
Absolute, drive-relative, parent-traversing and escaping paths are rejected.
Historical manifests and output files are not rewritten. The original path
strings still enter the terminal fingerprint; normalization is applied only
when opening a file. List-schema unit names use the same Windows-compatible
stem rule on both platforms.

The required ownership count remains **501** and the frozen fingerprint stays
`86029ed96f88c53fd0fe18769e33577d4eee56aed553f36943dd490f09b7ae80`.
No acceptance constant, certificate, manuscript, Lean source or proof-state
record is changed by this repair.

## Regression coverage and integration gate

The regression tests exercise LF and CRLF versions of real historical
artifacts, both path separator styles, unchanged raw identities, changed
source/payload/manifest rejection, missing files, production/replay mismatch
and paths outside the repository. Existing tests continue to require the
exact frozen G2 cover and the complete dependent Surface audits.

```sh
python -m pytest -q
python scripts/check_consistency.py
```

The control-plane workflow also runs when these audit and validation scripts
change, even if no test file changes. The repair must pass the full Linux
control-plane workflow before integration; the narrower `honesty` check alone
is insufficient. This is a software/evidence-reader repair, not a new Lean
compilation or a proof of four-dimensional Yang–Mills existence or mass gap.
