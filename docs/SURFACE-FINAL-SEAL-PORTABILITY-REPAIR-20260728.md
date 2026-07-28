# Surface final-seal portability repair (2026-07-28)

## Withdrawal

The nominal seal at `97a9a7f2` passed in the shared Windows checkout but did
not reproduce from its LF Git tree.  The external audit
`8c93990896e6f69fcfd5b8f2802ae163baca772f` correctly withdrew
`READY_FOR_CLAIM_AUDIT`.

The first failure was

```text
FINAL-SEAL BLOCKED: G2 terminal domain audit failed:
dependency drift scripts/certify_surface_k2_weak_main_covariance.py
```

The mathematical transcript and the dependency had identical content modulo
EOL representation.  Reproducing the failure from `git archive` revealed that
the same raw-hash comparison existed in two validators:

- `validate_surface_high_beta_lambda3_weak_relay_inputs.py`;
- `validate_surface_k2_weak_main_covariance_transcripts.py`.

After repairing both comparisons, the clean archive advanced to a second
blocking defect:

```text
No such file or directory:
scripts/surface_remainder_delta0_moving_tail.py
```

That source was listed in the weak-main transcript dependency ledger and
present in the shared worktree, but absent from commit `97a9a7f2`.

## Repair

Both validators now accept a recorded dependency hash only when it belongs to
`surface_eol_hashes.sha256_variants(path)`: the raw, LF-normalized, or
CRLF-normalized digest of the same bytes.  This is not a relaxed content
check.  New tests prove that LF and CRLF forms pass and that a one-line content
change fails.

The omitted moving-tail module is now included in the Git tree.  An explicit
dependency inventory confirms that every path recorded by the near, far, and
lambda-three transcript ledgers is versioned.

## Clean-tree reproduction

A clean detached LF worktree was created outside the shared worktree from the
repaired branch.  It contained only versioned files and had no access to the
shared worktree's untracked files.  From that directory:

```text
32 passed
Surface closure gate board OK
FINAL-SEAL PASS: terminal gates, manuscript, and PDF are present
```

## Test-layer follow-up

The clean terminal seal above is confirmed externally, but it was not a full
repository test run.  A later clean `python -m pytest -q` exposed an
unversioned Bessel-gap test dependency and then historical tests whose
positive assumptions had been superseded by the full-moment normalization
repair.  The follow-up and the separate, still-blocked repository integration
state are recorded in
`SURFACE-REPOSITORY-REPRODUCIBILITY-AUDIT-20260728.md`.

The full seal reconstructed the finite bridge, tail contract, right-edge
archives, weak-main terminal union, and closed-form anchors.

## Editorial repair and rebuilt artifact

The external mathematics audit passed all five questions but identified two
no-load presentation debts.  The manuscript now:

1. writes
   `X_main = 4 beta^3 Cov_P(F/D,(H_B/K)D)`, including the physical
   normalization and the already-defined kernel `H_B`;
2. defines `a,b,d,d_1,rho` and every main/mirror/rest moment and correction
   term before the two-stage assembly.

The affected pages 16--18 were rendered and visually inspected.  The new
two-pass pdfTeX build has 33 pages, zero fatal errors, undefined references,
undefined citations, or overfull boxes.

```text
TeX SHA-256
ebe578725f9ae049be059c1bc133b58a74b36819707c805b7afda799da609801

PDF SHA-256
e8cc61a1c370d941baff0ae9019dde4c0d528dbeb42f7c81b221667c1e67333e
```

The external audit transcript remains unchanged and is preserved as
`scripts/audit_weak_main_math_transcript.txt`.
