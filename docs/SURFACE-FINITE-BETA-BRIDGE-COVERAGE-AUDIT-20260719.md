# Finite scaled-bridge candidate coverage audit

**Date:** 2026-07-19
**State:** `TOPOLOGY_ONLY`; no G2/G6 load

The executable
`scripts/audit_surface_finite_beta_bridge_candidate_coverage.py` parses every
archived production transcript under `scripts/surface_scaled_bulk_*.txt` and
admits an interval only when its replay companion exists.  It understands the
three transcript header formats (`beta_domain`, `beta_unit`, and the older
`beta-box`/title form) and clips the result to the preregistered finite target
`[20,1000/9]`.

Current paired topology (including the fresh preregistered candidate
`[22,89/4]` rerun, but before terminal-status filtering):

```text
component [20,813/8] = [20,101.625]
gaps      [813/8,1000/9]
```

The historical unpaired high-order run on `[625/8,313/4]` (the file ending in
`_run.txt`) remains deliberately excluded; replacement production/replay pairs
are admitted only through their manifests. The audit is therefore an honest
inventory of the exact remaining seam, not a claim that candidate sign rows
prove `(H_tail)` or close the finite bridge.

## Current executable gap list (2026-07-22)

The stricter CWIN=3/2 relay auditor now emits exact uncovered beta intervals
instead of only a boolean adjacency flag. With the archived admissible set,
the gaps are

```text
[22, 89/4], [31, 74], [625/8, 401/4],
[803/8, 1609/16], [805/8, 1613/16], [807/8, 1617/16],
[809/8, 1621/16], [811/8, 1625/16], [1629/16, 1000/9].
```

The CWIN=4 strips `[31,37]` are deliberately excluded: they are quarantined
candidate evidence and do not satisfy the registered CWIN=3/2 relay contract.
The fresh `[22,89/4]` pair is likewise quarantined: it repairs the earlier
post-hoc provenance gap but does not enter the admissible relay set.  Thus the
strict relay auditor still reports `[22,89/4]` as uncovered until a terminal
manifest and the analytic sign-to-`H_tail` lemma exist.  The gap list is
topology only; even an empty list would still require the independent
finite-tail majorant and pointwise relay proof before G2/G6 promotion.
