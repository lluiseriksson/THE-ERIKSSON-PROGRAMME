# Surface K2 normalization supersession

**Effective:** 2026-07-28

**State:** `K2_ENDPOINT_WITHDRAWN`; `K2_REGULAR_EXTENSIONS_WITHDRAWN`;
`DO_NOT_SUBMIT`

The exact incident is
`INCIDENT-DELTA0-Y-DOUBLE-NORMALIZATION-20260728.md`.  Any claimed K2
certificate that loads the historical full-moment assembler or its
historical companion-error helpers inherits the duplicated normalization
and carries no theorem load.

This supersedes the theorem status, while preserving the historical bytes,
of:

- `surface-remainder-k2-endpoint-20260712T125718Z.json`;
- `surface-remainder-k2-hybrid009-current-20260717T085239Z.json`;
- all eight current `surface-remainder-k2-r4-regular008-*.json` segment
  manifests and their joint validation;
- both current
  `surface-remainder-k2-r4-v2-regular005-part*.json` manifests;
- any downstream union or role audit that treats one of those rows as K2
  evidence.

Already quarantined, superseded, or candidate-only manifests remain
historical diagnostics and are not promoted.

The following work is independent of the faulty assembler:

- the positive-delta order-eight S1/S2 arithmetic in
  `surface_remainder_s1_delta8_exact.py` and
  `surface_remainder_s2_delta8_exact.py`;
- finite-beta Wronskian sign certificates;
- G4 and G5 certificates whose dependency ledgers do not load the endpoint
  assembler;
- exact bridge, Neumann/Graf, and Bessel identities.

Restoration requires:

1. corrected endpoint production and independent replay;
2. corrected regular-extension production and independent replay;
3. an executable dependency audit proving that no accepted row loads the old
   assembler hash;
4. a fresh K2/G5/mirror role audit;
5. a fresh final-seal audit and PDF build.

The first dependency-scope audit is executable as
`python scripts/audit_surface_k2_normalization_supersession.py`.  It
identifies 22 historical manifests carrying the withdrawn LF digest
`3bf631c2...`, exactly 12 of which still say `status: current`; those 12 are
the current withdrawals listed above.  This is a scope audit, not the later
restoration audit: it does not promote any corrected replacement.

The source-shape contract
`python scripts/audit_surface_full_moment_y_normalization.py` additionally
checks every located live full-moment assembler and error propagator.  The
symbolic Gaussian derivations are deliberately excluded because they operate
on dimensionless moments and correctly retain `1/(2c)`.
