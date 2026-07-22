# Signed-bilinear K2 parallel candidate (2026-07-22)

This record archives two fresh executions of the preregistered endpoint lane
`delta=[0,1/1000]`, `t=[0,pi_hi]`.  The parallel runner uses the frozen born
partition of 158 adjacent `t` boxes and spatial grid 48 with eight workers.

Both executions completed with:

```text
rows=158
all row verdicts PASS
CANDIDATE_PRODUCTION_PASS
NO_G2_PROMOTION
```

The production transcript and replay transcript are byte-identical:

```text
SHA256 = ED7F46A571377DC71B390E0AB90274B541C1BD631654BBBF2FF1E204FE0A1EEA
GIT_HEAD = 8f8161c6633066fc1d96d6bcefee3bd8aa121de5
PYTHON = 3.12.6
FLINT = 0.9.0
```

The structural validator, the same-source replay validator, and the exact
`B(0)=0`/`KD(0)>0`/denominator-positivity audit all pass.  The latter checks the factor identity
`2(-8)=(-4)4=-16` pointwise and finds a positive `KD` lower endpoint in every
archived row, while verifying `cos(t/4)>0` in every row.
This is useful reproducible candidate evidence, not a terminal certificate:
the finite-beta relay and the remaining K2 remainder obligations are still
open, so K2 cannot be promoted and G2 remains open.

Artifacts:

- `scripts/run_surface_remainder_signed_bilinear_parallel_candidate.py`
- `scripts/validate_surface_remainder_signed_bilinear_production.py`
- `scripts/validate_surface_remainder_signed_bilinear_replay.py`
- `scripts/audit_surface_remainder_signed_bilinear_b0_identity.py`
- `scripts/surface_remainder_signed_bilinear_parallel_candidate_production_20260722.txt`
- `scripts/surface_remainder_signed_bilinear_parallel_candidate_replay_20260722.txt`
