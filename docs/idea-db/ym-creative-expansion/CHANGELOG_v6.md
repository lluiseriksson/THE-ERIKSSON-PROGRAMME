# CHANGELOG v6 — Batch-006 live-field control edition

## Added

- Batch-006 integration brief for the Gaussian/root/Hessian/activity/H# map.
- Raw-source M3 field DAG and field burndown matrix.
- 15 new mission contracts `OC_016`–`OC_030`.
- 15 new proof-obligation field cards `PO_13`–`PO_27`.
- 30 new derived cards `D76`–`D105`.
- Field-specific source extraction worksheets and theorem skeletons.
- `field_board.py`, `check_no_backfill.py`, `batch006_prompt_compiler.py`,
  `source_acquisition_planner.py`, and `validate_v6_live_fields.py`.

## Changed

- The highest-level harness now has two active lanes:
  1. Eq. (2.31) hypothesis-removal lane.
  2. Batch-006 raw-source live-field lane.
- Patch scoring now penalizes downstream backfill and monolithic raw-source
  packages more strongly.

## Boundary

v6 remains operational metadata only.  It does not promote any source key, prove
`hRpoly`, or provide any source evidence.
