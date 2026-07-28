# Current-head pair mean-value cell — result

**State:** candidate evidence only; no G2/G6 promotion

The cell `beta=[1629/16,3259/32]`, `lambda=[3/2,19/10]` was regenerated
under the current source head with 115 modes, beta/lambda Taylor orders
`50/50`, and 500 Arb bits.

- Production and replay both pass and are byte-identical.
- SHA-256 of both transcripts:
  `cea16b163d9c3e25571a15ad5f9dd24e89a2e60c6befcef997a439709e56c8af`.
- Outward-rounded `total_upper`:
  `-4.290376557020880438567038819302428324274214220431999351767500629117481403525452902853241537784427322e-109 +/- 4.80e-209`.
- The current-head manifest is
  `run-records/legacy/surface-scaled-pair-mean-value-cell-beta101p8125-101p84375-current-20260724.json`.
- The executable provenance check is
  `scripts/validate_surface_scaled_pair_mean_value_current_cell.py`; it
  rechecks the production/replay hash, all six dependency hashes, rational
  cell bounds, and the strict Arb sign.

This repairs provenance for one narrow candidate cell only. It does not
provide the surrounding beta/t union, the absolute `(H_tail)` relay, K2, G2,
or G6.
