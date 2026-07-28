# High-beta G5 ratio-side4 lambda-three result

**Verdict:** `CERTIFIED`

The preregistered terminal campaign closes

```text
delta in [0,9/1000],
lambda=beta(pi-t) in [2,3].
```

Ten production units and ten fresh replay units were run sequentially from
source head `4a5e9a6d8e4cfdd07b1277a6a61172e23e3ba7be`.  Production completed
before replay was launched.  Both runs contain 450/450 exact rational cells,
ten terminal verdicts, zero failure markers, and zero stderr bytes.  Every
corresponding transcript is byte-identical.

## Frozen result

```text
authoritative LF-stable aggregate SHA-256:
f3f76e1d65a9ef825ed78d5cad98ae3ec1a32f3d00068ebad207dfde3fe5ab11

raw CRLF aggregate at execution time:
06672f8033b73182f4bdef0695585428f3aa5b538555fbb563078055a3e7ba68

minimum B0 lower endpoint:
0.064125001634404030... at (lambda_index,delta_index)=(100,8)

minimum Qratio lower endpoint:
0.00003816825355509069... at (lambda_index,delta_index)=(146,8)

resolution counts:
436 coarse-ratio, 14 mixed-ratio
```

The validator checks the exact 50-by-9 union, cell endpoints, positive
`B0` and `Qratio` enclosures, five nonnegative tail budgets per row,
allowed resolution labels, source and dependency hashes, the angular-grid
configuration omitted from the compact transcript header, manifest
chronology, exact production/replay bytes, and both raw and LF-stable
digests.  The LF digest is authoritative across Git checkouts.

Because the exact algebra audit proves `P0=B0*Qratio`, the two strict lower
endpoints imply `P0>0` without subtracting independent large product
intervals.  This supplies the moving-edge lane `2<=lambda<=3`; it does not
by itself assert the full high-beta theorem.

## Reproduction

```powershell
python scripts/validate_surface_high_beta_g5_ratio_side4_lambda3.py
python -m pytest -q tests/test_surface_high_beta_g5_ratio_side4_lambda3_validator.py
```

The complete timing, dependency and per-file hash record is
`run-records/legacy/surface-high-beta-g5-ratio-side4-lambda3-20260728.json`.
