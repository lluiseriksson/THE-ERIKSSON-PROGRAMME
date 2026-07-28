# High-beta G5 lambda-two result

**Executed:** 2026-07-27

**Source head:** `613ed42d840e1e4d554c053fe81ae6f0c2aea40a`

**State:** certified production/replay union

## Result

The frozen campaign in
`SURFACE-HIGH-BETA-G5-LAMBDA2-PREREG-20260727.md` completed twice from the
same source head:

```text
delta in [0,9/1000],
lambda=beta(pi-t) in [3/2,2].
```

The exact union contains 225 cells.  Every cell proves with
outward-rounded Arb arithmetic

```text
B0>0, P0>0, H=P0/(4 B0^2)>0.
```

The worst lower endpoint is

```text
H_lower =
0.0200479966588318347930908203125...
```

at `delta_index=0`, `lambda_index=99`.  All five production units and all
five replay units terminate with `CERTIFIED`; every error stream is empty.

## Reproduction

The committed transcripts are in

```text
scripts/surface_high_beta_g5_lambda2_production_20260727/
scripts/surface_high_beta_g5_lambda2_replay_20260727/
```

Run

```powershell
python scripts/validate_surface_high_beta_g5_lambda2.py
python -m pytest -q tests/test_surface_high_beta_g5_lambda2_validator.py
```

The validator requires:

- exact parsed-row equality between production and replay;
- the exact 225-cell rational union with no duplicates;
- positive `B0`, `P0`, and `H` lower endpoints;
- the frozen dependency hashes;
- one source head across all ten transcripts.

## Scope

This closes the direct G5 strip `3/2<=lambda<=2`.  It does not by itself
promote K2, K4, G2, G6, or the final manuscript seal.  The remaining
high-beta interior obligation is tracked by the corrected three-block
bilinear contract.
