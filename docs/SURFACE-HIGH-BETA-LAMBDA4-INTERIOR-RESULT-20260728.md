# High-beta lambda-four interior result

**Executed:** 2026-07-28

**Source head:** `56bab787526e2b3a0d2b6c9b1ce059465bf1c8b0`

**State:** certified production/replay pair

## Result

The preregistered 180-bit Arb sweep completed on 2,176 parameter boxes:

```text
beta>=1000/9,
lambda=beta(pi-t)>=4,
p=sin(t/4)>=101/200.
```

The fixed-gap certificate already covers `p<=101/200`.  On the complementary
domain the sweep proves

```text
rho < 0.008421810,
absolute main-plus-mirror adverse correction < 0.495932.
```

The independently certified third-block rest correction is below
`1/100000`.  Since the non-bilinear term satisfies `Q>19/20`, the final
outward-rounded relay margin is

```text
19/20 - 3/4 - 1/100000 = 0.19999 > 0.
```

Thus the complete high-beta interior with `lambda>=4` is closed without the
two previously open ratio-sign lemmas.

## Reproduction

```powershell
python scripts/certify_surface_high_beta_lambda4_interior.py
python scripts/validate_surface_high_beta_lambda4_interior.py
python -m pytest -q tests/test_surface_high_beta_lambda4_interior.py `
  tests/test_surface_high_beta_lambda4_interior_validator.py
```

The production and replay transcripts are byte-identical, with SHA-256

```text
2435d37961ae5a4dd76c0c04f14ac4b3c9aaae7099ace9d34c952ebc19088ec8
```

and are committed beside the validator.

## Remaining scope

The certified direct G5 union reaches `lambda=2`.  The only remaining
high-beta interval is therefore

```text
2 < lambda < 4.
```

The uniform `exp(4)` five-family tail ledger is being tested separately and
is not assumed by this result.
