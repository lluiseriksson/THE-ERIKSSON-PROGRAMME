# High-beta lambda eighteen-fifths interior result

**Executed:** 2026-07-28

**Source head:** `f30e918676a4149384d461a1bb11f23bd41e9a80`

**State:** certified production/replay pair

## Result

The preregistered 180-bit Arb sweep completed on 2,176 parameter boxes:

```text
beta>=1000/9,
lambda=beta(pi-t)>=18/5,
p=sin(t/4)>=101/200.
```

The fixed-gap certificate already covers `p<=101/200`.  On the
complementary domain the sweep proves

```text
rho < 0.014749020,
absolute main-plus-mirror adverse correction < 0.877342.
```

The independently certified third-block rest correction is below
`1/100000`.  Since the non-bilinear term satisfies `Q>19/20`, the frozen
relay gives

```text
19/20 - 9/10 - 1/100000 = 0.04999 > 0.
```

Thus the complete high-beta interior with `lambda>=18/5` is closed.

## Reproduction

```powershell
python scripts/certify_surface_high_beta_lambda18_5_interior.py
python scripts/validate_surface_high_beta_lambda18_5_interior.py
python -m pytest -q `
  tests/test_surface_high_beta_lambda18_5_design.py `
  tests/test_surface_high_beta_lambda18_5_validator.py
```

The production and replay transcripts are byte-identical, with SHA-256

```text
386e932d9b90644bf33406a34c60bb24eee4d8c5911765a8d614d66d835dde87
```

and are committed beside the validator.

## Remaining scope

The direct G5 union is certified only through `lambda=2`.  The sole
remaining high-beta interval is now

```text
2 < lambda < 18/5.
```

The preregistered local-tail G5 campaign targets exactly this interval and
is not assumed by this result.
