# High-beta lambda-three joint interior result

**Executed:** 2026-07-28

**Source head:** `77fe27772e8a1686bbaf1194042925dadee37bce`

**State:** certified production/replay pair

## Result

The preregistered 180-bit Arb sweep completed on 2,560 common-`x`
parameter boxes:

```text
beta>=1000/9,
lambda=beta(pi-t)>=3,
p=sin(t/4)>=101/200.
```

Instead of multiplying independent marginal maxima, each box retained the
common physical variable through the principal moment bounds, mirror mass
ratio, and completed adverse expression.  The result is

```text
rho < 0.034107219,
joint main-plus-mirror adverse correction < 0.852989079.
```

The fixed-gap certificate handles `p<=101/200`, and the independently
certified third-block correction is below `1/100000`.  With the
non-bilinear certificate `Q>19/20`, the frozen relay is

```text
19/20 - 9/10 - 1/100000 = 0.04999 > 0.
```

Thus the complete high-beta interior with `lambda>=3` is closed.  This
strictly supersedes the weaker lambda-four and lambda-eighteen-fifths
interior thresholds without changing their valid certificates.

## Reproduction

```powershell
python scripts/certify_surface_high_beta_lambda3_joint_interior.py
python scripts/validate_surface_high_beta_lambda3_joint_interior.py
python -m pytest -q `
  tests/test_surface_high_beta_lambda3_joint_design.py `
  tests/test_surface_high_beta_lambda3_joint_validator.py
```

The production and replay transcripts are byte-identical, with SHA-256

```text
a2e9f9b7db49ddc3b6186552ef33c0b7bb6d15cc2a64929137e3f3032bc8f4c9
```

and are committed beside the validator.

## Remaining scope

The direct G5 union is certified through `lambda=2`.  The sole remaining
high-beta interval is now

```text
2 < lambda < 3.
```

The cancellation-preserving wider-chart campaign under design targets
exactly this interval and is not assumed by this result.
