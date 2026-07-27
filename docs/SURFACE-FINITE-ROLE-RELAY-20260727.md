# Surface finite-beta role relay

**State:** `FINITE_ROLE_PROVED`

This record binds the already certified range witnesses to the exact
Wronskian algebra.  It closes the logical relay on

```text
20 <= beta <= 1000/9,   0 < t < pi.
```

It is intentionally independent of K2 and of the obsolete split-tail
hypothesis `(H_tail)`.

## Partition

| t range | witness |
|---|---|
| `0<t<=3/5` | certified G4 scaled-left union |
| `3/5<=t<=pi-3/(2 beta)` | exact-union scaled bulk cover |
| `pi-3/(2 beta)<=t<pi` | certified G5 union |

The authoritative bulk audit checks strict negative upper endpoints,
production/replay equality, output hashes, exact rational beta union, the
moving seam at each box's **upper** beta endpoint, and an adjacent canonical
ownership subcover.  It reports the exact beta component `[20,1000/9]` with
no gap.

## Exact implication

Theorem A gives `F_B>0`.  Exact differentiation and the common positive
family scaling give

```text
W = 4 F_B^2 E',
W_scaled = positive_factor * W.
```

Therefore every strict `W_scaled<0` certificate implies `E'<0`.  Since the
three t ranges above cover `(0,pi)`, the finite-beta conclusion follows.

The executable role audit is
`scripts/audit_surface_finite_role_relay.py`.  It imports and reruns the
authoritative union audit, reruns the dependency-free sign algebra, requires
G4 and G5 to be `CERTIFIED` on the closure board, and checks the exact
Theorem A statement in the manuscript.

## Reproduction

```powershell
python scripts/audit_surface_finite_role_relay.py
python -m pytest -q tests/test_surface_finite_role_relay.py
```

This is a finite-range promotion only.  It does not promote K2, the
high-beta half-line, K4, S1'''/S2''', or the final paper seal.
