# Positive-lane delta-four remainder contract

**Registered:** 2026-07-12, after exact extraction of `r4` and before any
uniform delta-four remainder result  
**State:** `DESIGN_GATE`; no G2 promotion

Write

```text
Y(delta,t) = T(c) + r2(c) delta + r3(c) delta^2
             + r4(c) delta^3 + R5(delta,c),
c = cos(t/4),
r4(c) = (28c^8+41c^6-1464c^4+1856c^2-500)/(1024c^12).
```

The terminal positive-lane target is fixed as

```text
abs(R5(delta,c)) <= 384 delta^4
```

for `0<=delta<=1/20` and `1/sqrt(2)<=c<=1`.  An outward-rounded
1,000-box budget sweep proves that this target, together with the exact
`r3,r4`, lies strictly inside the pre-existing `Theta3 delta^2` direct
judge; its worst certified residual coefficient is greater than `384.08`
before rounding down to the registered integer 384.

The delta birth partition and t coverage remain those of
`SURFACE-REMAINDER-K2-PARTITION.md`.  Local subdivision may prove this
fixed target but may not raise 384, discard a t range, or replace absolute
error by relative error.  The endpoint `[0,1/1000]` certificate is an
independent overlap/audit; it does not by itself prove this stronger
four-term remainder statement.

A terminal certificate must charge the order-five Bessel companion,
geometry/exponential Taylor remainder, fixed physical completion, and every
moving/localization term.  It must print born and terminal boxes, strict
minimum margin, hashes, versions, and a terminal coverage verdict owned by a
run manifest and executable validator.
