# CWIN=8/5 seam diagnostic timeout

The preregistered successor bulk unit

```text
beta=[3258/32,3259/32], CWIN=8/5,
beta_order=30, t_order=37, Arb=180 bits, min_dt=1/100000
```

was run with the scoped G5 `lambda in [3/2,8/5]` extension as the intended
overlap witness.  The process reached the cached backend but emitted no
terminal sign row before the fixed five-minute timeout (`exit 124`).  No
production transcript or manifest was produced.

Moving the cut from `3/2` to `8/5` therefore does not by itself resolve the
finite-beta conditioning wall.  The scoped G5 certificate remains valid as an
independent result, but this CWIN=8/5 bulk continuation is retired.  G2/G6
are unchanged; a grouped cancellation evaluator or a new analytic splice is
required.
