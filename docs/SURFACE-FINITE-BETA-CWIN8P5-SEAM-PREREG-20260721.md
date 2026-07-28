# Finite-beta bulk seam with `CWIN=8/5`

**Registered:** 2026-07-21, after the scoped G5 lambda extension audit  
**Status:** `DIAGNOSTIC_ONLY`; no G2/G6 promotion

The scoped G5 certificate now covers `lambda in [3/2,8/5]` on the five
registered delta bands for `30 <= beta <= 125`.  This preregisters one
successor bulk diagnostic that leaves the overlap exact and moves the bulk
cut to `CWIN=8/5`:

```text
beta domain   [3258/32,3259/32] = [101.8125,101.84375]
bulk t-domain 3/5 <= t <= pi - (8/5)/beta
beta order    30
t order       37
precision     180 Arb bits
min_dt        1/100000
```

The only changed datum is the registered rational cut.  A green result is
still a diagnostic until a fresh CWIN=8/5 finite-beta production/replay union,
its exact splice validator, and a gate review are complete.  A timeout or
failure retires this successor for the unit and authorizes no silent
subdivision.
