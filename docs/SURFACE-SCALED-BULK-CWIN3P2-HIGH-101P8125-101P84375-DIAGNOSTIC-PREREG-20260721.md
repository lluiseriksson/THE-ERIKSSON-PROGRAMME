# Finite-beta seam diagnostic preregistration

**Registered:** 2026-07-21, before execution  
**Status:** `DIAGNOSTIC_ONLY`; no G2/G6 promotion

This is one bounded retry of the first uncovered finite-beta unit after the
current candidate union `[20,101.8125]`.  It uses the already registered
CWIN=`3/2` high-order scaled sign-row contract, with no change to its
Taylor orders, precision, beta domain rule, or minimum `t` width:

```text
beta domain   [101.8125,101.84375] = [3258/32,3259/32]
beta order    30
t order       37
precision     180 Arb bits
min_dt        1/100000
```

The run is a feasibility diagnostic only.  A green result would still need a
fresh production/replay pair, a manifest, and the finite-beta union validator;
it cannot alter G2 by itself.  A failure or timeout is terminal evidence
against this fixed unit contract and does not authorize unregistered
subdivision.
