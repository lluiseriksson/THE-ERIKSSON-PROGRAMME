# Theta-prism SU(2) geometry pre-audit — 2026-07-31

## Status

**Read-only adversarial pre-audit of an abstract cell.**  This record is not a
Lean theorem, does not certify a physical `GaugeConfig` realization, does not
establish reflection positivity, and does not count as the terminal SU(2)
Gate 7.  The audited cell is not yet an object in this repository.

The auditor worked cold and did not inspect design conversations, other audit
reports, new two-transporter branches, Fable, or the permitted reference
commit.  No repository file was edited or compiled during the audit.

## Abstract cell

Let `G = SU(2)` with normalized product Haar measure.  The positive half has
three parallel links `A0,A1,A2 : a+ -> b+`; the negative half has
`B0,B1,B2 : a- -> b-`; the crossing links are `s : a- -> a+` and
`t : b- -> b+`.  The three plaquette words are

```text
H_i = s A_i t^-1 B_i^-1.
```

Reflection interchanges `A_i` and `B_i` and sends `s,t` to their inverses.

## Verdicts within the geometric remit

| Claim | Verdict | Exact scope |
|---|---|---|
| Each half has `b1 = 2` | **PASS** | The physical half is a theta multigraph: `E=3`, `V=2`, `C=1`. |
| Gauge quotient retains two loops | **PASS** | With `U=A0^-1 A1`, `V=A0^-1 A2`, residual gauge is simultaneous conjugation; the quotient is `G^2 / Ad G`, not one loop. |
| Delete the third branch | **PASS, topological part only** | Removing `A2,B2` and the third plaquette gives `E=2`, `V=2`, hence `b1=1`.  Disappearance of the representation sector `(1,1/2,1/2)` was outside this auditor's remit and remains deferred. |
| Reflection and Haar compatibility | **PASS** | Pointwise, `theta(H_i) = s^-1 H_i^-1 s`, hence the fundamental SU(2) trace satisfies `chi(theta(H_i)) = chi(H_i)` without a change of variables. |

Two terminology constraints are load-bearing:

1. The physical half is a multigraph with two vertices and three parallel
   edges.  `K(2,3)` is its incidence graph, equivalently its barycentric
   subdivision; it is not the physical graph itself.
2. Integrating the crossing links produces the two-sided gauge average only
   inside the complete product-Haar integral.  It must not be described as an
   isolated operation on an arbitrary function of the `A_i`.

## Independent obstruction to a hidden one-loop collapse

After fixing `A0=1`, the stabilizer acts by

```text
(U,V) -> (k U k^-1, k V k^-1).
```

There is no further continuous gauge action eliminating one generator.  For
`q = diag(exp(i alpha), exp(-i alpha))`, `0 < alpha < pi`, the pairs `(1,1)`
and `(q,q)` have the same `U^-1 V = 1` but are not simultaneously conjugate,
because their first traces differ.  Thus a description by a single relative
loop loses information.

## Incidence-rule correction bought by the audit

The proposed rule "an edge occurring once can be removed by Haar integration"
was too strong.  Leaf/one-incidence elimination is valid only when that edge
appears exclusively in the weight.  It is invalid when the observable also
depends on the edge.  Every `A_i` has one plaquette incidence, yet an observable
`F(A0,A1,A2)` can retain it.  A lone nontrivial character integrates to zero;
that fact does not delete the variable from the coupled exponential or from
`F theta(F)`.

This correction must be applied to any future two-transporter design before a
formal gate is pre-registered.

## Measure and integrability check

For real `beta`, `|chi(g)| <= 2` gives

```text
0 < W_beta <= exp(3 |beta|).
```

For `F` in `L^2(G^3)`, normalized Haar and Cauchy--Schwarz give

```text
integral |W_beta F theta(F)| <= exp(3 |beta|) ||F||_2^2.
```

Thus the required Fubini/Tonelli rearrangements are legitimate for every real
`beta`.  At `beta=0` a nonzero mean-zero observable can have zero pairing; for
`beta<0` the integrability and reflection identities survive, but positivity
does not follow from them.

## Remaining gates

- A separate read-only representation audit has now passed the pure
  `(1,1/2,1/2)` sector, the factor `1/16`, and the pre-registered
  `beta^4/512` lower bound on `0<beta<=1`.  Its scope and a disclosed
  annotated-tag contamination are recorded in
  [`THETA-PRISM-REPRESENTATION-PREAUDIT-20260731.md`](THETA-PRISM-REPRESENTATION-PREAUDIT-20260731.md).
- No physical lattice embedding, `GaugeConfig` bridge, `ReflectionSplitting`
  theorem, Lean module, terminal Fable audit, paper, or submission is licensed
  by either pre-audit PASS.
