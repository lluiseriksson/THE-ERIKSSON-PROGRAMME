# CONTINUUM-C1 closure

**Status: CLOSED as a negative result; not merged; no paper.**

CONTINUUM-C1 tested whether the repository's existing volume-uniform
two-plaquette Kotecky--Preiss window could be used along a continuum scaling
trajectory.  The answer for that specific window is negative.

At `t = epsilon = 1`, the checked correlator theorem assumes

```text
(16 d + 1)^2 exp(3)
  ((exp(|beta| N_c) - 1) + s + (exp(|beta| N_c) - 1) s) < 1,
```

with `s > 0`.  The C1 Lean artifact proves that this implies the finite,
volume-independent cap

```text
beta < log(1 + exp(-3)/(16 d + 1)^2) / N_c
```

for `beta >= 0` and `N_c > 0`.  Consequently the same hypothesis is eventually
false along every trajectory with `beta -> +infinity`, including
`beta(a) = 1/(g^2 a^2)`.

This is a no-go theorem for the **current strong-coupling KP radius**, not for
all cluster expansions and not for continuum Yang--Mills.  It proves no
tightness estimate, continuum state, Osterwalder--Schrader reconstruction, or
continuum mass gap.  The M4--M5/Clay frontier is unchanged.

## Frozen evidence

- Branch head:
  [`0a46e266fc4808332ed20d2ab4611bfc271b208b`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/0a46e266fc4808332ed20d2ab4611bfc271b208b)
- Review vehicle:
  [draft PR #34](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/34)
- Remote `honesty` check on that exact head: `SUCCESS`
- Direct Lean build recorded in the branch: exit `0`
- Seven oracle queries: exactly
  `[propext, Classical.choice, Quot.sound]`
- Textual producer/consumer canary plus adversarial mutation self-test: `PASS`
- Repository consistency checker: `PASS`

The canary is a drift alarm, not a proof.  The proof is the typed Lean
artifact; the canary ensures that hosted CI notices textual divergence between
the copied C1 radius and the actual correlator hypothesis.

## Successor contracts

Two handoffs remain, neither of which is unfinished C1 work:

1. The continuum programme needs a producer that is genuinely uniform in the
   cutoff rather than a continuation of this strong-coupling window.
2. The first reusable analytic bridge for the positive two-dimensional Wilson
   route is the identification of the repository's Gamma-series Bessel
   function with its order-zero and order-one Fourier integral
   representations:

   ```text
   besselIReal_integral_repr_zero
   besselIReal_integral_repr_one
   ```

The branch remains deliberately outside `main`.  Any later integration must
update it against the then-current `main` and rerun Lean and CI.
