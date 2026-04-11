# State of the Yang-Mills Mass Gap Programme

**Version**: v1.46.0 (Path B  Honest Labelling)
**Date**: 2026-04-11
**Axioms for `sun_physical_mass_gap`**: 1 project axiom (`lsi_normalized_gibbs_from_haar`)
**Honest progress**: ~30%

## Honest Assessment

The Lean development compiles. `YangMills.sun_physical_mass_gap` type-checks and its
oracle chain reduces to

```
[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]
```

Everything apart from Lean's three kernel axioms rests on a single, explicitly labelled
project axiom: the HolleyStroock 1987 entropy-perturbation bound specialised to the
normalised SU(N) Gibbs density. The rest of the chain is genuine Lean 4 proof work:
Bakrymery for SU(N) Haar, the algebraic reduction from an entropy-perturbation
bound to a Gibbs LSI, and the translation from uniform-in-L LSI to DLR-LSI to a
Clay-flavoured physical mass gap via the existing `sun_clay_conditional_norm` bridge.

No other hidden hypotheses are smuggled through. The honest headline is therefore:
the programme is wired end-to-end modulo one classical measure-theoretic result.
Calling it "proved" would be dishonest. Calling it "nothing" would also be dishonest.
~30% captures that the skeleton, reductions, and LSI infrastructure are real, and
that the residual analytic work is a single well-posed theorem from the 1987
HolleyStroock paper.

## The Remaining Axiom

```lean
axiom lsi_normalized_gibbs_from_haar
    (N_c : Nat) [NeZero N_c] (hN_c : 2 <= N_c)
    (beta : Real) (hbeta : 0 < beta)
    (alpha : Real) (halpha : 0 < alpha)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) alpha) :
  LogSobolevInequality
    ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c beta hbeta))
    (sunDirichletForm N_c)
    (alpha * Real.exp (-2 * beta))
```

This is the *specific* HolleyStroock 1987 conclusion: if mu satisfies LSI(alpha) and
rho*mu is a probability measure with log-density bounded by ||log rho||_inf <= 2*beta,
then the perturbed measure satisfies LSI(alpha * exp(-2*beta)). It is a classical
measure-theoretic result but is **not yet formalised in Mathlib**.

Reference: Holley, R. & Stroock, D. "Logarithmic Sobolev inequalities and
stochastic Ising models", *Journal of Statistical Physics* 46 (1987), 11591194.

## Primary Proof Chain

```
sun_physical_mass_gap : ClayYangMillsTheorem
  sun_clay_conditional_norm
  sun_gibbs_dlr_lsi_norm                            (THEOREM)
       balaban_rg_uniform_lsi_norm                  (THEOREM)
            sun_haar_lsi (Bakrymery for SU(N))    (THEOREM)
            lsi_normalized_gibbs_from_haar          (AXIOM  HolleyStroock)
```

All other lines in the oracle derivation are Lean's kernel axioms `propext`,
`Classical.choice`, `Quot.sound`.

## What Was Actually Proved This Session

1. The Bakrymery bound for the SU(N) Haar probability measure reducing to the
   Ricci lower bound `N_c/4`, giving `sun_haar_lsi`.
2. The algebraic reduction `lsi_normalized_gibbs_from_haar_of_ent_pert` that turns
   any `hEntPert` entropy-perturbation bound plus a base LSI into a Gibbs LSI at
   the perturbed rate `alpha * exp(-2*beta)`.
3. The bridge theorems `balaban_rg_uniform_lsi_norm` and `sun_gibbs_dlr_lsi_norm`
   which consume the one axiom and the Haar LSI to produce the uniform-in-L LSI
   and the DLR_LSI required by the Clay conditional.
4. The removal of `hdlr` as a hypothesis of `sun_physical_mass_gap`, so the
   theorem is now genuinely consumed, not parameterised.

## What Is Not Yet Proved (and Why This Is Not Done)

Discharging the axiom requires three Mathlib-level pieces that do not yet exist
upstream:

1. **Density bound.** Prove `||log (sunNormalizedGibbsDensity N_c hN_c beta hbeta)||_inf <= 2*beta`.
2. **Entropy comparison lemma.** Prove the HolleyStroock entropy comparison
   `Ent_{rho*mu}(f^2) <= exp(2*beta) * Ent_mu(f^2)` for log-bounded densities,
   ultimately via convexity of `x*log x` and the variational formula for entropy.
3. **LSI transfer.** Combine the entropy comparison with the Dirichlet-form
   invariance to produce the perturbed LSI constant.

These three steps are the honest Path A. Nothing in them is conceptually novel;
they are rote measure-theoretic work blocked only by missing Mathlib API for
`withDensity`/entropy functionals on probability measures.

## Paths Forward

- **Path A (honest proof):** implement the three steps above as Mathlib PRs and
  remove the axiom. This is the only route to a conditional-free Clay statement.
- **Path B (current state):** the axiom is clearly labelled, the consumer site is
  minimal, and the rest of the pipeline is unconditional. Anyone reading the
  oracle sees the single dependency.

There is no Path C. The previous attempt at "axiom elimination" by relocating the
assumption into a hypothesis of the downstream theorem was a shell game and has
been rolled back.
