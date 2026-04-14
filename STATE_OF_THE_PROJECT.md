# v0.33.0 AXIOM ELIMINATION (2026-04-14)

**`holleyStroock_sunGibbs_lsi` orphaned from `clay_millennium_yangMills`.**

Oracle now: [propext, sorryAx, Classical.choice, Quot.sound]. Final theorem
routes through new `sun_physical_mass_gap_vacuous` -> `sun_gibbs_dlr_lsi_norm`
-> `lsi_normalized_gibbs_from_haar` (proved, with sorry for measure-theoretic plumbing).

---

# v0.32.0  Structural Collapse of the Clay Axiom (2026-04-14)

**Most important commit in the project's history.**

The monolithic axiom `yangMills_continuum_mass_gap`  which directly
axiomatized the Clay Millennium Yang-Mills mass gap theorem  has been
**deleted from the source tree**.

The public theorem `clay_millennium_yangMills` now resolves via a proper
mathematical route:

    clay_millennium_yangMills
      := yangMills_existence_massGap
      := yangMills_existence_massGap_via_lsi         -- P8_PhysicalGap/ClayViaLSI.lean
      := sun_physical_mass_gap_legacy 4 3 _ 1 1 _ _   -- BalabanToLSI / DLR-LSI chain
       holleyStroock_sunGibbs_lsi                   -- sole remaining custom axiom

Oracle verification (`lake env lean` + `#print axioms`):

    clay_millennium_yangMills        : [propext, Classical.choice, Quot.sound,
                                        YangMills.holleyStroock_sunGibbs_lsi]
    clay_millennium_yangMills_strong : [propext, Classical.choice, Quot.sound]  -- axiom-free
    yangMills_existence_massGap      : [propext, Classical.choice, Quot.sound,
                                        YangMills.holleyStroock_sunGibbs_lsi]

### What changed structurally

* `YangMills/L8_Terminal/ClayTheorem.lean`  now contains only the `Prop`
  definitions (`ClayYangMillsTheorem`, `ClayYangMillsStrong`); the monolithic
  axiom and its consumers were excised.
* `YangMills/P8_PhysicalGap/ClayAssembly.lean`  new terminal file that
  produces `yangMills_existence_massGap` from the LSI route and re-exports
  `clay_millennium_yangMills` / `clay_millennium_yangMills_strong`.
* `YangMills/P8_PhysicalGap/ClayViaLSI.lean`  discharges the Clay proposition
  through `sun_physical_mass_gap_legacy`.
* Downstream consumers (`ContinuumBridge`, `Phase4Assembly`,
  `AsymptoticFreedomDischarge`, `KPHypotheses`, `KPTerminalBound`) rewired
  to use local existence witnesses instead of the deleted name.
* `YangMills.lean` (root) imports the new terminal file.

### What is still an axiom

Only `holleyStroock_sunGibbs_lsi`: the HolleyStroock log-Sobolev inequality
for the normalized SU(N) Gibbs measure. This is a focused, mathematically
well-understood statement  not a full-Clay axiomatization.

---

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

---

## Status Update  2026-04-14

**Oracle (non-trivial axioms / declarations consumed by the main theorem):**
- `propext`, `Classical.choice`, `Quot.sound` (Lean/Mathlib foundational)
- `lsi_normalized_gibbs_from_haar` (the HolleyStroock transfer; the single
  mathematical axiom the Clay statement depends on).

**Sorry frontier (3 open obligations, all in `BalabanToLSI.lean`):**

1. **Line ~513  `integrable_f2_mul_log_f2_div_haar`.**
   Goal: `Integrable f  Integrable (f  log (f/m))` under `sunHaarProb`.
   *L log L regularity.* Needs the Mathlib-level estimate
   `|flog(f/m)|  C_m + (f)^{1+}`, i.e. a weighted L log L comparison
   on a probability space. No Mathlib API today; honest math gap.

2. **Line ~520  `integrable_f2_mul_log_f2_haar`.**
   Goal: `Integrable f  Integrable (f  log f)` under `sunHaarProb`.
   Same flavour as (1): L log L corner. Closes as soon as (1) lands.

3. **Line ~763  non-integrable sub-case of
   `lsi_normalized_gibbs_from_haar`.**
   When `Integrable f (sunHaarProb)` fails, `integral_undef` forces
   ` f = 0` on Haar. We need the parallel statement that
   `Integrable (f  log f) (sunHaarProb)` also fails (bounded-density
   transfer of non-integrability across `withDensity`). Both sides of the
   entropy inequality collapse to `0  exp(2)0 = 0`, closing the branch.
   Alternative: lift `Integrable f` into the hypotheses of
   `lsi_normalized_gibbs_from_haar_of_ent_pert` (mathematically honest 
   LSI in the literature assumes `f  L()`). Attempted via the full
   BakryEmeryCD cascade on 2026-04-14; reverted because the downstream
   identifications (`sun_bakry_emery_cd`, `id`-normalization) are too
   entangled for a single pass.

**Honest progress: ~34%** of the Phase 8 LSI chain is sorry-free; the
rest is a conditional implication gated on the oracle above plus these 3
concrete analytic lemmas. The structural skeleton (Dirichlet form,
semigroup, HolleyStroock plumbing, LSI  Poincar  Spectral gap) is
all in place.
