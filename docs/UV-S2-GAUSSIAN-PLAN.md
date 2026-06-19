# UV-S2 GAUSSIAN PLAN — the renormalized-Gaussian covariance contraction

**Date:** 2026-06-12.  **Status:** OPEN (brick G1 in progress).

S2 of `docs/UV-U1-SMALL-FIELD-PLAN.md`: turn the *deterministic*
ℓ²-contraction of the averaging operator (`linAvg_l2_contraction`,
`∑‖QA‖² ≤ L⁻¹∑‖A‖²` for `d ≥ 3`, ledger Add. 43–44) into the
**covariance contraction under the renormalized Gaussian measure** that
the small-field RG step actually requires.

## Mathlib status (verified 2026-06-12) — the measure framework EXISTS

Contrary to the earlier "Mathlib lacks Gaussian measures" assumption,
`Mathlib/Probability/Distributions/Gaussian/` provides:

* `ProbabilityTheory.IsGaussian` — a class for Gaussian measures on a
  topological `ℝ`-vector space (characterised via one-dimensional
  marginals `μ.map L = gaussianReal …` for dual `L`), with Fernique
  integrability and characteristic-function lemmas;
* **`isGaussian_map (L : E →L[ℝ] F) : IsGaussian (μ.map L)`** — an
  *instance*: the pushforward of a Gaussian under a **continuous linear
  map** is Gaussian.  This is exactly the (free) renormalization-group
  step: if the fine field is Gaussian and `Q` is a CLM, the coarse field
  is Gaussian;
* `IsGaussian.map_eq_gaussianReal`, `Var[L; μ]` — the covariance is
  recoverable through dual functionals, so the *transformed* covariance
  `L ↦ Var[L ∘ Q; μ]` is accessible and is bounded by `linAvg_l2_le`.

So the free-field structure is **reachable** on existing infrastructure;
the genuine wall is the *interacting* (non-Gaussian Yang–Mills) measure
and the specific gauge propagator bound.

## Brick ladder

| Brick | Content | Status |
|---|---|---|
| **G1** | **`Q` as a continuous linear map** `linAvgCLM : (E_fine) →L[ℝ] (E_coarse)` (finite-dimensional fibres; linearity is `linAvg_add`/`linAvg_smul`).  The object `isGaussian_map` consumes. `RG/AveragingL2.linAvgCLM` (+ `linAvgCLM_apply`). | **CLOSED** (ledger Add. 45, core 8247) |
| **G2** | **Free lattice Gaussian field** as an `IsGaussian` measure on the bond-field space `E = ConcreteEdge → V` with a prescribed covariance (the prototype: mass-term / identity covariance). | reachable |
| **G3** | **Free RG step = Gaussian pushforward**: `(linAvgCLM)_* μ` is Gaussian (`isGaussian_map`); its covariance is `Q C Qᵀ` — the **covariance transformation law** `covarianceBilinDual (μ.map Q) L L = covarianceBilinDual μ (L∘Q) (L∘Q)`, proved abstractly for any CLM. `RG/GaussianStep.covarianceBilinDual_map_clm`. | **CLOSED** (ledger Add. 46, core 8248) |
| **G4** | **Free covariance contraction by `‖Q‖²`**: given a covariance bound `Cov(μ)[M,M] ≤ B‖M‖²` (the CMP 95 input `‖C_k‖ ≤ cL²`), `Cov(μ.map Q)[L,L] ≤ B·‖Q‖²·‖L‖²`. With `‖Q‖² ≤ L^{2-d}` (linAvg_l2) this is the free per-scale contraction. `RG/GaussianStep.covarianceBilinDual_map_le`. | **CLOSED** (ledger Add. 47, core 8248) |
| **G4′** | **Hilbert-space adjoint mass `Q†Q`**: the scaled averaging map on bond `ℓ²`/`PiLp 2` spaces, with explicit scalar `s`, and the positive mass `qMassCLM = (sQ)†(sQ)`.  Proves `⟪A,Q†Q A⟫ = ‖QA‖²`, PSD, and `‖Q†Q‖ ≤ ‖Q‖²`. | **CLOSED** (ledger Add. 144, core 8274) |
| **G5** | **Interacting correction** (the genuine analytic core): the Yang–Mills measure is `Gaussian · exp(−interaction)`; the RG step is the fluctuation integral with the small/large-field split, and the covariance contraction must survive the interaction.  Bałaban CMP 95–96 + 122; months-scale. | **campaign (the wall)** |

## Honest scope

G1–G4 are a genuine, reachable free-field sub-campaign (a few sessions,
building directly on `IsGaussian`/`isGaussian_map` and the proven
operator contraction) — they formalise the **Gaussian fixed-point**
analysis.  They do **not** discharge (UV-core): the actual RG remainder
`R_k` is a property of the *interacting* measure, and **G5** — the
fluctuation-integral control with the large-field suppression — is
Bałaban's genuine analytic heart, a months-scale constructive-QFT
formalisation.  Direct Clay relevance after even a full S2/U1/U2
discharge remains ~0% (<0.1%): M4/M5 (continuum limit, OS reconstruction)
are untouched.

## Precise source request (for G5, the interacting core)

To build G5 non-vacuously (not the forbidden vacuous `ClayCore/Balaban*`
scaffolding) I need, with equation-level precision:

1. **Bałaban, CMP 95 (1984), §2–3** — the explicit bound on the
   **fluctuation-field covariance** `C_k` of the single RG step (the
   propagator estimate `‖C_k(x,y)‖ ≤ const·e^{−c|x−y|}` and the
   `L`-scaling of its ℓ²/operator norm).  This is the analytic input the
   deterministic `linAvg_l2_contraction` must be combined with.
2. **Bałaban, CMP 96 (1984)** — the RG transformation law for the
   covariance across one block step (how `C_{k+1}` is obtained from
   `C_k` and `Q`).
3. **Bałaban, CMP 122-II, Theorem 1** (already referenced) — the
   target single-scale stability statement, to fix the exact form of
   `|R_k| ≤ M·rᵏ`.
4. (Method shape, optional) **Dimock, "RG according to Bałaban" II** —
   the cleanest exposition of the fluctuation integral / small-field
   step for the scalar prototype, to mirror the proof architecture.

A clean transcription of the covariance bound (CMP 95 eqs in §2–3) is
the single most useful item; with it, G5 becomes *specifiable* as a
Lean target rather than reconstructed from memory (declined on honesty
grounds).
