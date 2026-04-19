/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonClusterIdentity
import YangMills.ClayCore.KPSmallness

/-!
# Phase 15j.3: Wilson Cluster Proof (honest partial delivery)

## Why this file does NOT claim an unconditional closure of `h_cluster`

The plain target — deriving `ClusterCorrelatorBound` directly
from `WilsonPolymerActivityBound` alone — is not provable
under the current structure.  `wab.K` is abstract (satisfies
only the amplitude bound `|K γ| ≤ A₀ · r^|γ|`) and has no
intrinsic connection to `wilsonConnectedCorr`.  A vacuous
`wab.K ≡ 0` satisfies the amplitude bound trivially while
`wilsonConnectedCorr` for nontrivial `F` is generally
nonzero, so the two are logically decoupled without a linking
hypothesis (which is precisely the Bloque4 Theorem 7.1
content — hard Kotecky-Preiss cluster expansion).

## What this file DOES deliver

The purely algebraic bridge from the geometric / polymer-size
shape `r^dist` (Balaban-Lemma-3 form) to the exponential /
Kotecky-Preiss shape `exp(-(kpParameter r) · dist)` (the form
consumed by `clay_yangMills_large_beta`):

    r ^ x ≤ exp(-(kpParameter r) · x)    for r ∈ (0,1), x ≥ 0.

Plus two reduction theorems that chain through it:

* `clusterCorrelatorBound_of_rpow_bound` — given a pointwise
  correlator bound `|corr(p,q)| ≤ C · r^dist`, produce
  `ClusterCorrelatorBound N_c r C`.
* `clay_theorem_of_rpow_bound` — chain the rpow-shape
  pointwise bound through `WilsonPolymerActivityBound` all
  the way to `ClayYangMillsTheorem`.

The hard analytic content — the pointwise correlator bound
in rpow-shape itself — remains an input hypothesis, in
exactly the form Bloque4 Theorem 7.1 delivers.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry. No new axioms.

References:
* Bloque4 §7.2, Theorem 7.1.
* Kotecky-Preiss, Commun. Math. Phys. **103** (1986).
* Balaban, Commun. Math. Phys. **116** (1988), Lemma 3.
-/

namespace YangMills

open scoped BigOperators
open Real

/-! ## Algebraic bridge: r^x ≤ exp(-(kpParameter r) · x) -/

/-- **Phase 15j.3, core lemma.**  For `r ∈ (0,1)` and `x ≥ 0`:

    `r ^ x ≤ exp(-(kpParameter r) · x)`.

Proof.  `kpParameter r = -log r / 2`, so
`-(kpParameter r) · x = (log r / 2) · x`.  Using
`r^x = exp(log r · x)` (from `Real.rpow_def_of_pos`), the
inequality reduces to `log r · x ≤ log r · x / 2`, which holds
because `log r ≤ 0` (since `0 < r < 1`) and `x ≥ 0`. -/
theorem rpow_le_exp_kpParameter
    {r : ℝ} (hr_pos : 0 < r) (hr_lt1 : r < 1)
    {x : ℝ} (hx : 0 ≤ x) :
    r ^ x ≤ Real.exp (-(kpParameter r) * x) := by
  rw [Real.rpow_def_of_pos hr_pos]
  apply Real.exp_le_exp.mpr
  have hlog_r : Real.log r ≤ 0 :=
    Real.log_nonpos hr_pos.le hr_lt1.le
  have hmul : x * Real.log r ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx hlog_r
  unfold kpParameter
  -- Goal: Real.log r * x ≤ -(-(Real.log r) / 2) * x
  -- RHS simplifies to Real.log r * x / 2 by `ring`.
  have hring : -(-(Real.log r) / 2) * x = Real.log r * x / 2 := by ring
  rw [hring]
  -- Goal: Real.log r * x ≤ Real.log r * x / 2
  -- True because `Real.log r * x = x * Real.log r ≤ 0` (hmul) and
  -- dividing a nonpositive number by 2 makes it larger.
  have hcomm : Real.log r * x = x * Real.log r := by ring
  linarith [hmul, hcomm]

/-! ## Pointwise rpow-bound ⇒ `ClusterCorrelatorBound` -/

/-- **Phase 15j.3, bridge theorem.**  If the connected Wilson
correlator satisfies a pointwise rpow-shape bound
    `|corr(p,q)| ≤ C · r^(siteLatticeDist p q)`
for every admissible `β > 0`, `F` with `|F| ≤ 1`, and `p,q`
with `siteLatticeDist ≥ 1`, then the exponential-shape
`ClusterCorrelatorBound N_c r C` follows by applying
`rpow_le_exp_kpParameter` pointwise.

This is the clean algebraic conversion between the two
natural forms the cluster bound takes in the literature:
    r^dist                       (Balaban / polymer-size form)
    exp(-(kpParameter r) · dist) (Kotecky-Preiss form). -/
theorem clusterCorrelatorBound_of_rpow_bound
    (N_c : ℕ) [NeZero N_c]
    {r : ℝ} (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (h_rpow : ∀ {d L : ℕ} [NeZero d] [NeZero L]
              (β : ℝ) (_hβ : 0 < β)
              (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
              (_hF : ∀ U, |F U| ≤ 1)
              (p q : ConcretePlaquette d L),
              (1 : ℝ) ≤ siteLatticeDist p.site q.site →
              |wilsonConnectedCorr (sunHaarProb N_c)
                  (wilsonPlaquetteEnergy N_c) β F p q| ≤
              C * r ^ (siteLatticeDist p.site q.site)) :
    ClusterCorrelatorBound N_c r C := by
  intro d L _ _ β hβ F hF p q hdist
  refine le_trans (h_rpow β hβ F hF p q hdist) ?_
  apply mul_le_mul_of_nonneg_left _ hC
  have hd_nn : (0 : ℝ) ≤ siteLatticeDist p.site q.site := by linarith
  exact rpow_le_exp_kpParameter hr_pos hr_lt1 hd_nn

/-! ## Chain to Clay theorem from rpow-shape pointwise bound -/

/-- **Phase 15j.3, final chain.**  Given
  (a) a Wilson polymer activity bound `wab`, and
  (b) a pointwise rpow-shape bound on the connected correlator
      at rate `wab.r` and prefactor `C`,
the Clay Yang-Mills mass-gap theorem statement follows. -/
theorem clay_theorem_of_rpow_bound
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C : ℝ) (hC_pos : 0 < C)
    (h_rpow : ∀ {d L : ℕ} [NeZero d] [NeZero L]
              (β : ℝ) (_hβ : 0 < β)
              (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
              (_hF : ∀ U, |F U| ≤ 1)
              (p q : ConcretePlaquette d L),
              (1 : ℝ) ≤ siteLatticeDist p.site q.site →
              |wilsonConnectedCorr (sunHaarProb N_c)
                  (wilsonPlaquetteEnergy N_c) β F p q| ≤
              C * wab.r ^ (siteLatticeDist p.site q.site)) :
    ClayYangMillsTheorem :=
  clay_theorem_from_wilson_activity wab C hC_pos
    (clusterCorrelatorBound_of_rpow_bound N_c
      wab.hr_pos wab.hr_lt1 C hC_pos.le h_rpow)

end YangMills
