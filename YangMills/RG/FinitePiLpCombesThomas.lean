/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.CoerciveCovariance

/-!
# Combes--Thomas extraction on finite dependent-index `PiLp` spaces

CMP99 regional Green operators live on different finite subtypes of active
sites.  The physical-bond Combes--Thomas API therefore cannot be applied
directly.  This file supplies the type-generic finite `PiLp` layer, with the
same source/target convention and no transport through cardinality choices.

This first layer proves the exact tilt algebra and extracts exponential kernel
decay from coercivity of every rooted tilted precision.  The finite-range
Schur estimate that produces that tilted coercivity is kept as the next layer.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- Counting-Hilbert `L2` field over an arbitrary finite index type. -/
abbrev FinitePiLpField (ι g : Type*) := WithLp 2 (ι → g)

/-- Single-coordinate probe on a finite counting-Hilbert field. -/
noncomputable def singleFinitePiLp
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (source : ι) (v : g) : FinitePiLpField ι g :=
  WithLp.toLp 2 fun target => if target = source then v else 0

@[simp] theorem singleFinitePiLp_self
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (source : ι) (v : g) :
    singleFinitePiLp source v source = v := by
  simp [singleFinitePiLp]

@[simp] theorem singleFinitePiLp_of_ne
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    {source target : ι} (v : g) (h : target ≠ source) :
    singleFinitePiLp source v target = 0 := by
  simp [singleFinitePiLp, h]

theorem singleFinitePiLp_eq_toLp_single
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (source : ι) (v : g) :
    singleFinitePiLp source v = WithLp.toLp 2 (Pi.single source v) := by
  ext target
  by_cases h : target = source
  · subst h
    simp [singleFinitePiLp]
  · simp [singleFinitePiLp, h]

@[simp] theorem norm_singleFinitePiLp
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (source : ι) (v : g) :
    ‖singleFinitePiLp source v‖ = ‖v‖ := by
  rw [singleFinitePiLp_eq_toLp_single]
  simp

/-- Entrywise kernel bound on a finite counting-Hilbert field. -/
def FinitePiLpKernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (weight : ι → ι → ℝ) : Prop :=
  ∀ source target (v : g),
    ‖C (singleFinitePiLp source v) target‖ ≤
      weight target source * ‖v‖

/-- Exact finite range in the source/target kernel convention. -/
def FinitePiLpFiniteRange
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) (R : ℕ) : Prop :=
  ∀ source target (v : g), R < dist target source →
    C (singleFinitePiLp source v) target = 0

/-- Fixed-rate exponential kernel bound on a regional finite field. -/
def FinitePiLpExponentialKernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (dist : ι → ι → ℕ) (A rate : ℝ) : Prop :=
  0 ≤ A ∧ 0 < rate ∧
    ∀ source target (v : g),
      ‖C (singleFinitePiLp source v) target‖ ≤
        A * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖

/-- Coordinatewise exponential tilt rooted at `root`. -/
noncomputable def finitePiLpTiltCLM
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root : ι) :
    FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun target =>
        Real.exp (rate * (dist root target : ℝ)) • f target
      map_add' := fun f h => by
        apply PiLp.ext
        intro target
        exact smul_add _ _ _
      map_smul' := fun c f => by
        apply PiLp.ext
        intro target
        exact smul_comm _ c _ }

@[simp] theorem finitePiLpTiltCLM_apply
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root target : ι)
    (f : FinitePiLpField ι g) :
    finitePiLpTiltCLM (g := g) dist rate root f target =
      Real.exp (rate * (dist root target : ℝ)) • f target := rfl

theorem finitePiLpTiltCLM_comp
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate₁ rate₂ : ℝ) (root : ι) :
    (finitePiLpTiltCLM (g := g) dist rate₁ root).comp
        (finitePiLpTiltCLM dist rate₂ root) =
      finitePiLpTiltCLM dist (rate₁ + rate₂) root := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro target
  simp only [ContinuousLinearMap.comp_apply, finitePiLpTiltCLM_apply,
    smul_smul, ← Real.exp_add, add_mul]

theorem finitePiLpTiltCLM_zero
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (root : ι) :
    finitePiLpTiltCLM (g := g) dist 0 root =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro target
  simp

theorem finitePiLpTiltCLM_neg_comp
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root : ι) :
    (finitePiLpTiltCLM (g := g) dist (-rate) root).comp
        (finitePiLpTiltCLM dist rate root) =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g) := by
  rw [finitePiLpTiltCLM_comp]
  simpa using finitePiLpTiltCLM_zero (g := g) dist root

theorem finitePiLpTiltCLM_comp_neg
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root : ι) :
    (finitePiLpTiltCLM (g := g) dist rate root).comp
        (finitePiLpTiltCLM dist (-rate) root) =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g) := by
  rw [finitePiLpTiltCLM_comp]
  simpa using finitePiLpTiltCLM_zero (g := g) dist root

/-- Tilted conjugate of a regional precision. -/
noncomputable def finitePiLpTiltConjCLM
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root : ι)
    (K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g :=
  (finitePiLpTiltCLM (g := g) dist rate root).comp
    (K.comp (finitePiLpTiltCLM (g := g) dist (-rate) root))

/-- A rooted probe is fixed by tilting when the distance vanishes on the
diagonal. -/
theorem finitePiLpTiltCLM_single_root
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root : ι) (v : g)
    (hself : dist root root = 0) :
    finitePiLpTiltCLM (g := g) dist rate root (singleFinitePiLp root v) =
      singleFinitePiLp root v := by
  apply PiLp.ext
  intro target
  by_cases h : target = root
  · subst h
    simp [hself]
  · simp [h]

/-- Generic CT kernel extraction once every rooted tilted precision retains
half the original coercivity. -/
theorem finitePiLpExponentialKernelBound_of_tilted_coercive
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    {rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (K C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (hKC : K.comp C = ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
    (htilt : ∀ root,
      IsCoerciveCLM (finitePiLpTiltConjCLM dist rate root K) (c / 2)) :
    FinitePiLpExponentialKernelBound C dist (2 / c) rate := by
  refine ⟨by positivity, hrate, ?_⟩
  intro source target v
  let delta : FinitePiLpField ι g := singleFinitePiLp source v
  let y : FinitePiLpField ι g :=
    finitePiLpTiltCLM (g := g) dist rate source (C delta)
  have huntilt : finitePiLpTiltCLM (g := g) dist (-rate) source y = C delta := by
    change finitePiLpTiltCLM (g := g) dist (-rate) source
      (finitePiLpTiltCLM (g := g) dist rate source (C delta)) = C delta
    exact ContinuousLinearMap.ext_iff.mp
      (finitePiLpTiltCLM_neg_comp (g := g) dist rate source) (C delta)
  have hKCdelta : K (C delta) = delta := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun T => T delta) hKC
  have htiltY : finitePiLpTiltConjCLM dist rate source K y = delta := by
    unfold finitePiLpTiltConjCLM
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      huntilt, hKCdelta]
    exact finitePiLpTiltCLM_single_root dist rate source v (hself source)
  have hynorm : ‖y‖ ≤ 2 / c * ‖v‖ := by
    have hcoerY := htilt source y
    rw [htiltY] at hcoerY
    have hinner : inner ℝ y delta ≤ ‖y‖ * ‖delta‖ :=
      real_inner_le_norm y delta
    have hdeltanorm : ‖delta‖ = ‖v‖ := norm_singleFinitePiLp source v
    by_cases hy : ‖y‖ = 0
    · rw [hy]
      positivity
    · have hypos : 0 < ‖y‖ :=
        lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
      have hchain : c / 2 * ‖y‖ ^ 2 ≤ ‖y‖ * ‖v‖ := by
        calc
          c / 2 * ‖y‖ ^ 2 ≤ inner ℝ y delta := hcoerY
          _ ≤ ‖y‖ * ‖delta‖ := hinner
          _ = ‖y‖ * ‖v‖ := by rw [hdeltanorm]
      have hcY : c * ‖y‖ ≤ 2 * ‖v‖ := by
        nlinarith [hchain, hypos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
  have hentry : C delta target =
      Real.exp (-rate * (dist source target : ℝ)) • y target := by
    rw [← huntilt]
    exact finitePiLpTiltCLM_apply dist (-rate) source target y
  calc
    ‖C (singleFinitePiLp source v) target‖ =
        Real.exp (-rate * (dist source target : ℝ)) * ‖y target‖ := by
      change ‖C delta target‖ = _
      rw [hentry, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    _ ≤ Real.exp (-rate * (dist source target : ℝ)) * ‖y‖ := by
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ target)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-rate * (dist source target : ℝ)) *
        (2 / c * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left hynorm (Real.exp_pos _).le
    _ = 2 / c * Real.exp (-(rate * (dist target source : ℝ))) * ‖v‖ := by
      rw [hsymm source target]
      ring

end

end YangMills.RG
