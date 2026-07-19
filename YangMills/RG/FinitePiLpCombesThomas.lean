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

/-- Baseline entry bound supplied by the operator norm. -/
theorem finitePiLpKernelBound_const_opNorm
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    FinitePiLpKernelBound C (fun _ _ => ‖C‖) := by
  intro source target v
  calc
    ‖C (singleFinitePiLp source v) target‖ ≤
        ‖C (singleFinitePiLp source v)‖ := PiLp.norm_apply_le _ target
    _ ≤ ‖C‖ * ‖singleFinitePiLp source v‖ :=
      ContinuousLinearMap.le_opNorm C _
    _ = ‖C‖ * ‖v‖ := by rw [norm_singleFinitePiLp]

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

/-- Sums of finite `PiLp` fields evaluate coordinatewise. -/
theorem finitePiLp_sum_apply
    {ι κ g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (s : Finset κ) (f : κ → FinitePiLpField ι g) (target : ι) :
    (∑ k ∈ s, f k) target = ∑ k ∈ s, f k target := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons k s hk ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih]
      rfl

/-- Every finite counting-Hilbert field is the sum of its coordinate probes. -/
theorem sum_singleFinitePiLp_eq
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (f : FinitePiLpField ι g) :
    ∑ source, singleFinitePiLp source (f source) = f := by
  classical
  apply PiLp.ext
  intro target
  rw [finitePiLp_sum_apply]
  rw [Finset.sum_eq_single target]
  · simp
  · intro source _ hne
    exact singleFinitePiLp_of_ne (f source) (Ne.symm hne)
  · intro h
    exact absurd (Finset.mem_univ target) h

/-- Generic finite-index block Schur estimate.  Both row and column counts
are controlled by the same symmetric distance-ball budget. -/
theorem finitePiLpOpNorm_le_of_kernelBound_finiteRange
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (dist : ι → ι → ℕ) (hsymm : ∀ p q, dist p q = dist q p)
    {R NR : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (hNR : ∀ x : ι,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {A : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    (hrange : FinitePiLpFiniteRange A dist R)
    (hentry : FinitePiLpKernelBound A (fun _ _ => beta)) :
    ‖A‖ ≤ beta * (NR : ℝ) := by
  classical
  have hbetaNR : (0 : ℝ) ≤ beta * (NR : ℝ) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound A hbetaNR
  intro f
  have hdecomp : A f = ∑ source, A (singleFinitePiLp source (f source)) := by
    rw [← map_sum, sum_singleFinitePiLp_eq]
  have hpoint : ∀ target : ι,
      ‖A f target‖ ≤ beta *
        ∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R), ‖f source‖ := by
    intro target
    have happ : A f target =
        ∑ source, A (singleFinitePiLp source (f source)) target := by
      rw [hdecomp, finitePiLp_sum_apply]
    have hsplit :
        ∑ source, A (singleFinitePiLp source (f source)) target =
          ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R),
            A (singleFinitePiLp source (f source)) target := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro source _ hne
      by_contra hle
      push_neg at hle
      exact hne (hrange source target (f source) hle)
    rw [happ, hsplit]
    calc
      ‖∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R),
          A (singleFinitePiLp source (f source)) target‖ ≤
          ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R),
            ‖A (singleFinitePiLp source (f source)) target‖ :=
        norm_sum_le _ _
      _ ≤ ∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R), beta * ‖f source‖ :=
        Finset.sum_le_sum (fun source _ => hentry source target (f source))
      _ = beta * ∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R), ‖f source‖ := by
        rw [Finset.mul_sum]
  have hsq : ‖A f‖ ^ 2 ≤ (beta * (NR : ℝ) * ‖f‖) ^ 2 := by
    have hAf : ‖A f‖ ^ 2 = ∑ target, ‖A f target‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 _ (A f)
    have hff : ‖f‖ ^ 2 = ∑ source, ‖f source‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 _ f
    have hterm : ∀ target, ‖A f target‖ ^ 2 ≤
        beta ^ 2 * (NR : ℝ) *
          ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R), ‖f source‖ ^ 2 := by
      intro target
      have h1 : ‖A f target‖ ^ 2 ≤
          (beta * ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R), ‖f source‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hpoint target) 2
      have hCS :
          (∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R), ‖f source‖) ^ 2 ≤
          ((Finset.univ.filter (fun source =>
            dist target source ≤ R)).card : ℝ) *
            ∑ source ∈ Finset.univ.filter (fun source =>
              dist target source ≤ R), ‖f source‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      have hcard :
          ((Finset.univ.filter (fun source =>
            dist target source ≤ R)).card : ℝ) ≤ (NR : ℝ) := by
        exact_mod_cast hNR target
      have hsum : 0 ≤ ∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R), ‖f source‖ ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      calc
        ‖A f target‖ ^ 2 ≤
            (beta * ∑ source ∈ Finset.univ.filter (fun source =>
              dist target source ≤ R), ‖f source‖) ^ 2 := h1
        _ = beta ^ 2 *
            (∑ source ∈ Finset.univ.filter (fun source =>
              dist target source ≤ R), ‖f source‖) ^ 2 := by ring
        _ ≤ beta ^ 2 *
            (((Finset.univ.filter (fun source =>
              dist target source ≤ R)).card : ℝ) *
              ∑ source ∈ Finset.univ.filter (fun source =>
                dist target source ≤ R), ‖f source‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (sq_nonneg beta)
        _ ≤ beta ^ 2 * ((NR : ℝ) *
              ∑ source ∈ Finset.univ.filter (fun source =>
                dist target source ≤ R), ‖f source‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcard hsum) (sq_nonneg beta)
        _ = beta ^ 2 * (NR : ℝ) *
              ∑ source ∈ Finset.univ.filter (fun source =>
                dist target source ≤ R), ‖f source‖ ^ 2 := by ring
    have hswap :
        ∑ target, ∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R), ‖f source‖ ^ 2 =
        ∑ source, ((Finset.univ.filter (fun target =>
          dist target source ≤ R)).card : ℝ) * ‖f source‖ ^ 2 := by
      calc
        ∑ target, ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R), ‖f source‖ ^ 2 =
            ∑ target, ∑ source,
              if dist target source ≤ R then ‖f source‖ ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro target _
          exact Finset.sum_filter _ _
        _ = ∑ source, ∑ target,
              if dist target source ≤ R then ‖f source‖ ^ 2 else 0 :=
          Finset.sum_comm
        _ = ∑ source, ((Finset.univ.filter (fun target =>
            dist target source ≤ R)).card : ℝ) * ‖f source‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro source _
          calc
            ∑ target, (if dist target source ≤ R then
                ‖f source‖ ^ 2 else 0) =
                ∑ target ∈ Finset.univ.filter (fun target =>
                  dist target source ≤ R), ‖f source‖ ^ 2 :=
              (Finset.sum_filter _ _).symm
            _ = ((Finset.univ.filter (fun target =>
                dist target source ≤ R)).card : ℝ) * ‖f source‖ ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hcolumn : ∀ source : ι,
        ((Finset.univ.filter (fun target =>
          dist target source ≤ R)).card : ℝ) ≤ (NR : ℝ) := by
      intro source
      have heq : Finset.univ.filter (fun target => dist target source ≤ R) =
          Finset.univ.filter (fun target => dist source target ≤ R) := by
        apply Finset.filter_congr
        intro target _
        rw [hsymm target source]
      rw [heq]
      exact_mod_cast hNR source
    have hdouble :
        ∑ target, ∑ source ∈ Finset.univ.filter (fun source =>
          dist target source ≤ R), ‖f source‖ ^ 2 ≤
        (NR : ℝ) * ∑ source, ‖f source‖ ^ 2 := by
      rw [hswap, Finset.mul_sum]
      exact Finset.sum_le_sum (fun source _ =>
        mul_le_mul_of_nonneg_right (hcolumn source) (sq_nonneg _))
    calc
      ‖A f‖ ^ 2 = ∑ target, ‖A f target‖ ^ 2 := hAf
      _ ≤ ∑ target, beta ^ 2 * (NR : ℝ) *
          ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R), ‖f source‖ ^ 2 :=
        Finset.sum_le_sum (fun target _ => hterm target)
      _ = beta ^ 2 * (NR : ℝ) *
          ∑ target, ∑ source ∈ Finset.univ.filter (fun source =>
            dist target source ≤ R), ‖f source‖ ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ beta ^ 2 * (NR : ℝ) *
          ((NR : ℝ) * ∑ source, ‖f source‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdouble (by positivity)
      _ = (beta * (NR : ℝ) * ‖f‖) ^ 2 := by
        rw [← hff]
        ring
  have hleft : 0 ≤ ‖A f‖ := norm_nonneg _
  have hright : 0 ≤ beta * (NR : ℝ) * ‖f‖ := by positivity
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Kernel entry of a tilted conjugate. -/
theorem finitePiLpTiltConjCLM_single_apply
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root source target : ι) (v : g)
    (K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    finitePiLpTiltConjCLM dist rate root K
        (singleFinitePiLp source v) target =
      Real.exp (rate * ((dist root target : ℝ) -
        (dist root source : ℝ))) •
        K (singleFinitePiLp source v) target := by
  have hsingle : finitePiLpTiltCLM (g := g) dist (-rate) root
      (singleFinitePiLp source v) =
      Real.exp (-rate * (dist root source : ℝ)) •
        singleFinitePiLp source v := by
    apply PiLp.ext
    intro q
    by_cases hq : q = source
    · subst hq
      simp [PiLp.smul_apply]
    · simp [PiLp.smul_apply, hq]
  unfold finitePiLpTiltConjCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hsingle, map_smul, map_smul]
  calc
    (Real.exp (-rate * (dist root source : ℝ)) •
        finitePiLpTiltCLM (g := g) dist rate root
          (K (singleFinitePiLp source v))) target =
      Real.exp (-rate * (dist root source : ℝ)) •
        (Real.exp (rate * (dist root target : ℝ)) •
          K (singleFinitePiLp source v) target) := by rfl
    _ = Real.exp (rate * ((dist root target : ℝ) -
          (dist root source : ℝ))) •
        K (singleFinitePiLp source v) target := by
      rw [smul_smul, ← Real.exp_add]
      congr 2
      ring

/-- Triangle control for the rooted distance difference. -/
theorem abs_finiteDist_sub_le_of_symm_triangle
    {ι : Type*} (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (root source target : ι) :
    |(dist root target : ℝ) - (dist root source : ℝ)| ≤
      (dist target source : ℝ) := by
  rw [abs_sub_le_iff]
  constructor
  · have h : dist root target ≤ dist root source + dist target source := by
      calc
        dist root target ≤ dist root source + dist source target :=
          htri root source target
        _ = dist root source + dist target source := by
          rw [hsymm source target]
    have hreal : (dist root target : ℝ) ≤
        (dist root source : ℝ) + (dist target source : ℝ) := by
      exact_mod_cast h
    linarith
  · have h : dist root source ≤ dist root target + dist target source :=
      htri root target source
    have hreal : (dist root source : ℝ) ≤
        (dist root target : ℝ) + (dist target source : ℝ) := by
      exact_mod_cast h
    linarith

/-- Two-sided exponential perturbation estimate. -/
theorem abs_exp_sub_one_le_of_abs_le_finitePiLp {t s : ℝ}
    (h : |t| ≤ s) :
    |Real.exp t - 1| ≤ Real.exp s - 1 := by
  rw [abs_le] at h
  rw [abs_le]
  constructor
  · have hlow : Real.exp (-s) ≤ Real.exp t :=
      Real.exp_le_exp.mpr (by linarith)
    have htwo : (2 : ℝ) ≤ Real.exp s + Real.exp (-s) := by
      have hmul : Real.exp s * Real.exp (-s) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [sq_nonneg (Real.exp s - 1), Real.exp_pos s]
    linarith
  · have hupp : Real.exp t ≤ Real.exp s :=
      Real.exp_le_exp.mpr (by linarith)
    linarith

/-- Tilt perturbation preserves the original finite range. -/
theorem finitePiLpTiltConj_sub_finiteRange
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) (rate : ℝ) (root : ι) {R : ℕ}
    {K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    (hrange : FinitePiLpFiniteRange K dist R) :
    FinitePiLpFiniteRange
      (finitePiLpTiltConjCLM dist rate root K - K) dist R := by
  intro source target v hfar
  have hK := hrange source target v hfar
  have hsub : (finitePiLpTiltConjCLM dist rate root K - K)
      (singleFinitePiLp source v) target =
      finitePiLpTiltConjCLM dist rate root K
        (singleFinitePiLp source v) target -
      K (singleFinitePiLp source v) target := rfl
  rw [hsub, finitePiLpTiltConjCLM_single_apply, hK, smul_zero, sub_zero]

/-- Entrywise bound for the tilt perturbation. -/
theorem finitePiLpTiltConj_sub_kernelBound
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {rate : ℝ} (hrate : 0 ≤ rate) (root : ι)
    {R : ℕ} {Mbound : ℝ} (hM : 0 ≤ Mbound)
    {K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    (hrange : FinitePiLpFiniteRange K dist R)
    (hbound : FinitePiLpKernelBound K (fun _ _ => Mbound)) :
    FinitePiLpKernelBound
      (finitePiLpTiltConjCLM dist rate root K - K)
      (fun _ _ => Mbound * (Real.exp (rate * (R : ℝ)) - 1)) := by
  intro source target v
  have happ : (finitePiLpTiltConjCLM dist rate root K - K)
      (singleFinitePiLp source v) target =
      (Real.exp (rate * ((dist root target : ℝ) -
        (dist root source : ℝ))) - 1) •
        K (singleFinitePiLp source v) target := by
    have hsub : (finitePiLpTiltConjCLM dist rate root K - K)
        (singleFinitePiLp source v) target =
        finitePiLpTiltConjCLM dist rate root K
          (singleFinitePiLp source v) target -
        K (singleFinitePiLp source v) target := rfl
    rw [hsub, finitePiLpTiltConjCLM_single_apply, sub_smul, one_smul]
  by_cases hfar : R < dist target source
  · rw [happ, hrange source target v hfar, smul_zero]
    have : 0 ≤ Mbound * (Real.exp (rate * (R : ℝ)) - 1) * ‖v‖ := by
      have hexp : 1 ≤ Real.exp (rate * (R : ℝ)) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by positivity)
      exact mul_nonneg
        (mul_nonneg hM (sub_nonneg.mpr hexp)) (norm_nonneg v)
    simpa using this
  · push_neg at hfar
    rw [happ, norm_smul, Real.norm_eq_abs]
    have habs := abs_finiteDist_sub_le_of_symm_triangle
      dist hsymm htri root source target
    have hdist : (dist target source : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hfar
    have htilt :
        |rate * ((dist root target : ℝ) - (dist root source : ℝ))| ≤
          rate * (R : ℝ) := by
      rw [abs_mul, abs_of_nonneg hrate]
      exact mul_le_mul_of_nonneg_left (le_trans habs hdist) hrate
    have hfac := abs_exp_sub_one_le_of_abs_le_finitePiLp htilt
    have hK := hbound source target v
    have hexp : 1 ≤ Real.exp (rate * (R : ℝ)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    calc
      |Real.exp (rate * ((dist root target : ℝ) -
          (dist root source : ℝ))) - 1| *
          ‖K (singleFinitePiLp source v) target‖ ≤
        (Real.exp (rate * (R : ℝ)) - 1) * (Mbound * ‖v‖) := by
          exact mul_le_mul hfac hK (norm_nonneg _)
            (sub_nonneg.mpr hexp)
      _ = Mbound * (Real.exp (rate * (R : ℝ)) - 1) * ‖v‖ := by ring

/-- Operator-norm budget for the rooted tilt perturbation. -/
theorem norm_finitePiLpTiltConj_sub_le
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {rate : ℝ} (hrate : 0 ≤ rate) (root : ι)
    {R NR : ℕ} {Mbound : ℝ} (hM : 0 ≤ Mbound)
    (hNR : ∀ x : ι,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    (hrange : FinitePiLpFiniteRange K dist R)
    (hbound : FinitePiLpKernelBound K (fun _ _ => Mbound)) :
    ‖finitePiLpTiltConjCLM dist rate root K - K‖ ≤
      Mbound * (Real.exp (rate * (R : ℝ)) - 1) * (NR : ℝ) := by
  have hfactor : 0 ≤ Mbound * (Real.exp (rate * (R : ℝ)) - 1) := by
    have hexp : 1 ≤ Real.exp (rate * (R : ℝ)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    exact mul_nonneg hM (sub_nonneg.mpr hexp)
  exact finitePiLpOpNorm_le_of_kernelBound_finiteRange dist hsymm hfactor hNR
    (finitePiLpTiltConj_sub_finiteRange dist rate root hrange)
    (finitePiLpTiltConj_sub_kernelBound
      dist hsymm htri hrate root hM hrange hbound)

/-- Coercivity survives the generic finite-index tilt with the explicit Schur
budget. -/
theorem isCoerciveCLM_finitePiLpTiltConj
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    {rate : ℝ} (hrate : 0 ≤ rate) (root : ι)
    {R NR : ℕ} {Mbound c : ℝ} (hM : 0 ≤ Mbound)
    (hNR : ∀ x : ι,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    {K : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g}
    (hrange : FinitePiLpFiniteRange K dist R)
    (hbound : FinitePiLpKernelBound K (fun _ _ => Mbound))
    (hcoer : IsCoerciveCLM K c) :
    IsCoerciveCLM (finitePiLpTiltConjCLM dist rate root K)
      (c - Mbound * (Real.exp (rate * (R : ℝ)) - 1) * (NR : ℝ)) := by
  have hsplit : finitePiLpTiltConjCLM dist rate root K =
      K + (finitePiLpTiltConjCLM dist rate root K - K) := by abel
  rw [hsplit]
  exact isCoercive_add_of_opNorm_le K _ hcoer
    (norm_finitePiLpTiltConj_sub_le
      dist hsymm htri hrate root hM hNR hrange hbound)

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

/-- Generic finite-index Combes--Thomas theorem.  A finite-range coercive
precision with a uniform entry and ball-cardinality budget has an exponentially
localized right inverse. -/
theorem finitePiLpExponentialKernelBound_of_coercive
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {rate c Mbound : ℝ} {R NR : ℕ}
    (hrate : 0 < rate) (hc : 0 < c) (hM : 0 ≤ Mbound)
    (hNR : ∀ x : ι,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (K C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (hrange : FinitePiLpFiniteRange K dist R)
    (hbound : FinitePiLpKernelBound K (fun _ _ => Mbound))
    (hcoer : IsCoerciveCLM K c)
    (hKC : K.comp C = ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
    (hbudget : Mbound * (Real.exp (rate * (R : ℝ)) - 1) *
      (NR : ℝ) ≤ c / 2) :
    FinitePiLpExponentialKernelBound C dist (2 / c) rate := by
  apply finitePiLpExponentialKernelBound_of_tilted_coercive
    dist hsymm hself hrate hc K C hKC
  intro root
  have htilt := isCoerciveCLM_finitePiLpTiltConj
    dist hsymm htri hrate.le root hM hNR hrange hbound hcoer
  intro x
  calc
    c / 2 * ‖x‖ ^ 2 ≤
        (c - Mbound * (Real.exp (rate * (R : ℝ)) - 1) *
          (NR : ℝ)) * ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖x‖)
      linarith
    _ ≤ inner ℝ x (finitePiLpTiltConjCLM dist rate root K x) := htilt x

end

end YangMills.RG
