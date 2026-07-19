/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedMassRange
import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
# Combes--Thomas decay for the generated CMP99 Green operator

This file derives finite range and exponential decay from the literal
generated precision.  The multiscale `Q'†Q'` range is supplied by the exact
terminal-block theorem, while the Dirichlet Laplacian range follows from its
nearest-neighbour stencil.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The arbitrary-region source covariant Laplacian has exact one-link
range in the underlying periodic site metric. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ) :
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site Omega) (g := SUNLieCoord Nc)
      (cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing)
      (fun x y => finBoxDist x.1 y.1) 1 := by
  intro source target v hfar
  change 1 < finBoxDist target.1 source.1 at hfar
  let phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
    singleFinitePiLp source v
  let ext : PhysicalGaugeZeroCochain d N Nc := extendZeroZeroCLM Omega phi
  have hext_zero (y : FinBox d N) (hy : y ≠ source.1) : ext y = 0 := by
    by_cases hyOmega : y ∈ Omega.sites
    · rw [show ext y = phi ⟨y, hyOmega⟩ by
          exact extendZeroZeroCLM_apply_of_mem Omega phi y hyOmega]
      apply singleFinitePiLp_of_ne
      intro hsub
      exact hy (congrArg Subtype.val hsub)
    · exact extendZeroZeroCLM_apply_of_not_mem Omega phi y hyOmega
  have htarget : target.1 ≠ source.1 := by
    intro h
    rw [h, finBoxDist_self] at hfar
    omega
  have hforward : ∀ i : Fin d, target.1.shift i ≠ source.1 := by
    intro i h
    have hnear : finBoxDist target.1 source.1 ≤ 1 := by
      rw [← h]
      exact finBoxDist_shift_le target.1 i
    omega
  have hback : ∀ i : Fin d, target.1.shiftBack i ≠ source.1 := by
    intro i h
    have hnear : finBoxDist target.1 source.1 ≤ 1 := by
      rw [← h]
      exact finBoxDist_shiftBack_le target.1 i
    omega
  have hambient := cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_zero
    rho U spacing ext target.1 (hext_zero target.1 htarget)
      (fun i => hext_zero _ (hforward i))
      (fun i => hext_zero _ (hback i))
  rw [cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression]
  exact hambient

/-- The complete literal generated precision has range one terminal block.
The chosen radius `M^(depth+1)` simultaneously dominates the exact mass
radius `M^(depth+1)-1` and the one-link Laplacian radius. -/
theorem cmp99SourceGeneratedPhysicalPrecision_finiteRange
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpFiniteRange
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
        background budget fineSmall)
      (fun x y => finBoxDist x.1 y.1) (M ^ (depth + 1)) := by
  intro source target v hfar
  change M ^ (depth + 1) < finBoxDist target.1 source.1 at hfar
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  have hpowPos : 0 < M ^ (depth + 1) := pow_pos (NeZero.pos M) _
  have hlapFar : 1 <
      (fun x y : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        finBoxDist x.1 y.1) target source := by
    change 1 < finBoxDist target.1 source.1
    omega
  have hlap := cmp99ActiveRegionSourceCovariantLaplacian_finiteRange_one
    (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing source target v hlapFar
  have hmassFar : M ^ (depth + 1) - 1 <
      (fun x y : ActiveGaugeRegion.Site
          (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)) =>
        finBoxDist x.1 y.1) target source := by
    change M ^ (depth + 1) - 1 < finBoxDist target.1 source.1
    omega
  have hmass := cmp99SourceIteratedLift_QprimeMass_finiteRange
    Omega (depth + 1) hd hM (matrixSUNAdjointModel Nc) spacing epsilon
      background budget.toRadiusChain fineSmall source target v hmassFar
  rw [cmp99SourceGeneratedPhysicalPrecision, cmp99SourceGaugePrecision,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  change cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (matrixSUNAdjointModel Nc) background spacing
          (singleFinitePiLp source v) target +
      cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon •
        ((T.Qprime.adjoint.comp T.Qprime)
          (singleFinitePiLp source v)) target = 0
  rw [hlap, hmass, smul_zero, add_zero]

/-- Balls in an arbitrary active-region subtype inject into the ambient
periodic `FinBox` ball, hence retain a volume-independent cardinality. -/
theorem activeGaugeRegion_finBoxDist_ball_card_le
    (Omega : ActiveGaugeRegion d N) (x : ActiveGaugeRegion.Site Omega)
    (R : ℕ) :
    (Finset.univ.filter (fun y : ActiveGaugeRegion.Site Omega =>
      finBoxDist x.1 y.1 ≤ R)).card ≤ (2 * R + 1) ^ d := by
  classical
  let regional := Finset.univ.filter
    (fun y : ActiveGaugeRegion.Site Omega => finBoxDist x.1 y.1 ≤ R)
  let ambient := Finset.univ.filter
    (fun y : FinBox d N => finBoxDist x.1 y ≤ R)
  have hmaps : ∀ y ∈ regional, y.1 ∈ ambient := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hy.2⟩
  have hinj : Set.InjOn
      (fun y : ActiveGaugeRegion.Site Omega => y.1) (regional : Set _) := by
    intro y _ z _ h
    exact Subtype.ext h
  calc
    (Finset.univ.filter (fun y : ActiveGaugeRegion.Site Omega =>
      finBoxDist x.1 y.1 ≤ R)).card = regional.card := rfl
    _ ≤ ambient.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (2 * R + 1) ^ d :=
      finBoxDist_ball_card_le_two_mul_add_one_pow x.1 R

/-- An operator-norm upper bound gives the corresponding constant entrywise
kernel bound without inspecting the definition of the operator. -/
theorem finitePiLpKernelBound_of_opNorm_le
    {iota g : Type*} [Fintype iota] [DecidableEq iota]
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (A : FinitePiLpField iota g →L[ℝ] FinitePiLpField iota g)
    {B : ℝ} (hA : ‖A‖ ≤ B) :
    FinitePiLpKernelBound (ι := iota) (g := g) A (fun _ _ => B) := by
  intro source target v
  calc
    ‖A (singleFinitePiLp source v) target‖ ≤ ‖A‖ * ‖v‖ :=
      finitePiLpKernelBound_const_opNorm A source target v
    _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg v)

/-- Uniform entrywise bound for the literal generated precision, derived
from its source-generated operator-norm estimate. -/
theorem cmp99SourceGeneratedPhysicalPrecision_kernelBound
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    FinitePiLpKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
        background budget fineSmall)
      (fun _ _ => cmp99SourceGeneratedPhysicalPrecisionUpperBound
        d M (depth + 1) spacing epsilon) := by
  apply finitePiLpKernelBound_of_opNorm_le
  exact norm_cmp99SourceGeneratedPhysicalPrecision_le
    hd hM Omega depth hspacing background budget fineSmall

set_option maxHeartbeats 1200000 in
/-- Source-generated Combes--Thomas estimate at any positive rate satisfying
the displayed physical tilt budget.  Finite range, ball growth, coercivity,
the kernel budget, and the right inverse are all discharged internally. -/
theorem cmp99SourceGeneratedPhysicalGreen_exponentialKernelBound
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon rate : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1)
    (hrate : 0 < rate)
    (hbudget :
      cmp99SourceGeneratedPhysicalPrecisionUpperBound
          d M (depth + 1) spacing epsilon *
        (Real.exp (rate * (M ^ (depth + 1) : ℕ)) - 1) *
        (((2 * M ^ (depth + 1) + 1) ^ d : ℕ) : ℝ) ≤
      cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon / 2) :
    FinitePiLpExponentialKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
        background budget fineSmall hsmall)
      (fun x y => finBoxDist x.1 y.1)
      (2 / cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon)
      rate := by
  let Omega' := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let K := cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
    spacing epsilon background budget fineSmall
  let C := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  change FinitePiLpExponentialKernelBound
    (ι := ActiveGaugeRegion.Site Omega') (g := SUNLieCoord Nc)
    C (fun x y => finBoxDist x.1 y.1)
      (2 / cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon)
      rate
  apply finitePiLpExponentialKernelBound_of_coercive
    (fun x y : ActiveGaugeRegion.Site Omega' => finBoxDist x.1 y.1)
    (fun p q => finBoxDist_comm p.1 q.1)
    (fun p q s => finBoxDist_triangle p.1 q.1 s.1)
    (fun p => finBoxDist_self p.1)
    hrate
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall)
    (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      d M (depth + 1) hspacing).le
    (R := M ^ (depth + 1))
    (NR := (2 * M ^ (depth + 1) + 1) ^ d)
    (fun x => activeGaugeRegion_finBoxDist_ball_card_le Omega' x _)
    K C
  · exact cmp99SourceGeneratedPhysicalPrecision_finiteRange
      hd hM Omega depth spacing epsilon background budget fineSmall
  · exact cmp99SourceGeneratedPhysicalPrecision_kernelBound
      hd hM Omega depth hspacing background budget fineSmall
  · exact isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
      hd hM Omega depth hspacing background budget fineSmall hsmall
  · exact cmp99SourceGeneratedPhysicalPrecision_comp_green
      hd hM Omega depth hspacing background budget fineSmall hsmall
  · exact hbudget

/-- Canonical positive decay rate for the generated depth-`depth+1` Green
operator, obtained by spending exactly half of its generated coercivity. -/
noncomputable def cmp99SourceGeneratedCombesThomasRate
    (d M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  let R : ℝ := (M ^ (depth + 1) : ℕ)
  let NR : ℝ := (((2 * M ^ (depth + 1) + 1) ^ d : ℕ) : ℝ)
  let B := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    d M (depth + 1) spacing epsilon
  let c := cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon
  Real.log (1 + c / (2 * B * NR)) / R

theorem cmp99SourceGeneratedCombesThomasRate_pos
    (d M depth : ℕ) [NeZero d] [NeZero M]
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    0 < cmp99SourceGeneratedCombesThomasRate
      d M depth spacing epsilon := by
  let R : ℝ := (M ^ (depth + 1) : ℕ)
  let NR : ℝ := (((2 * M ^ (depth + 1) + 1) ^ d : ℕ) : ℝ)
  let B := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    d M (depth + 1) spacing epsilon
  let c := cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast pow_pos (NeZero.pos M) (depth + 1)
  have hNR : 0 < NR := by dsimp [NR]; positivity
  have hB : 0 < B :=
    cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      d M (depth + 1) hspacing
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall
  unfold cmp99SourceGeneratedCombesThomasRate
  dsimp only
  apply div_pos
  · apply Real.log_pos
    have : 0 < c / (2 * B * NR) := by positivity
    linarith
  · exact hR

theorem cmp99SourceGeneratedCombesThomasRate_budget
    (d M depth : ℕ) [NeZero d] [NeZero M]
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    cmp99SourceGeneratedPhysicalPrecisionUpperBound
          d M (depth + 1) spacing epsilon *
        (Real.exp
          (cmp99SourceGeneratedCombesThomasRate d M depth spacing epsilon *
            (M ^ (depth + 1) : ℕ)) - 1) *
        (((2 * M ^ (depth + 1) + 1) ^ d : ℕ) : ℝ) ≤
      cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon / 2 := by
  let R : ℝ := (M ^ (depth + 1) : ℕ)
  let NR : ℝ := (((2 * M ^ (depth + 1) + 1) ^ d : ℕ) : ℝ)
  let B := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    d M (depth + 1) spacing epsilon
  let c := cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast pow_pos (NeZero.pos M) (depth + 1)
  have hNR : 0 < NR := by dsimp [NR]; positivity
  have hB : 0 < B :=
    cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      d M (depth + 1) hspacing
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall
  have harg : 0 < 1 + c / (2 * B * NR) := by positivity
  have hrateMul :
      cmp99SourceGeneratedCombesThomasRate d M depth spacing epsilon * R =
        Real.log (1 + c / (2 * B * NR)) := by
    unfold cmp99SourceGeneratedCombesThomasRate
    change (Real.log (1 + c / (2 * B * NR)) / R) * R = _
    exact div_mul_cancel₀ _ (ne_of_gt hR)
  have hexp :
      Real.exp
        (cmp99SourceGeneratedCombesThomasRate d M depth spacing epsilon * R) =
          1 + c / (2 * B * NR) := by
    rw [hrateMul, Real.exp_log harg]
  change B *
      (Real.exp
        (cmp99SourceGeneratedCombesThomasRate d M depth spacing epsilon * R) - 1) *
        NR ≤ c / 2
  rw [hexp]
  have hBN : 2 * B * NR ≠ 0 := by positivity
  field_simp
  linarith

/-- Unconditional generated physical Green decay at its canonical positive
rate.  No finite-range, ball, kernel, coercivity, inverse, or tilt-budget
premise remains in the interface. -/
theorem cmp99SourceGeneratedPhysicalGreen_canonicalExponentialKernelBound
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpExponentialKernelBound
      (ι := ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
      (g := SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
        background budget fineSmall hsmall)
      (fun x y => finBoxDist x.1 y.1)
      (2 / cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate d M depth spacing epsilon) :=
  cmp99SourceGeneratedPhysicalGreen_exponentialKernelBound
    hd hM Omega depth hspacing background budget fineSmall hsmall
      (cmp99SourceGeneratedCombesThomasRate_pos
        d M depth hspacing hsmall)
      (cmp99SourceGeneratedCombesThomasRate_budget
        d M depth hspacing hsmall)

end

end YangMills.RG
