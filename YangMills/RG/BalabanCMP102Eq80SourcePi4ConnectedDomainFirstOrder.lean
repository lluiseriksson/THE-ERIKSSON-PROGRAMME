/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainNormalization
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# First-order normalization of the equation-(80) domain coefficients

The domain coefficients differentiate the equation-(80) functional first in
the propagator and later in the physical field.  This file proves that the
two operations can be interchanged without adding a mixed-derivative premise.

The proof views the functional as a smooth map on the product of propagator
and physical-field spaces.  Its partial propagator jet is represented by the
joint iterated derivative along propagator-only directions.  Symmetry of the
joint derivative rotates the physical-field direction to the final slot,
where the known zero first derivative of the literal equation-(80)
functional makes the whole jet vanish.

The result is propagated through both finite Faà di Bruno sums.  Commutation
with the recursive interval integrals of the final FTC activity is a separate
measure-theoretic layer and is intentionally not asserted here.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

section MixedJets

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `n`-th propagator jet of a joint functional, evaluated along
propagator-only directions while retaining the physical field as parameter. -/
noncomputable def cmp102PartialPropagatorJet
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : ℝ :=
  iteratedFDeriv ℝ n F (h, x) (fun i => (v i, 0))

/-- A partial derivative computed in the propagator slice is exactly the
joint derivative along propagator-only directions. -/
theorem iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    iteratedFDeriv ℝ n (fun y : H => F (y, x)) h v =
      cmp102PartialPropagatorJet F n h v x := by
  let eH : H →L[ℝ] H × E := ContinuousLinearMap.inl ℝ H E
  let Fshift : H × E → ℝ := fun p => F (p + (0, x))
  have hshift : ContDiff ℝ ⊤ Fshift := by
    exact hF.comp (contDiff_id.add contDiff_const)
  have hcomp :=
    eH.iteratedFDeriv_comp_right hshift h (i := n) (by simp)
  have htrans :=
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F)
      n (0, x) (eH h)
  have heval := congrArg (fun T => T v) hcomp
  have htransEval :=
    congrArg (fun T => T (fun i => eH (v i))) htrans
  unfold cmp102PartialPropagatorJet
  simpa [Fshift, eH, Function.comp_def] using heval.trans htransEval

/-- The derivative of the partial jet before using symmetry. -/
theorem fderiv_cmp102PartialPropagatorJet
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) :
    fderiv ℝ (cmp102PartialPropagatorJet F n h v) 0 =
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).comp
        ((fderiv ℝ (iteratedFDeriv ℝ n F) (h, 0)).comp
          ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))) := by
  unfold cmp102PartialPropagatorJet
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : HasFDerivAt (fun x : E => (h, x))
      ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) 0 :=
    (hasFDerivAt_const (x := (0 : E)) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E)))
  have hcomp :=
    hjet.differentiableAt.hasFDerivAt.comp (0 : E) hpath
  have heval :=
    (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ
      (fun i => (v i, 0))).hasFDerivAt.comp (0 : E) hcomp
  simpa using heval.fderiv

/-- If the physical-field derivative of the joint functional vanishes on
the zero-field slice, then every propagator jet has zero physical-field
derivative there.  No mixed-derivative equality is assumed. -/
theorem hasFDerivAt_cmp102PartialPropagatorJet_zero
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hpartial : ∀ h : H, ∀ a : E,
      fderiv ℝ F (h, 0) (0, a) = 0)
    (n : ℕ) (h : H) (v : Fin n → H) :
    HasFDerivAt (cmp102PartialPropagatorJet F n h v)
      (0 : E →L[ℝ] ℝ) 0 := by
  have hdiff : Differentiable ℝ
      (cmp102PartialPropagatorJet F n h v) := by
    unfold cmp102PartialPropagatorJet
    have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
      hF.differentiable_iteratedFDeriv (by simp)
    have hpath : Differentiable ℝ (fun x : E => (h, x)) := by
      fun_prop
    exact
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).differentiable.comp
          (hjet.comp hpath)
  have hzero :
      fderiv ℝ (cmp102PartialPropagatorJet F n h v) 0 = 0 := by
    rw [fderiv_cmp102PartialPropagatorJet F hF n h v]
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
      ContinuousMultilinearMap.apply_apply, fderiv_iteratedFDeriv,
      Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply]
    change
      iteratedFDeriv ℝ (n + 1) F (h, 0)
        (Fin.cons (0, a) (fun i => (v i, 0))) = 0
    have hperm :=
      hF.contDiffAt.iteratedFDeriv_comp_perm
        (x := (h, (0 : E)))
        (Fin.cons (0, a) (fun i => (v i, 0)))
        (finRotate (n + 1))
    have hrotate :
        (Fin.cons (0, a) (fun i => (v i, 0))) ∘
            (finRotate (n + 1)) =
          Fin.snoc (fun i => (v i, 0)) (0, a) := by
      funext i
      simpa [Function.comp_def] using
        congrFun
          (Fin.snoc_eq_cons_rotate (fun i => (v i, 0)) (0, a)).symm i
    rw [hrotate] at hperm
    rw [← hperm]
    rw [iteratedFDeriv_succ_apply_right]
    simp only [Fin.init_snoc, Fin.snoc_last]
    let eH : H →L[ℝ] H × E := ContinuousLinearMap.inl ℝ H E
    have hc : ContDiff ℝ ⊤ (fderiv ℝ F) :=
      hF.fderiv_right (by simp)
    have hrestrict :=
      eH.iteratedFDeriv_comp_right hc h (i := n) (by simp)
    have happly :=
      iteratedFDeriv_clm_apply_const_apply
        (c := fun y : H => fderiv ℝ F (eH y))
        (hc := hc.comp eH.contDiff) (i := n) (by simp)
        (x := h) (u := (0, a)) (m := v)
    have hreval :=
      congrArg (fun T => T v (0, a)) hrestrict
    have hreval' :
        ((iteratedFDeriv ℝ n
            (fun y : H => fderiv ℝ F (eH y)) h) v) (0, a) =
          ((iteratedFDeriv ℝ n (fderiv ℝ F) (h, 0))
            (fun i => (v i, 0))) (0, a) := by
      simpa [eH, Function.comp_def] using hreval
    rw [← hreval']
    rw [← happly]
    have hidenticallyZero :
        (fun y : H => fderiv ℝ F (eH y) (0, a)) =
          (fun _ : H => 0) := by
      funext y
      exact hpartial y a
    rw [hidenticallyZero]
    simp
  have hder :
      HasFDerivAt (cmp102PartialPropagatorJet F n h v)
        (fderiv ℝ (cmp102PartialPropagatorJet F n h v) 0) 0 :=
    hdiff.differentiableAt.hasFDerivAt
  simpa [hzero] using hder

end MixedJets

/-- The literal equation-(80) functional is jointly smooth in its
propagator and physical-field variables. -/
theorem contDiff_cmp102Eq80JointPotential
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2) := by
  unfold cmp102Eq80GlobalPotential
  have hHD : ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        p.1 (D p.2)) :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  have hHD₃ : ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        p.1 (D₃ p.2)) :=
    contDiff_fst.clm_apply (hD₃.comp contDiff_snd)
  have hΔHD : ContDiff ℝ ⊤
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        Δπ (p.1 (D p.2))) :=
    Δπ.contDiff.comp hHD
  exact
    (((hHD₃.inner ℝ contDiff_const).neg.add
      ((contDiff_snd.inner ℝ hΔHD).neg)).add
      (contDiff_const.mul (hHD.inner ℝ hΔHD))).add
      (hV₀.comp (contDiff_snd.sub hHD))

/-- The vertical derivative of the joint equation-(80) functional vanishes
on the entire zero-field propagator slice. -/
theorem fderiv_cmp102Eq80JointPotential_vertical_zero
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0)
    (H : PhysicalEndomorphism M Q Nc)
    (a : PhysicalField M Q Nc) :
    fderiv ℝ
      (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
        cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
      (H, 0) (0, a) = 0 := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_cmp102Eq80JointPotential D D₃ V₀ Δπ J hD hD₃ hV₀
  have hpath : HasFDerivAt (fun x : PhysicalField M Q Nc => (H, x))
      ((0 : PhysicalField M Q Nc →L[ℝ] PhysicalEndomorphism M Q Nc).prod
        (1 : PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc)) 0 :=
    (hasFDerivAt_const (x := (0 : PhysicalField M Q Nc)) H).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : PhysicalField M Q Nc)))
  have hcomp :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
      (0 : PhysicalField M Q Nc) hpath
  have hD' :
      HasFDerivAt D (fderiv ℝ D 0) 0 :=
    (hD.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hslice :=
    cmp102Eq80GlobalPotential_hasFDerivAt_zero
      D D₃ V₀ H Δπ J (fderiv ℝ D 0)
      hD0 hD₃0 hD' hD₃' hV₀'
  have heq := hcomp.unique hslice
  have heval := congrArg (fun T => T a) heq
  simpa [F] using heval

/-- Each physical domain-choice propagator jet has zero physical-field
derivative at the origin. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (fun A =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition choice)
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0 := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let H₀ :=
    cmp116FiniteMultiaffineInterpolation
      (fun u =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK u ∅)
      vertexBase L sigma
  let directions :=
    fun block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK sigma
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block)
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_cmp102Eq80JointPotential D D₃ V₀ Δπ J hD hD₃ hV₀
  have hpartial :
      ∀ H : PhysicalEndomorphism M Q Nc,
        ∀ a : PhysicalField M Q Nc,
          fderiv ℝ F (H, 0) (0, a) = 0 := by
    intro H a
    exact
      fderiv_cmp102Eq80JointPotential_vertical_zero
        D D₃ V₀ Δπ J hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀' H a
  have hjet :=
    hasFDerivAt_cmp102PartialPropagatorJet_zero
      F hF hpartial partition.length H₀ directions
  have hfun :
      (fun A =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition choice) =
        cmp102PartialPropagatorJet
          F partition.length H₀ directions := by
    funext A
    have hs :=
      iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
        F hF partition.length H₀ directions A
    simpa [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt,
      cmp102Eq80PotentialAsFunctionOfPropagator, ftaylorSeries,
      F, H₀, directions] using hs
  rw [hfun]
  exact hjet

/-- The coefficient of one domain label inside an ordered partition has zero
physical-field derivative at the origin. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_hasFDerivAt_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (W : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (fun A =>
        cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition W)
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0 := by
  unfold cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
  convert HasFDerivAt.fun_sum (u :=
      (Finset.univ :
        Finset (CMP102Eq80FaaDiBrunoDomainChoice
          (Q := Q) partition)).filter
        (fun choice =>
          cmp102Eq80SourcePi4AnchoredDomainUnion anchor
            Finset.univ choice = W))
      (A := fun choice A =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition choice)
      (A' := fun _ => (0 : PhysicalField M Q Nc →L[ℝ] ℝ))
      (x := (0 : PhysicalField M Q Nc))
      (fun choice _hchoice =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt_zero_field
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          vertexBase sigma L coordinates partition choice
          hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀') using 1
  all_goals simp

/-- The complete coefficient of every physical domain label has zero
physical-field derivative at the origin, after summing all ordered
partitions. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_hasFDerivAt_zero_field
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0)
    (hD₃' : HasFDerivAt D₃
      (0 : PhysicalEndomorphism M Q Nc) 0)
    (hV₀' : HasFDerivAt V₀
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0) :
    HasFDerivAt
      (fun A =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates W)
      (0 : PhysicalField M Q Nc →L[ℝ] ℝ) 0 := by
  unfold cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
  convert HasFDerivAt.fun_sum
      (u := (Finset.univ : Finset (OrderedFinpartition n)))
      (A := fun partition A =>
        cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
          vertexBase sigma L coordinates partition W)
      (A' := fun _ => (0 : PhysicalField M Q Nc →L[ℝ] ℝ))
      (x := (0 : PhysicalField M Q Nc))
      (fun partition _hpartition =>
        cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_hasFDerivAt_zero_field
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          vertexBase sigma L coordinates partition W
          hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀') using 1
  all_goals simp

end

end YangMills.RG
