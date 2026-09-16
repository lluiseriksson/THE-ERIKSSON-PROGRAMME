/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80ParametricIntervalFirstOrder

/-!
# Continuous physical-field derivatives of equation-(80) domain jets

The parametric FTC theorem needs a continuous family of derivatives with
respect to the physical field, while the weakening coordinate itself is
only known to vary continuously.  This file constructs that derivative
literally from the next joint iterated derivative of the equation-(80)
functional.

The last variable is separated by the continuous multilinear
`curryRight` equivalence.  Consequently both the propagator point and all
localized propagator directions may vary continuously without adding a
derivative hypothesis for the weakening parameter.
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

variable {H E T : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T]

/-- The physical-field derivative of a partial propagator jet, represented
by currying the final variable of the next joint iterated derivative. -/
noncomputable def cmp102PartialPropagatorJetFieldDerivative
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : E →L[ℝ] ℝ :=
  ((continuousMultilinearCurryRightEquiv' ℝ n (H × E) ℝ)
      (iteratedFDeriv ℝ (n + 1) F (h, x))
      (fun i => (v i, 0))).comp
      ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))

/-- The derivative of the partial jet before rotating its new direction to
the final slot. -/
theorem fderiv_cmp102PartialPropagatorJet_at
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    fderiv ℝ (cmp102PartialPropagatorJet F n h v) x =
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).comp
        ((fderiv ℝ (iteratedFDeriv ℝ n F) (h, x)).comp
          ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))) := by
  unfold cmp102PartialPropagatorJet
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : HasFDerivAt (fun y : E => (h, y))
      ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) x :=
    (hasFDerivAt_const (x := x) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := x))
  have hcomp :=
    hjet.differentiableAt.hasFDerivAt.comp x hpath
  have heval :=
    (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ
      (fun i => (v i, 0))).hasFDerivAt.comp x hcomp
  simpa using heval.fderiv

/-- The curried next derivative is exactly the Fréchet derivative of the
partial propagator jet at an arbitrary physical field. -/
theorem fderiv_cmp102PartialPropagatorJet_eq_fieldDerivative
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    fderiv ℝ (cmp102PartialPropagatorJet F n h v) x =
      cmp102PartialPropagatorJetFieldDerivative F n h v x := by
  rw [fderiv_cmp102PartialPropagatorJet_at F hF n h v x]
  ext a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
    ContinuousMultilinearMap.apply_apply, fderiv_iteratedFDeriv,
    Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply]
  unfold cmp102PartialPropagatorJetFieldDerivative
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
    continuousMultilinearCurryRightEquiv_apply']
  have hperm :=
    hF.contDiffAt.iteratedFDeriv_comp_perm
      (x := (h, x))
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
  exact hperm.symm

/-- The literal field derivative remains continuous when the propagator
point, every propagator direction, and the physical field vary
continuously. -/
theorem continuous_cmp102PartialPropagatorJetFieldDerivative_comp
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : T → H) (v : T → Fin n → H)
    (x : T → E)
    (hh : Continuous h) (hv : ∀ i, Continuous fun t => v t i)
    (hx : Continuous x) :
    Continuous fun t =>
      cmp102PartialPropagatorJetFieldDerivative
        F n (h t) (v t) (x t) := by
  unfold cmp102PartialPropagatorJetFieldDerivative
  have hfd :
      Continuous (iteratedFDeriv ℝ (n + 1) F) :=
    hF.continuous_iteratedFDeriv (by simp)
  fun_prop

/-- Partial propagator jets themselves are continuous under the same
simultaneous variation of point, directions, and physical field. -/
theorem continuous_cmp102PartialPropagatorJet_comp
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : T → H) (v : T → Fin n → H)
    (x : T → E)
    (hh : Continuous h) (hv : ∀ i, Continuous fun t => v t i)
    (hx : Continuous x) :
    Continuous fun t =>
      cmp102PartialPropagatorJet F n (h t) (v t) (x t) := by
  unfold cmp102PartialPropagatorJet
  have hfd :
      Continuous (iteratedFDeriv ℝ n F) :=
    hF.continuous_iteratedFDeriv (by simp)
  fun_prop

end MixedJets

/-- The source-specific physical-field derivative of one domain-choice
term. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition) :
    PhysicalField M Q Nc →L[ℝ] ℝ :=
  cmp102PartialPropagatorJetFieldDerivative
    (fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2)
    partition.length
    (cmp116FiniteMultiaffineInterpolation
      (fun u =>
        cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
          (R := R) anchor K hc hmass hK u ∅)
      vertexBase L sigma)
    (fun block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK sigma
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block))
    A

/-- The explicit source derivative is the Fréchet derivative of the
domain-choice coefficient at every physical field. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    HasFDerivAt
      (fun x =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase sigma L coordinates partition choice)
      (cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition choice)
      A := by
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
  have hfun :
      (fun x =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase sigma L coordinates partition choice) =
        cmp102PartialPropagatorJet
          F partition.length H₀ directions := by
    funext x
    have hs :=
      iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
        F hF partition.length H₀ directions x
    simpa [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt,
      cmp102Eq80PotentialAsFunctionOfPropagator, ftaylorSeries,
      F, H₀, directions] using hs
  rw [hfun]
  have hdiff :
      Differentiable ℝ
        (cmp102PartialPropagatorJet
          F partition.length H₀ directions) := by
    unfold cmp102PartialPropagatorJet
    have hjet : Differentiable ℝ
        (iteratedFDeriv ℝ partition.length F) :=
      hF.differentiable_iteratedFDeriv (by simp)
    fun_prop
  have hder :
      HasFDerivAt
        (cmp102PartialPropagatorJet
          F partition.length H₀ directions)
        (fderiv ℝ
          (cmp102PartialPropagatorJet
            F partition.length H₀ directions) A)
        A :=
    hdiff.differentiableAt.hasFDerivAt
  rw [fderiv_cmp102PartialPropagatorJet_eq_fieldDerivative
    F hF partition.length H₀ directions A] at hder
  simpa [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt,
    F, H₀, directions] using hder

set_option maxHeartbeats 64000000 in
/-- Along every coordinatewise continuous physical contour, the explicit
field derivative of a domain-choice coefficient is continuous jointly with
a continuously varying physical field. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt_comp
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (A : T → PhysicalField M Q Nc) (hA : Continuous A)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A t)
        vertexBase (sigma t) L coordinates partition choice := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let H₀ :=
    fun t =>
      cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        vertexBase L (sigma t)
  let directions :=
    fun t block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK (sigma t)
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block)
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_cmp102Eq80JointPotential D D₃ V₀ Δπ J hD hD₃ hV₀
  have hbase : Continuous H₀ :=
    (contDiff_cmp116FiniteMultiaffineInterpolation
      0 _ vertexBase L).continuous.comp (continuous_pi hsigma)
  have hargs (block : Fin partition.length) :
      Continuous fun t => directions t block :=
    continuous_cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_comp
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hsigma hRweak hcap
      (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
        partition coordinates block)
      (choice block) hsmall
  simpa [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt,
    F, H₀, directions] using
    continuous_cmp102PartialPropagatorJetFieldDerivative_comp
      F hF partition.length H₀ directions A hbase hargs hA

set_option maxHeartbeats 64000000 in
/-- The domain-choice coefficient is itself continuous under the same joint
variation of physical field and weakening contour. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_joint
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (A : T → PhysicalField M Q Nc) (hA : Continuous A)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (partition : OrderedFinpartition n)
    (choice : CMP102Eq80FaaDiBrunoDomainChoice
      (Q := Q) partition)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A t)
        vertexBase (sigma t) L coordinates partition choice := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let H₀ :=
    fun t =>
      cmp116FiniteMultiaffineInterpolation
        (fun u =>
          cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
            (R := R) anchor K hc hmass hK u ∅)
        vertexBase L (sigma t)
  let directions :=
    fun t block =>
      cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK (sigma t)
        (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
          partition coordinates block)
        (choice block)
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_cmp102Eq80JointPotential D D₃ V₀ Δπ J hD hD₃ hV₀
  have hbase : Continuous H₀ :=
    (contDiff_cmp116FiniteMultiaffineInterpolation
      0 _ vertexBase L).continuous.comp (continuous_pi hsigma)
  have hargs (block : Fin partition.length) :
      Continuous fun t => directions t block :=
    continuous_cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_comp
      anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
      sigma hsigma hRweak hcap
      (cmp102Eq80SourcePi4FaaDiBrunoBlockCarrier
        partition coordinates block)
      (choice block) hsmall
  have hpartial :=
    continuous_cmp102PartialPropagatorJet_comp
      F hF partition.length H₀ directions A hbase hargs hA
  apply hpartial.congr
  intro t
  have hs :=
    iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
      F hF partition.length (H₀ t) (directions t) (A t)
  simpa [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt,
    cmp102Eq80PotentialAsFunctionOfPropagator, ftaylorSeries,
    F, H₀, directions] using hs.symm

/-- The explicit derivative of a domain-choice term vanishes on the
zero-field slice under the physical component normalizations. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt_zero_field
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
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase sigma L coordinates partition choice = 0 := by
  have hexplicit :=
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
      vertexBase sigma L coordinates partition choice hD hD₃ hV₀
  have hzero :=
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase sigma L coordinates partition choice
      hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'
  exact hexplicit.unique hzero

/-- Explicit derivative of a complete physical-domain coefficient, after
the two finite Faà di Bruno sums. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q))) :
    PhysicalField M Q Nc →L[ℝ] ℝ :=
  ∑ partition : OrderedFinpartition n,
    ∑ choice ∈
        (Finset.univ :
          Finset (CMP102Eq80FaaDiBrunoDomainChoice
            (Q := Q) partition)).filter
          (fun choice =>
            cmp102Eq80SourcePi4AnchoredDomainUnion anchor
              Finset.univ choice = W),
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition choice

/-- The complete explicit derivative differentiates the complete physical
domain coefficient. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_hasFDerivAt_explicit
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (vertexBase sigma : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    HasFDerivAt
      (fun x =>
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase sigma L coordinates W)
      (cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates W)
      A := by
  classical
  unfold cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
  convert HasFDerivAt.fun_sum
      (u := (Finset.univ : Finset (OrderedFinpartition n)))
      (A := fun partition x =>
        ∑ choice ∈
            (Finset.univ :
              Finset (CMP102Eq80FaaDiBrunoDomainChoice
                (Q := Q) partition)).filter
              (fun choice =>
                cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                  Finset.univ choice = W),
          cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
            vertexBase sigma L coordinates partition choice)
      (A' := fun partition =>
        ∑ choice ∈
            (Finset.univ :
              Finset (CMP102Eq80FaaDiBrunoDomainChoice
                (Q := Q) partition)).filter
              (fun choice =>
                cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                  Finset.univ choice = W),
          cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
            vertexBase sigma L coordinates partition choice)
      (x := A)
      (fun partition _hpartition => by
        convert HasFDerivAt.fun_sum
            (u :=
              (Finset.univ :
                Finset (CMP102Eq80FaaDiBrunoDomainChoice
                  (Q := Q) partition)).filter
                (fun choice =>
                  cmp102Eq80SourcePi4AnchoredDomainUnion anchor
                    Finset.univ choice = W))
            (A := fun choice x =>
              cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                vertexBase sigma L coordinates partition choice)
            (A' := fun choice =>
              cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase sigma L coordinates partition choice)
            (x := A)
            (fun choice _hchoice =>
              cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase sigma L coordinates partition choice
                hD hD₃ hV₀) using 1) using 1

set_option maxHeartbeats 64000000 in
/-- The complete explicit field derivative is continuous jointly in the
physical field and weakening contour. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt_comp
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (A : T → PhysicalField M Q Nc) (hA : Continuous A)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A t)
        vertexBase (sigma t) L coordinates W := by
  classical
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
  apply continuous_finset_sum
  intro partition _hpartition
  apply continuous_finset_sum
  intro choice _hchoice
  exact
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt_comp
      anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      A hA vertexBase sigma hsigma L coordinates partition choice
      hRweak hcap hsmall hD hD₃ hV₀

/-- The complete domain coefficient is continuous under the same joint
variation. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_joint
    {M Q Nc R Δ n : ℕ} {T : Type*}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [TopologicalSpace T]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (A : T → PhysicalField M Q Nc) (hA : Continuous A)
    (vertexBase : FinBox 4 (2 * Q) → ℝ)
    (sigma : T → FinBox 4 (2 * Q) → ℝ)
    (hsigma : ∀ d, Continuous fun t => sigma t d)
    (L : List (FinBox 4 (2 * Q)))
    (coordinates : Fin n → FinBox 4 (2 * Q))
    (W : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ t d, ‖(sigma t d : ℂ)‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    Continuous fun t =>
      cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A t)
        vertexBase (sigma t) L coordinates W := by
  classical
  unfold cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt
  apply continuous_finset_sum
  intro partition _hpartition
  apply continuous_finset_sum
  intro choice _hchoice
  exact
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_joint
      anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      A hA vertexBase sigma hsigma L coordinates partition choice
      hRweak hcap hsmall hD hD₃ hV₀

/-- The explicit derivative of a complete physical-domain coefficient
vanishes at the zero field. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt_zero_field
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
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J 0
        vertexBase sigma L coordinates W = 0 := by
  classical
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
  apply Finset.sum_eq_zero
  intro partition _hpartition
  apply Finset.sum_eq_zero
  intro choice _hchoice
  exact
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt_zero_field
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      vertexBase sigma L coordinates partition choice
      hD hD₃ hV₀ hD0 hD₃0 hD₃' hV₀'

end

end YangMills.RG
