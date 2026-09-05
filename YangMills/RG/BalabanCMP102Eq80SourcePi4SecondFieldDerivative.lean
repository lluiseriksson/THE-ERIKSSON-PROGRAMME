/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainFieldDerivative

/-!
# Second physical-field derivatives of equation-(80) domain jets

The radial Taylor operator used in the source-faithful construction of
`Q(Y,B)` requires two continuous physical-field derivatives.  This file
constructs the second derivative literally from the next joint iterated
derivative of the equation-(80) functional.

The two final variables are curried and restricted to the physical-field
factor.  Their apparent order is reversed so that the result is the
Fréchet derivative of the already constructed first derivative.  Symmetry
of the iterated derivative proves that this agrees with the usual
bilinear Hessian order.
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

private noncomputable def cmp102PartialPropagatorJetFirstExtraction
    (n : ℕ) (v : Fin n → H) :
    ((H × E) [×(n + 1)]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  ((ContinuousLinearMap.compL ℝ E (H × E) ℝ).flip incl).comp
    ((ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ((H × E) →L[ℝ] ℝ)
      (fun i => (v i, 0))).comp
      (LinearIsometry.toContinuousLinearMap
        (LinearIsometryEquiv.toLinearIsometry
          (continuousMultilinearCurryRightEquiv' ℝ n (H × E) ℝ))))

private theorem cmp102PartialPropagatorJetFirstExtraction_apply
    (n : ℕ) (v : Fin n → H)
    (L : (H × E) [×(n + 1)]→L[ℝ] ℝ) :
    cmp102PartialPropagatorJetFirstExtraction n v L =
      (((continuousMultilinearCurryRightEquiv' ℝ n (H × E) ℝ) L)
        (fun i => (v i, 0))).comp
        ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) := by
  rfl

/-- The second physical-field derivative of a partial propagator jet.
The outer argument is the new Fréchet direction and the inner argument
evaluates the already constructed first derivative. -/
noncomputable def cmp102PartialPropagatorJetSecondFieldDerivative
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  let raw : (H × E) →L[ℝ] (H × E) →L[ℝ] ℝ :=
    ((continuousMultilinearCurryRightEquiv' ℝ n (H × E)
        ((H × E) →L[ℝ] ℝ))
      ((continuousMultilinearCurryRightEquiv' ℝ (n + 1)
          (H × E) ℝ)
        (iteratedFDeriv ℝ (n + 2) F (h, x))))
      (fun i => (v i, 0))
  let post : ((H × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (H × E) ℝ).flip incl
  post.comp (raw.flip.comp incl)

theorem cmp102PartialPropagatorJetSecondFieldDerivative_apply
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x a b : E) :
    cmp102PartialPropagatorJetSecondFieldDerivative F n h v x a b =
      iteratedFDeriv ℝ (n + 2) F (h, x)
        (Fin.snoc (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a)) := by
  simp [cmp102PartialPropagatorJetSecondFieldDerivative]

private theorem cmp102PartialPropagatorJetFieldDerivative_eq_extraction
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) :
    cmp102PartialPropagatorJetFieldDerivative F n h v x =
      cmp102PartialPropagatorJetFirstExtraction n v
        (iteratedFDeriv ℝ (n + 1) F (h, x)) := by
  rfl

/-- The explicit second field derivative is the Fréchet derivative of the
explicit first field derivative at every physical field. -/
theorem
    cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    HasFDerivAt
      (cmp102PartialPropagatorJetFieldDerivative F n h v)
      (cmp102PartialPropagatorJetSecondFieldDerivative F n h v x) x := by
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ (n + 1) F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : HasFDerivAt (fun y : E => (h, y)) incl x :=
    (hasFDerivAt_const (x := x) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := x))
  have hcomp :=
    hjet.differentiableAt.hasFDerivAt.comp x hpath
  have hext :=
    (cmp102PartialPropagatorJetFirstExtraction n v).hasFDerivAt.comp x hcomp
  have hfun :
      (⇑(cmp102PartialPropagatorJetFirstExtraction n v) ∘
        iteratedFDeriv ℝ (n + 1) F ∘ fun y : E => (h, y)) =
        cmp102PartialPropagatorJetFieldDerivative F n h v := by
    funext y
    exact
      (cmp102PartialPropagatorJetFieldDerivative_eq_extraction
        F n h v y).symm
  rw [hfun] at hext
  convert hext using 1
  ext a b
  simp only [ContinuousLinearMap.comp_apply,
    cmp102PartialPropagatorJetFirstExtraction_apply,
    fderiv_iteratedFDeriv, Function.comp_apply]
  rw [cmp102PartialPropagatorJetSecondFieldDerivative_apply]
  have hperm :=
    hF.contDiffAt.iteratedFDeriv_comp_perm
      (x := (h, x))
      (Fin.cons (0, a)
        (Fin.snoc (fun i => (v i, 0)) (0, b)))
      (finRotate (n + 2))
  have hrotate :
      (Fin.cons (0, a)
          (Fin.snoc (fun i => (v i, 0)) (0, b))) ∘
          (finRotate (n + 2)) =
        Fin.snoc
          (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a) := by
    funext i
    simpa [Function.comp_def] using
      congrFun
        (Fin.snoc_eq_cons_rotate
          (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a)).symm i
  rw [hrotate] at hperm
  simpa [incl, continuousMultilinearCurryLeftEquiv_apply,
    continuousMultilinearCurryRightEquiv_apply'] using hperm

set_option synthInstance.maxHeartbeats 200000 in
/-- The explicit second derivative remains continuous when the
propagator point, all propagator directions, and the field vary
continuously. -/
theorem
    continuous_cmp102PartialPropagatorJetSecondFieldDerivative_comp
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : T → H) (v : T → Fin n → H)
    (x : T → E)
    (hh : Continuous h) (hv : ∀ i, Continuous fun t => v t i)
    (hx : Continuous x) :
    Continuous fun t =>
      cmp102PartialPropagatorJetSecondFieldDerivative
        F n (h t) (v t) (x t) := by
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  let raw : T → (H × E) →L[ℝ] (H × E) →L[ℝ] ℝ :=
    fun t =>
      ((continuousMultilinearCurryRightEquiv' ℝ n (H × E)
          ((H × E) →L[ℝ] ℝ))
        ((continuousMultilinearCurryRightEquiv' ℝ (n + 1)
            (H × E) ℝ)
          (iteratedFDeriv ℝ (n + 2) F (h t, x t))))
        (fun i => (v t i, 0))
  let post : ((H × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (H × E) ℝ).flip incl
  have hfd : Continuous (iteratedFDeriv ℝ (n + 2) F) :=
    hF.continuous_iteratedFDeriv (by simp)
  have hraw : Continuous raw := by
    dsimp [raw]
    fun_prop
  have hflip : Continuous fun t => (raw t).flip :=
    (ContinuousLinearMap.flipₗᵢ ℝ (H × E) (H × E) ℝ).continuous.comp hraw
  have hrestricted :
      Continuous fun t => (raw t).flip.comp incl :=
    hflip.clm_comp_const incl
  have hresult :
      Continuous fun t => post.comp ((raw t).flip.comp incl) :=
    hrestricted.const_clm_comp post
  simpa [cmp102PartialPropagatorJetSecondFieldDerivative,
    raw, incl, post] using hresult

end MixedJets

/-- Source-specific second field derivative of one domain-choice term. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
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
    PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ :=
  cmp102PartialPropagatorJetSecondFieldDerivative
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

/-- The source-specific second derivative differentiates the literal first
derivative of one domain-choice coefficient. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt_hasFDerivAt
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
        cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase sigma L coordinates partition choice)
      (cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition choice)
      A := by
  let F :=
    fun p : PhysicalEndomorphism M Q Nc × PhysicalField M Q Nc =>
      cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_cmp102Eq80JointPotential D D₃ V₀ Δπ J hD hD₃ hV₀
  simpa [cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt,
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt,
    F] using
    cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
      F hF partition.length
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

/-- Second field derivative of a complete physical-domain coefficient,
after both finite Faà di Bruno sums. -/
noncomputable def
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
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
    PhysicalField M Q Nc →L[ℝ]
      PhysicalField M Q Nc →L[ℝ] ℝ :=
  ∑ partition : OrderedFinpartition n,
    ∑ choice ∈
        (Finset.univ :
          Finset (CMP102Eq80FaaDiBrunoDomainChoice
            (Q := Q) partition)).filter
          (fun choice =>
            cmp102Eq80SourcePi4AnchoredDomainUnion anchor
              Finset.univ choice = W),
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates partition choice

/-- The complete second derivative differentiates the complete first
derivative after the two finite source sums. -/
theorem
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt_hasFDerivAt
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
        cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
          vertexBase sigma L coordinates W)
      (cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
        vertexBase sigma L coordinates W)
      A := by
  classical
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientFieldDerivativeAt
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
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
          cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
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
          cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
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
              cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J x
                vertexBase sigma L coordinates partition choice)
            (A' := fun choice =>
              cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase sigma L coordinates partition choice)
            (x := A)
            (fun choice _hchoice =>
              cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceFieldDerivativeAt_hasFDerivAt
                (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J A
                vertexBase sigma L coordinates partition choice
                hD hD₃ hV₀) using 1) using 1

set_option maxHeartbeats 64000000 in
/-- Along every coordinatewise continuous weakening contour, the explicit
second derivative of one domain-choice coefficient is continuous jointly
with the physical field. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt_comp
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
      cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt
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
  simpa [
    cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt,
    F, H₀, directions] using
    continuous_cmp102PartialPropagatorJetSecondFieldDerivative_comp
      F hF partition.length H₀ directions A hbase hargs hA

set_option maxHeartbeats 64000000 in
/-- The complete second derivative is continuous jointly in the physical
field and weakening contour. -/
theorem
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt_comp
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
      cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J (A t)
        vertexBase (sigma t) L coordinates W := by
  classical
  unfold
    cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientSecondFieldDerivativeAt
  apply continuous_finset_sum
  intro partition _hpartition
  apply continuous_finset_sum
  intro choice _hchoice
  exact
    continuous_cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceSecondFieldDerivativeAt_comp
      anchor K hc hmass hK D D₃ V₀ Δπ J
      hAhead hrho hrate Cert htri hrange hΔ hΔ1
      A hA vertexBase sigma hsigma L coordinates partition choice
      hRweak hcap hsmall hD hD₃ hV₀

end

end YangMills.RG
