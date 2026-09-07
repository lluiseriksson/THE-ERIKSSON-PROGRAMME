/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCSecondFieldDerivative
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientThirdFieldDerivative

/-!
# Three physical-field derivatives through the literal domain FTC integral

The source-metric third jet previously applied only to one reconstructed
domain coefficient. This file transports that jet through the literal
affine FTC integral defining the equation-(80) domain potential.

The proof stays in the nested continuous-linear-map representation used by
the second-order FTC lane. A jointly smooth partial propagator jet generates
its vertical derivatives internally; differentiation under the interval
integral then identifies the third derivative of the actual FTC potential.
-/

open MeasureTheory
open scoped Interval RealInnerProductSpace

namespace YangMills.RG

noncomputable section

section GenericAffineJetFTCThird

variable {H E G : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [Nontrivial E] [FiniteDimensional ℝ E]

/- Mathlib does not choose the operator-norm instance automatically at the
third nested level. Pinning it here keeps the Banach-valued FTC theorem on
the same operator-norm topology as the second-order lane. -/
noncomputable local instance nestedTwoNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] ℝ)
    (σ₁₂ := RingHom.id ℝ)

noncomputable local instance nestedThreeNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] (E →L[ℝ] ℝ)) (σ₁₂ := RingHom.id ℝ)

noncomputable local instance nestedThreeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] (E →L[ℝ] ℝ)) (σ₁₂ := RingHom.id ℝ)
    (𝕜' := ℝ)

/-- Fréchet differentiation in the physical-field coordinate of a joint
map on propagator and field variables. -/
noncomputable def cmp102PhysicalVerticalFDeriv
    (F : H × E → G) (p : H × E) : E →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ H E)

/-- A smooth joint map has a smooth vertical derivative. -/
theorem contDiff_cmp102PhysicalVerticalFDeriv
    (F : H × E → G) (hF : ContDiff ℝ ⊤ F) :
    ContDiff ℝ ⊤ (cmp102PhysicalVerticalFDeriv F) := by
  unfold cmp102PhysicalVerticalFDeriv
  have hd : ContDiff ℝ ⊤ (fderiv ℝ F) :=
    hF.fderiv_right (m := ⊤) (by simp)
  fun_prop

/-- The vertical derivative differentiates every fixed propagator slice. -/
theorem cmp102PhysicalVerticalFDeriv_hasFDerivAt
    (F : H × E → G) (hF : ContDiff ℝ ⊤ F)
    (h : H) (x : E) :
    HasFDerivAt (fun y => F (h, y))
      (cmp102PhysicalVerticalFDeriv F (h, x)) x := by
  exact (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
    x ((hasFDerivAt_const (x := x) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := x)))

/-- The partial propagator jet as one joint scalar map. -/
noncomputable def cmp102PartialPropagatorJetJoint
    (F : H × E → ℝ) (n : ℕ) (v : Fin n → H) :
    H × E → ℝ := fun p =>
  cmp102PartialPropagatorJet F n p.1 v p.2

/-- Fixed propagator directions preserve smooth joint dependence on the
propagator point and physical field. -/
theorem contDiff_cmp102PartialPropagatorJetJoint
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (v : Fin n → H) :
    ContDiff ℝ ⊤ (cmp102PartialPropagatorJetJoint F n v) := by
  unfold cmp102PartialPropagatorJetJoint cmp102PartialPropagatorJet
  let ev :=
    ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ (fun i => (v i, 0))
  have hfd : ContDiff ℝ ⊤ (iteratedFDeriv ℝ n F) :=
    hF.iteratedFDeriv_right (m := ⊤) (by simp)
  exact ev.contDiff.comp hfd

/-- The third vertical derivative of a joint partial propagator jet. -/
noncomputable def cmp102PartialPropagatorJetThirdFieldDerivativeNested
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) :
    E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  cmp102PhysicalVerticalFDeriv
    (cmp102PhysicalVerticalFDeriv
      (cmp102PhysicalVerticalFDeriv
        (cmp102PartialPropagatorJetJoint F n v))) (h, x)

/-- The first vertical derivative agrees with the already constructed
literal first field derivative. -/
theorem cmp102PartialPropagatorJetJoint_vertical_eq_first
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    cmp102PhysicalVerticalFDeriv
        (cmp102PartialPropagatorJetJoint F n v) (h, x) =
      cmp102PartialPropagatorJetFieldDerivative F n h v x := by
  have hj :=
    cmp102PhysicalVerticalFDeriv_hasFDerivAt
      (cmp102PartialPropagatorJetJoint F n v)
      (contDiff_cmp102PartialPropagatorJetJoint F hF n v) h x
  have hp :=
    cmp102PartialPropagatorJet_hasFDerivAt F hF n h v x
  have hj' :
      HasFDerivAt (cmp102PartialPropagatorJet F n h v)
        (cmp102PhysicalVerticalFDeriv
          (cmp102PartialPropagatorJetJoint F n v) (h, x)) x := by
    simpa [cmp102PartialPropagatorJetJoint] using hj
  exact hj'.fderiv.symm.trans hp.fderiv

/-- The second vertical derivative agrees with the already constructed
literal Hessian. -/
theorem cmp102PartialPropagatorJetJoint_vertical_two_eq_second
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    cmp102PhysicalVerticalFDeriv
        (cmp102PhysicalVerticalFDeriv
          (cmp102PartialPropagatorJetJoint F n v)) (h, x) =
      cmp102PartialPropagatorJetSecondFieldDerivative F n h v x := by
  let J := cmp102PartialPropagatorJetJoint F n v
  have hJ : ContDiff ℝ ⊤ J :=
    contDiff_cmp102PartialPropagatorJetJoint F hF n v
  have hJ₁ : ContDiff ℝ ⊤ (cmp102PhysicalVerticalFDeriv J) :=
    contDiff_cmp102PhysicalVerticalFDeriv J hJ
  have hslice :=
    cmp102PhysicalVerticalFDeriv_hasFDerivAt
      (cmp102PhysicalVerticalFDeriv J) hJ₁ h x
  have heq :
      (fun y => cmp102PhysicalVerticalFDeriv J (h, y)) =
        cmp102PartialPropagatorJetFieldDerivative F n h v := by
    funext y
    exact cmp102PartialPropagatorJetJoint_vertical_eq_first
      F hF n h v y
  rw [heq] at hslice
  exact hslice.fderiv.symm.trans
    (cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
      F hF n h v x).fderiv

/-- The nested third jet differentiates the literal Hessian on every
fixed propagator slice. -/
theorem
    cmp102PartialPropagatorJetSecondFieldDerivative_hasFDerivAt_nested
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    HasFDerivAt
      (cmp102PartialPropagatorJetSecondFieldDerivative F n h v)
      (cmp102PartialPropagatorJetThirdFieldDerivativeNested
        F n h v x) x := by
  let J := cmp102PartialPropagatorJetJoint F n v
  have hJ : ContDiff ℝ ⊤ J :=
    contDiff_cmp102PartialPropagatorJetJoint F hF n v
  have hJ₁ : ContDiff ℝ ⊤ (cmp102PhysicalVerticalFDeriv J) :=
    contDiff_cmp102PhysicalVerticalFDeriv J hJ
  have hJ₂ :
      ContDiff ℝ ⊤
        (cmp102PhysicalVerticalFDeriv
          (cmp102PhysicalVerticalFDeriv J)) :=
    contDiff_cmp102PhysicalVerticalFDeriv
      (cmp102PhysicalVerticalFDeriv J) hJ₁
  have hslice :=
    cmp102PhysicalVerticalFDeriv_hasFDerivAt
      (cmp102PhysicalVerticalFDeriv
        (cmp102PhysicalVerticalFDeriv J)) hJ₂ h x
  have heq :
      (fun y =>
        cmp102PhysicalVerticalFDeriv
          (cmp102PhysicalVerticalFDeriv J) (h, y)) =
        cmp102PartialPropagatorJetSecondFieldDerivative F n h v := by
    funext y
    exact cmp102PartialPropagatorJetJoint_vertical_two_eq_second
      F hF n h v y
  rw [heq] at hslice
  simpa [cmp102PartialPropagatorJetThirdFieldDerivativeNested, J]
    using hslice

/-- The nested third jet varies continuously with propagator point and
physical field. -/
theorem
    continuous_cmp102PartialPropagatorJetThirdFieldDerivativeNested_comp
    {T : Type*} [TopologicalSpace T]
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : T → H) (v : Fin n → H) (x : T → E)
    (hh : Continuous h) (hx : Continuous x) :
    Continuous fun t =>
      cmp102PartialPropagatorJetThirdFieldDerivativeNested
        F n (h t) v (x t) := by
  let J := cmp102PartialPropagatorJetJoint F n v
  have hJ : ContDiff ℝ ⊤ J :=
    contDiff_cmp102PartialPropagatorJetJoint F hF n v
  have hJ₁ : ContDiff ℝ ⊤ (cmp102PhysicalVerticalFDeriv J) :=
    contDiff_cmp102PhysicalVerticalFDeriv J hJ
  have hJ₂ :
      ContDiff ℝ ⊤
        (cmp102PhysicalVerticalFDeriv
          (cmp102PhysicalVerticalFDeriv J)) :=
    contDiff_cmp102PhysicalVerticalFDeriv
      (cmp102PhysicalVerticalFDeriv J) hJ₁
  have hJ₃ :
      Continuous
        (cmp102PhysicalVerticalFDeriv
          (cmp102PhysicalVerticalFDeriv
            (cmp102PhysicalVerticalFDeriv J))) :=
    (contDiff_cmp102PhysicalVerticalFDeriv
      (cmp102PhysicalVerticalFDeriv
        (cmp102PhysicalVerticalFDeriv J)) hJ₂).continuous
  exact hJ₃.comp (hh.prodMk hx)

/-- The nested derivative has exactly the norm of the third iterated
derivative of the fixed-propagator coefficient. -/
theorem norm_cmp102PartialPropagatorJetThirdFieldDerivativeNested_eq
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    ‖cmp102PartialPropagatorJetThirdFieldDerivativeNested
        F n h v x‖ =
      ‖iteratedFDeriv ℝ 3
        (cmp102PartialPropagatorJet F n h v) x‖ := by
  let g : E → ℝ := cmp102PartialPropagatorJet F n h v
  let g₁ : E → (E →L[ℝ] ℝ) :=
    cmp102PartialPropagatorJetFieldDerivative F n h v
  let g₂ : E → (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    cmp102PartialPropagatorJetSecondFieldDerivative F n h v
  have hg₁ : g₁ = fderiv ℝ g := by
    funext y
    exact (cmp102PartialPropagatorJet_hasFDerivAt
      F hF n h v y).fderiv.symm
  have hg₂ : g₂ = fderiv ℝ g₁ := by
    funext y
    exact
      (cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
        F hF n h v y).fderiv.symm
  have hg₃ :
      fderiv ℝ g₂ x =
        cmp102PartialPropagatorJetThirdFieldDerivativeNested
          F n h v x :=
    (cmp102PartialPropagatorJetSecondFieldDerivative_hasFDerivAt_nested
      F hF n h v x).fderiv
  calc
    ‖cmp102PartialPropagatorJetThirdFieldDerivativeNested
        F n h v x‖ = ‖fderiv ℝ g₂ x‖ := by rw [hg₃]
    _ = ‖iteratedFDeriv ℝ 1 g₂ x‖ := by
      rw [norm_iteratedFDeriv_one]
    _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g₁) x‖ := by rw [hg₂]
    _ = ‖iteratedFDeriv ℝ 2 g₁ x‖ := norm_iteratedFDeriv_fderiv
    _ = ‖iteratedFDeriv ℝ 2 (fderiv ℝ g) x‖ := by rw [hg₁]
    _ = ‖iteratedFDeriv ℝ 3 g x‖ := norm_iteratedFDeriv_fderiv
    _ = _ := rfl

/-- Integral of the nested third physical-field derivative along the
literal affine propagator segment. -/
noncomputable def cmp102AffinePropagatorJetFTCThirdFieldDerivative
    (F : H × E → ℝ) (n : ℕ) (P T : H)
    (v : Fin n → H) (x : E) :
    E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ∫ t in (0 : ℝ)..1,
    cmp102PartialPropagatorJetThirdFieldDerivativeNested
      F n (P + t • T) v x

/-- Third differentiation under the literal affine FTC integral. -/
theorem
    cmp102AffinePropagatorJetFTCSecondFieldDerivative_hasFDerivAt
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) (x : E) :
    HasFDerivAt
      (cmp102AffinePropagatorJetFTCSecondFieldDerivative F n P T v)
      (cmp102AffinePropagatorJetFTCThirdFieldDerivative
        F n P T v x) x := by
  let A : E × ℝ → (E →L[ℝ] (E →L[ℝ] ℝ)) := fun p =>
    cmp102PartialPropagatorJetSecondFieldDerivative
      F n (P + p.2 • T) v p.1
  let A' : E × ℝ → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := fun p =>
    cmp102PartialPropagatorJetThirdFieldDerivativeNested
      F n (P + p.2 • T) v p.1
  have hA : Continuous A :=
    continuous_cmp102PartialPropagatorJetSecondFieldDerivative_comp
      F hF n
      (fun p : E × ℝ => P + p.2 • T)
      (fun _p : E × ℝ => v)
      (fun p : E × ℝ => p.1)
      (by fun_prop) (fun _i => by fun_prop) (by fun_prop)
  have hA' : Continuous A' :=
    continuous_cmp102PartialPropagatorJetThirdFieldDerivativeNested_comp
      F hF n
      (fun p : E × ℝ => P + p.2 • T) v
      (fun p : E × ℝ => p.1)
      (by fun_prop) (by fun_prop)
  have hder :=
    hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative_banach
      A A' x hA hA'
      (fun y t =>
        cmp102PartialPropagatorJetSecondFieldDerivative_hasFDerivAt_nested
          F hF n (P + t • T) v y)
  simpa [
    cmp102AffinePropagatorJetFTCSecondFieldDerivative,
    cmp102AffinePropagatorJetFTCThirdFieldDerivative,
    A, A'] using hder

/-- A uniform third-jet bound on the coefficient yields the same bound
for the integrated third derivative. -/
theorem norm_cmp102AffinePropagatorJetFTCThirdFieldDerivative_le
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) (x : E)
    (C : ℝ)
    (hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 3
        (cmp102PartialPropagatorJet F n (P + t • T) v) x‖ ≤ C) :
    ‖cmp102AffinePropagatorJetFTCThirdFieldDerivative
        F n P T v x‖ ≤ C := by
  unfold cmp102AffinePropagatorJetFTCThirdFieldDerivative
  have hconst :
      IntervalIntegrable (fun _t : ℝ => C) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hnorm :
      ‖∫ t in (0 : ℝ)..1,
          cmp102PartialPropagatorJetThirdFieldDerivativeNested
            F n (P + t • T) v x‖ ≤
        ∫ _t in (0 : ℝ)..1, C := by
    apply intervalIntegral.norm_integral_le_of_norm_le
      (by norm_num : (0 : ℝ) ≤ 1)
      (Filter.Eventually.of_forall ?_) hconst
    intro t ht
    rw [
      norm_cmp102PartialPropagatorJetThirdFieldDerivativeNested_eq
        F hF n (P + t • T) v x]
    exact hbound t (by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
  simpa using hnorm

/-- The third iterated derivative of the actual FTC potential has the norm
of the integrated nested third derivative. -/
theorem
    norm_iteratedFDeriv_three_cmp102AffinePropagatorJetFTC_eq
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) (x : E) :
    ‖iteratedFDeriv ℝ 3
        (cmp102AffinePropagatorJetFTC F n P T v) x‖ =
      ‖cmp102AffinePropagatorJetFTCThirdFieldDerivative
        F n P T v x‖ := by
  let g : E → ℝ := cmp102AffinePropagatorJetFTC F n P T v
  let g₁ : E → (E →L[ℝ] ℝ) :=
    cmp102AffinePropagatorJetFTCFirstFieldDerivative F n P T v
  let g₂ : E → (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    cmp102AffinePropagatorJetFTCSecondFieldDerivative F n P T v
  have hg₁ : g₁ = fderiv ℝ g := by
    funext y
    exact (cmp102AffinePropagatorJetFTC_hasFDerivAt
      F hF n P T v y).fderiv.symm
  have hg₂ : g₂ = fderiv ℝ g₁ := by
    funext y
    exact
      (cmp102AffinePropagatorJetFTCFirstFieldDerivative_hasFDerivAt
        F hF n P T v y).fderiv.symm
  have hg₃ :
      fderiv ℝ g₂ x =
        cmp102AffinePropagatorJetFTCThirdFieldDerivative
          F n P T v x :=
    (cmp102AffinePropagatorJetFTCSecondFieldDerivative_hasFDerivAt
      F hF n P T v x).fderiv
  calc
    ‖iteratedFDeriv ℝ 3 g x‖ =
        ‖iteratedFDeriv ℝ 2 (fderiv ℝ g) x‖ :=
      norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv ℝ 2 g₁ x‖ := by rw [hg₁]
    _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g₁) x‖ :=
      norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv ℝ 1 g₂ x‖ := by rw [hg₂]
    _ = ‖fderiv ℝ g₂ x‖ := norm_iteratedFDeriv_one _
    _ = ‖cmp102AffinePropagatorJetFTCThirdFieldDerivative
          F n P T v x‖ := by rw [hg₃]

end GenericAffineJetFTCThird

end

end YangMills.RG
