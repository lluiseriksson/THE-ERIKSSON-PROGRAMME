/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGlobalStratification
import YangMills.RG.PhysicalGaugeOperator

/-!
# Scale-typed realization of the CMP99 global strata

Printed CMP99 p. 393 does not place all `Lambda_j` on one lattice.  It states

`Omega_j \ Omega_{j+1} = B^j(Lambda_j)`

and `Lambda_j` belongs to the lattice of spacing `L^j eta`.  Consequently the
order-`j` average `Q'_j` and the restriction to `Lambda_j` must have a target
type depending on `j`.

This file records exactly that dependent typing.  A scaled stratification
contains a common fine-carrier stratification, the lattice type at each
scale, the fine block represented by one scale site, and the equality saying
that the lifted scale stratum is precisely the corresponding global shell.
It then constructs the literal restriction map and the physical quadratic
form in (3.24).
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u v w

/-- A dependent-lattice realization of
`Omega_r \ Omega_{r+1} = B^r(Lambda_r)` from printed CMP99 p. 393. -/
structure CMP99SourceScaledStratification
    (FineSite : Type u) [DecidableEq FineSite]
    (n : ℕ) (ScaleSite : Fin n → Type v)
    [∀ r, DecidableEq (ScaleSite r)] where
  global : CMP99SourceGlobalStratification FineSite n
  fineBlock : ∀ r, ScaleSite r → Finset FineSite
  strata : ∀ r, Finset (ScaleSite r)
  lift_stratum : ∀ r,
    (strata r).biUnion (fineBlock r) = global.stratum r

namespace CMP99SourceScaledStratification

variable {FineSite : Type u} [DecidableEq FineSite]
variable {n : ℕ} {ScaleSite : Fin n → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]

/-- The complete order-`r` field before restriction to `Lambda_r`. -/
abbrev ScaleField
    (g : Type w) (r : Fin n) :=
  PiLp 2 (fun _ : ScaleSite r => g)

/-- The field on the literal source stratum `Lambda_r`. -/
abbrev StratumField
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (g : Type w) (r : Fin n) :=
  PiLp 2 (fun _ : {x : ScaleSite r // x ∈ S.strata r} => g)

/-- Restriction of an order-`r` averaged field to the printed stratum
`Lambda_r`. -/
noncomputable def restrictStratumCLM
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) :
    ScaleField (ScaleSite := ScaleSite) g r →L[ℝ] S.StratumField g r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi =>
        WithLp.toLp 2 fun x : {x : ScaleSite r // x ∈ S.strata r} =>
          phi x.1
      map_add' := fun phi psi => by ext x; rfl
      map_smul' := fun a phi => by ext x; rfl }

@[simp] theorem restrictStratumCLM_apply
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) (phi : ScaleField (ScaleSite := ScaleSite) g r)
    (x : {x : ScaleSite r // x ∈ S.strata r}) :
    S.restrictStratumCLM r phi x = phi x.1 := rfl

/-- Zero extension from the printed stratum `Lambda_r` to its complete
order-`r` lattice.  This is the source-faithful right inverse of stratum
restriction. -/
noncomputable def extendStratumCLM
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) :
    S.StratumField g r →L[ℝ]
      ScaleField (ScaleSite := ScaleSite) g r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun xi =>
        WithLp.toLp 2 fun x : ScaleSite r =>
          if hx : x ∈ S.strata r then xi ⟨x, hx⟩ else 0
      map_add' := fun xi zeta => by
        ext x
        by_cases hx : x ∈ S.strata r <;> simp [hx]
      map_smul' := fun a xi => by
        ext x
        by_cases hx : x ∈ S.strata r <;> simp [hx] }

@[simp] theorem extendStratumCLM_apply_of_mem
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) (xi : S.StratumField g r) (x : ScaleSite r)
    (hx : x ∈ S.strata r) :
    S.extendStratumCLM r xi x = xi ⟨x, hx⟩ := by
  simp [extendStratumCLM, hx]

@[simp] theorem extendStratumCLM_apply_of_not_mem
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) (xi : S.StratumField g r) (x : ScaleSite r)
    (hx : x ∉ S.strata r) :
    S.extendStratumCLM r xi x = 0 := by
  simp [extendStratumCLM, hx]

/-- Restriction followed by zero extension is exactly the identity on the
physical stratum field. -/
theorem restrictStratumCLM_comp_extendStratumCLM
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) :
    (S.restrictStratumCLM r).comp (S.extendStratumCLM r) =
      ContinuousLinearMap.id ℝ (S.StratumField g r) := by
  apply ContinuousLinearMap.ext
  intro xi
  ext x
  simp [restrictStratumCLM, extendStratumCLM]

/-- Zero extension preserves the counting norm exactly. -/
theorem norm_extendStratumCLM_eq
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) (xi : S.StratumField g r) :
    ‖S.extendStratumCLM r xi‖ = ‖xi‖ := by
  have hsq : ‖S.extendStratumCLM r xi‖ ^ 2 = ‖xi‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    calc
      (∑ x : ScaleSite r, ‖S.extendStratumCLM r xi x‖ ^ 2) =
          ∑ x ∈ S.strata r, ‖S.extendStratumCLM r xi x‖ ^ 2 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ (S.strata r))
            intro x _hx hx
            simp [S.extendStratumCLM_apply_of_not_mem r xi x hx]
      _ = ∑ x : {x : ScaleSite r // x ∈ S.strata r},
          ‖S.extendStratumCLM r xi x.1‖ ^ 2 := by
            exact Finset.sum_subtype (S.strata r) (fun _ => Iff.rfl)
              (fun x => ‖S.extendStratumCLM r xi x‖ ^ 2)
      _ = ∑ x : {x : ScaleSite r // x ∈ S.strata r}, ‖xi x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _hx
            simp [S.extendStratumCLM_apply_of_mem r xi x.1 x.2]
  nlinarith [norm_nonneg (S.extendStratumCLM r xi), norm_nonneg xi]

/-- Exact Hilbert pairing between stratum restriction and zero extension. -/
theorem inner_restrictStratumCLM_eq_extendStratumCLM
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) (xi : S.StratumField g r)
    (phi : ScaleField (ScaleSite := ScaleSite) g r) :
    inner ℝ xi (S.restrictStratumCLM r phi) =
      inner ℝ (S.extendStratumCLM r xi) phi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  let f : ScaleSite r → ℝ := fun x =>
    if hx : x ∈ S.strata r then inner ℝ (xi ⟨x, hx⟩) (phi x) else 0
  calc
    (∑ x : {x : ScaleSite r // x ∈ S.strata r},
        inner ℝ (xi x) (phi x.1)) =
        ∑ x : {x : ScaleSite r // x ∈ S.strata r}, f x.1 := by
          apply Finset.sum_congr rfl
          intro x _hx
          simp [f, x.2]
    _ = ∑ x ∈ S.strata r, f x := by
          exact (Finset.sum_subtype (S.strata r) (fun _ => Iff.rfl) f).symm
    _ = ∑ x : ScaleSite r, f x := by
          apply Finset.sum_subset (Finset.subset_univ (S.strata r))
          intro x _hx hx
          simp [f, hx]
    _ = ∑ x : ScaleSite r,
        inner ℝ (S.extendStratumCLM r xi x) (phi x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hx : x ∈ S.strata r <;>
            simp [f, hx, extendStratumCLM]

/-- Zero extension is literally the counting-Hilbert adjoint of restriction.
No free adjoint or surjectivity certificate is needed. -/
theorem extendStratumCLM_eq_adjoint_restrictStratumCLM
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) :
    S.extendStratumCLM (g := g) r =
      (S.restrictStratumCLM (g := g) r).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff
    (S.extendStratumCLM (g := g) r)
    (S.restrictStratumCLM (g := g) r)]
  intro xi phi
  exact (S.inner_restrictStratumCLM_eq_extendStratumCLM r xi phi).symm

/-- The literal stratum restriction is a coisometry. -/
theorem restrictStratumCLM_comp_adjoint
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) :
    (S.restrictStratumCLM (g := g) r).comp
        (S.restrictStratumCLM (g := g) r).adjoint =
      ContinuousLinearMap.id ℝ (S.StratumField g r) := by
  rw [← S.extendStratumCLM_eq_adjoint_restrictStratumCLM (g := g) r]
  exact S.restrictStratumCLM_comp_extendStratumCLM (g := g) r

/-- The restriction norm is literally the sum over `y in Lambda_r`. -/
theorem norm_restrictStratumCLM_sq
    [∀ r, Fintype (ScaleSite r)]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (r : Fin n) (phi : ScaleField (ScaleSite := ScaleSite) g r) :
    ‖S.restrictStratumCLM r phi‖ ^ 2 =
      ∑ y ∈ S.strata r, ‖phi y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ y : {y : ScaleSite r // y ∈ S.strata r}, ‖phi y.1‖ ^ 2) =
    ∑ y ∈ S.strata r, ‖phi y‖ ^ 2
  exact (Finset.sum_subtype (S.strata r) (fun _ => Iff.rfl)
    (fun y => ‖phi y‖ ^ 2)).symm

/-- Counting-Hilbert representation of a stratified mass.  Each `Qprime r`
lands on its own lattice and is then restricted to the corresponding
`Lambda_r`.

The argument `weight` is the coefficient in the *counting* inner product.
For the printed source pairing at spacing `eta`, the physical coefficient
must first be divided by `eta^d`; this conversion is made explicitly in
`BalabanCMP99SourceMassWeights`. -/
noncomputable def sourceGaugeMass
    [∀ r, Fintype (ScaleSite r)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (Qprime : ∀ r, E →L[ℝ] ScaleField (ScaleSite := ScaleSite) g r)
    (weight : Fin n → ℝ) : E →L[ℝ] E :=
  cmp99SourceStratifiedGaugeMass
    (fun r => ScaleField (ScaleSite := ScaleSite) g r)
    (fun r => S.StratumField g r)
    Qprime (fun r => S.restrictStratumCLM r) weight

/-- Exact counting-Hilbert quadratic form, before converting to the printed
spacing-weighted source pairing. -/
theorem inner_sourceGaugeMass
    [∀ r, Fintype (ScaleSite r)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {g : Type w} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (S : CMP99SourceScaledStratification FineSite n ScaleSite)
    (Qprime : ∀ r, E →L[ℝ] ScaleField (ScaleSite := ScaleSite) g r)
    (weight : Fin n → ℝ) (phi : E) :
    inner ℝ phi (S.sourceGaugeMass Qprime weight phi) =
      ∑ r : Fin n,
        weight r * ∑ y ∈ S.strata r, ‖Qprime r phi y‖ ^ 2 := by
  rw [sourceGaugeMass, inner_cmp99SourceStratifiedGaugeMass]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [S.norm_restrictStratumCLM_sq]

end CMP99SourceScaledStratification

end

end YangMills.RG
