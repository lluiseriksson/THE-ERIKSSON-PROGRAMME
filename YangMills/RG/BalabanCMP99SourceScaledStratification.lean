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

/-- The source-typed mass in (3.24).  Each `Qprime r` lands on its own lattice
and is then restricted to the corresponding `Lambda_r`. -/
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

/-- Exact source formula (3.24), before substituting the printed coefficient
`a_r (L^r eta)^(d-2)` for `weight r`. -/
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
