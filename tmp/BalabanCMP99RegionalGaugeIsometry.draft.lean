/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ContourHolonomy

/-!
# PRE-VALIDATION: regional gauge isometries for CMP99 Corollary 3.6

Source is present only in scratch.  No `.olean` has been materialized and no
declaration in this file has yet been verified by the Lean compiler.

This is the algebraic C6c.8a prefix.  It packages the already-defined adjoint
gauge actions as literal `PiLp` linear isometric equivalences.  It assumes no
operator covariance and proves only application, inverse, norm/support, and
regional restriction/zero-extension identities.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d Nc : ℕ}
variable [NeZero d] [NeZero Nc]

section Fine

variable {N : ℕ} [NeZero N]

/-- Ambient pointwise adjoint gauge action, bundled as a real linear isometry. -/
noncomputable def cmp99FineGaugeLinearIsometryEquiv
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc)) :
    GaugeZeroCochain d N (SUNLieCoord Nc) ≃ₗᵢ[ℝ]
      GaugeZeroCochain d N (SUNLieCoord Nc) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun x =>
    rho.adLinearIsometryEquiv (u x)

@[simp] theorem cmp99FineGaugeLinearIsometryEquiv_apply
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : GaugeZeroCochain d N (SUNLieCoord Nc))
    (x : FinBox d N) :
    cmp99FineGaugeLinearIsometryEquiv rho u phi x =
      rho.adCLM (u x) (phi x) := rfl

/-- The regional fine action is the dependent `PiLp` lift of the physical
adjoint isometry at every active site. -/
noncomputable def cmp99RegionalFineGaugeLinearIsometryEquiv
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc)) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) ≃ₗᵢ[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun x =>
    rho.adLinearIsometryEquiv (u x.1)

omit [NeZero d] in
@[simp] theorem cmp99RegionalFineGaugeLinearIsometryEquiv_apply
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u phi x =
      rho.adCLM (u x.1) (phi x) := rfl

omit [NeZero d] in
theorem cmp99RegionalFineGaugeLinearIsometryEquiv_eq_gaugeAct
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u phi =
      cmp99RegionalFineGaugeAct Omega rho u phi := rfl

omit [NeZero d] in
@[simp] theorem cmp99RegionalFineGaugeLinearIsometryEquiv_symm_apply
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u).symm phi x =
      rho.adCLM (u x.1)⁻¹ (phi x) := rfl

omit [NeZero d] in
theorem norm_cmp99RegionalFineGaugeAct_eq
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖cmp99RegionalFineGaugeAct Omega rho u phi‖ = ‖phi‖ := by
  rw [← cmp99RegionalFineGaugeLinearIsometryEquiv_eq_gaugeAct]
  exact LinearIsometryEquiv.norm_map _ _

omit [NeZero d] in
theorem support_cmp99RegionalFineGaugeAct_eq
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    Function.support (cmp99RegionalFineGaugeAct Omega rho u phi) =
      Function.support phi := by
  ext x
  simp only [Function.mem_support, cmp99RegionalFineGaugeAct_apply]
  exact (rho.adLinearIsometryEquiv (u x.1)).map_eq_zero_iff.not

/-- Zero extension commutes with the regional fine gauge action.  No support
hypothesis is needed: both sides vanish off the active carrier. -/
theorem extendZeroZeroCLM_cmp99RegionalFineGaugeAct
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    extendZeroZeroCLM Omega (cmp99RegionalFineGaugeAct Omega rho u phi) =
      cmp99FineGaugeLinearIsometryEquiv rho u (extendZeroZeroCLM Omega phi) := by
  apply PiLp.ext
  intro x
  by_cases hx : x ∈ Omega.sites <;>
    simp [extendZeroZeroCLM, hx]

/-- Restriction commutes with the ambient pointwise gauge isometry. -/
theorem restrictZeroCLM_cmp99FineGaugeLinearIsometryEquiv
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (phi : GaugeZeroCochain d N (SUNLieCoord Nc)) :
    restrictZeroCLM Omega (cmp99FineGaugeLinearIsometryEquiv rho u phi) =
      cmp99RegionalFineGaugeAct Omega rho u (restrictZeroCLM Omega phi) := by
  apply PiLp.ext
  intro x
  rfl

end Fine

section Coarse

variable {M N' : ℕ} [NeZero M] [NeZero N']

/-- The induced coarse action is the dependent `PiLp` lift of the adjoint
isometry at each canonical fine block basepoint. -/
noncomputable def cmp99RegionalCoarseGaugeLinearIsometryEquiv
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc)) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieCoord Nc) ≃ₗᵢ[ℝ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (SUNLieCoord Nc) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun y =>
    rho.adLinearIsometryEquiv (u (blockBasepoint M N' y.1))

omit [NeZero d] in
@[simp] theorem cmp99RegionalCoarseGaugeLinearIsometryEquiv_apply
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    cmp99RegionalCoarseGaugeLinearIsometryEquiv Omega rho u eta y =
      rho.adCLM (u (blockBasepoint M N' y.1)) (eta y) := rfl

omit [NeZero d] in
theorem cmp99RegionalCoarseGaugeLinearIsometryEquiv_eq_gaugeAct
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    cmp99RegionalCoarseGaugeLinearIsometryEquiv Omega rho u eta =
      cmp99RegionalCoarseGaugeAct Omega rho u eta := rfl

omit [NeZero d] in
@[simp] theorem cmp99RegionalCoarseGaugeLinearIsometryEquiv_symm_apply
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)) :
    (cmp99RegionalCoarseGaugeLinearIsometryEquiv Omega rho u).symm eta y =
      rho.adCLM (u (blockBasepoint M N' y.1))⁻¹ (eta y) := rfl

omit [NeZero d] in
theorem norm_cmp99RegionalCoarseGaugeAct_eq
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    ‖cmp99RegionalCoarseGaugeAct Omega rho u eta‖ = ‖eta‖ := by
  rw [← cmp99RegionalCoarseGaugeLinearIsometryEquiv_eq_gaugeAct]
  exact LinearIsometryEquiv.norm_map _ _

omit [NeZero d] in
theorem support_cmp99RegionalCoarseGaugeAct_eq
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    Function.support (cmp99RegionalCoarseGaugeAct Omega rho u eta) =
      Function.support eta := by
  ext y
  simp only [Function.mem_support, cmp99RegionalCoarseGaugeAct_apply]
  exact
    (rho.adLinearIsometryEquiv
      (u (blockBasepoint M N' y.1))).map_eq_zero_iff.not

/-- The coarse action of one scale is definitionally the fine action on the
coarse region for the restricted gauge transform.  Naming the equality keeps
the recursive retained-tower proof from relying on an implicit convention. -/
theorem cmp99RegionalCoarseGaugeLinearIsometryEquiv_eq_fine_coarseTransform
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d (M * N') (SUN Nc)) :
    cmp99RegionalCoarseGaugeLinearIsometryEquiv Omega rho u =
      cmp99RegionalFineGaugeLinearIsometryEquiv
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) rho
        (coarseTransform u) := rfl

end Coarse

end

end YangMills.RG
