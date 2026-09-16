/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99RegionalGaugeIsometry
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision

/-!
# PRE-VALIDATION: ambient CMP99 covariant-D0 gauge intertwiner

Source is present only in scratch.  No `.olean` has been materialized and no
declaration in this file has yet been verified by the Lean compiler.

This is the ambient algebraic prefix of C6c.8b.  The positive-bond action is
fixed at the source vertex, matching the orientation of the literal
`covariantD0CLM`.  Covariance is derived from `GaugeConfig.gaugeAct`; it is not
accepted as a field or an equality between caller-selected operators.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

section IsometricIntertwinerAlgebra

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Taking adjoints reverses an intertwiner between two linear isometries. -/
theorem continuousLinearMap_adjoint_intertwines_of_isometries
    (T T' : E →L[ℝ] F)
    (eE : E ≃ₗᵢ[ℝ] E) (eF : F ≃ₗᵢ[ℝ] F)
    (h : T'.comp (eE : E →L[ℝ] E) =
      (eF : F →L[ℝ] F).comp T) :
    T'.adjoint.comp (eF : F →L[ℝ] F) =
      (eE : E →L[ℝ] E).comp T.adjoint := by
  have hadj :
      (eE.symm : E →L[ℝ] E).comp T'.adjoint =
        T.adjoint.comp (eF.symm : F →L[ℝ] F) := by
    simpa only [ContinuousLinearMap.adjoint_comp,
      LinearIsometryEquiv.adjoint_eq_symm] using
      congrArg (fun S : E →L[ℝ] F => S.adjoint) h
  calc
    T'.adjoint.comp (eF : F →L[ℝ] F) =
        ((eE : E →L[ℝ] E).comp (eE.symm : E →L[ℝ] E)).comp
          (T'.adjoint.comp (eF : F →L[ℝ] F)) := by simp
    _ = (eE : E →L[ℝ] E).comp
          (((eE.symm : E →L[ℝ] E).comp T'.adjoint).comp
            (eF : F →L[ℝ] F)) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = (eE : E →L[ℝ] E).comp
          ((T.adjoint.comp (eF.symm : F →L[ℝ] F)).comp
            (eF : F →L[ℝ] F)) := by rw [hadj]
    _ = (eE : E →L[ℝ] E).comp T.adjoint := by
        simp only [ContinuousLinearMap.comp_assoc,
          ContinuousLinearEquiv.coe_symm_comp_coe,
          ContinuousLinearMap.comp_id]

/-- Consequently `T†T` intertwines under the source isometry whenever `T`
intertwines under source and target isometries. -/
theorem continuousLinearMap_adjoint_comp_self_intertwines_of_isometries
    (T T' : E →L[ℝ] F)
    (eE : E ≃ₗᵢ[ℝ] E) (eF : F ≃ₗᵢ[ℝ] F)
    (h : T'.comp (eE : E →L[ℝ] E) =
      (eF : F →L[ℝ] F).comp T) :
    (T'.adjoint.comp T').comp (eE : E →L[ℝ] E) =
      (eE : E →L[ℝ] E).comp (T.adjoint.comp T) := by
  have hadj := continuousLinearMap_adjoint_intertwines_of_isometries
    T T' eE eF h
  calc
    (T'.adjoint.comp T').comp (eE : E →L[ℝ] E) =
        T'.adjoint.comp (T'.comp (eE : E →L[ℝ] E)) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = T'.adjoint.comp ((eF : F →L[ℝ] F).comp T) := by rw [h]
    _ = (T'.adjoint.comp (eF : F →L[ℝ] F)).comp T := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = ((eE : E →L[ℝ] E).comp T.adjoint).comp T := by rw [hadj]
    _ = (eE : E →L[ℝ] E).comp (T.adjoint.comp T) := by
      rw [ContinuousLinearMap.comp_assoc]

/-- Strict coercivity transports backwards through an exact isometric
intertwiner.  This is the algebraic step that constructs the regular-side
Green from coercivity of its small gauge representative. -/
theorem isCoerciveCLM_of_intertwines_linearIsometryEquiv
    (A A' : E →L[ℝ] E) (e : E ≃ₗᵢ[ℝ] E) {c : ℝ}
    (hintertwines : A'.comp (e : E →L[ℝ] E) =
      (e : E →L[ℝ] E).comp A)
    (hA' : IsCoerciveCLM A' c) :
    IsCoerciveCLM A c := by
  intro x
  have h := hA' (e x)
  have happ := congrArg (fun T : E →L[ℝ] E => T x) hintertwines
  change A' (e x) = e (A x) at happ
  rw [e.norm_map, happ, ← e.inner_map_map] at h
  exact h

end IsometricIntertwinerAlgebra

/-- Pointwise adjoint action on positive physical bonds, based at the source
vertex of the oriented positive representative. -/
noncomputable def cmp99PhysicalBondGaugeLinearIsometryEquiv
    (rho : SUNAdjointModel Nc) (u : GaugeTransform d N (SUN Nc)) :
    PhysicalGaugeOneCochain d N Nc ≃ₗᵢ[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  LinearIsometryEquiv.piLpCongrRight 2 fun b =>
    rho.adLinearIsometryEquiv (u b.1)

@[simp] theorem cmp99PhysicalBondGaugeLinearIsometryEquiv_apply
    (rho : SUNAdjointModel Nc) (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N) :
    cmp99PhysicalBondGaugeLinearIsometryEquiv rho u A b =
      rho.adCLM (u b.1) (A b) := rfl

@[simp] theorem cmp99PhysicalBondGaugeLinearIsometryEquiv_symm_apply
    (rho : SUNAdjointModel Nc) (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N) :
    (cmp99PhysicalBondGaugeLinearIsometryEquiv rho u).symm A b =
      rho.adCLM (u b.1)⁻¹ (A b) := rfl

theorem norm_cmp99PhysicalBondGaugeLinearIsometryEquiv_apply
    (rho : SUNAdjointModel Nc) (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) :
    ‖cmp99PhysicalBondGaugeLinearIsometryEquiv rho u A‖ = ‖A‖ :=
  LinearIsometryEquiv.norm_map _ _

theorem support_cmp99PhysicalBondGaugeLinearIsometryEquiv_apply
    (rho : SUNAdjointModel Nc) (u : GaugeTransform d N (SUN Nc))
    (A : PhysicalGaugeOneCochain d N Nc) :
    Function.support (cmp99PhysicalBondGaugeLinearIsometryEquiv rho u A) =
      Function.support A := by
  ext b
  simp only [Function.mem_support,
    cmp99PhysicalBondGaugeLinearIsometryEquiv_apply]
  exact (rho.adLinearIsometryEquiv (u b.1)).map_eq_zero_iff.not

/-- Literal ambient form of CMP99 (3.31) at the covariant-gradient level.
The bond action is source-based and no operator covariance is assumed. -/
theorem covariantD0CLM_gaugeAct
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (U : PhysicalGaugeBackground d N Nc)
    (phi : PhysicalGaugeZeroCochain d N Nc) :
    covariantD0CLM rho (GaugeConfig.gaugeAct u U)
        (cmp99FineGaugeLinearIsometryEquiv rho u phi) =
      cmp99PhysicalBondGaugeLinearIsometryEquiv rho u
        (covariantD0CLM rho U phi) := by
  apply PiLp.ext
  intro b
  rcases b with ⟨x, i⟩
  simp only [covariantD0CLM_apply,
    cmp99FineGaugeLinearIsometryEquiv_apply,
    cmp99PhysicalBondGaugeLinearIsometryEquiv_apply,
    GaugeConfig.gaugeAct_apply, finBoxGeometry_src, finBoxGeometry_dst,
    srcV_mk_pos, dstV_mk_pos]
  rw [rho.ad_mul, rho.ad_mul]
  simp only [ContinuousLinearMap.comp_apply, rho.ad_inv_apply_ad,
    ContinuousLinearMap.map_sub]

/-- Global-gauge covariance of the literal scaled regional derivative.  This
uses only zero-extension covariance and the ambient `D0` intertwiner.  The
separate locality/collar obligation enters later, when a gauge witness known
only on the CMP99 regular cube is extended to such a global `u`. -/
theorem cmp99ActiveRegionSourceCovariantD0CLM_gaugeAct
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99ActiveRegionSourceCovariantD0CLM Omega rho
        (GaugeConfig.gaugeAct u U) spacing
        (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u phi) =
      cmp99PhysicalBondGaugeLinearIsometryEquiv rho u
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing phi) := by
  unfold cmp99ActiveRegionSourceCovariantD0CLM
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [cmp99RegionalFineGaugeLinearIsometryEquiv_eq_gaugeAct,
    extendZeroZeroCLM_cmp99RegionalFineGaugeAct,
    covariantD0CLM_gaugeAct, map_smul]

/-- Operator form of the regional `D0` intertwiner, used to transport its
adjoint without inserting a covariance hypothesis. -/
theorem cmp99ActiveRegionSourceCovariantD0CLM_comp_gaugeIsometry
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    (cmp99ActiveRegionSourceCovariantD0CLM Omega rho
      (GaugeConfig.gaugeAct u U) spacing).comp
        (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u :
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) =
      (cmp99PhysicalBondGaugeLinearIsometryEquiv rho u :
        PhysicalGaugeOneCochain d N Nc →L[ℝ]
          PhysicalGaugeOneCochain d N Nc).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing) := by
  apply ContinuousLinearMap.ext
  intro phi
  exact cmp99ActiveRegionSourceCovariantD0CLM_gaugeAct
    Omega rho u U spacing phi

/-- Literal regional Laplacian covariance derived from the `D0` intertwiner
and the adjoints of the two physical gauge isometries. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_gaugeAct
    (Omega : ActiveGaugeRegion d N)
    (rho : SUNAdjointModel Nc)
    (u : GaugeTransform d N (SUN Nc))
    (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho
        (GaugeConfig.gaugeAct u U) spacing
        (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u phi) =
      cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u
        (cmp99ActiveRegionSourceCovariantLaplacian
          Omega rho U spacing phi) := by
  let D := cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing
  let D' := cmp99ActiveRegionSourceCovariantD0CLM Omega rho
    (GaugeConfig.gaugeAct u U) spacing
  let eE := cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u
  let eF := cmp99PhysicalBondGaugeLinearIsometryEquiv rho u
  have hD : D'.comp (eE : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) =
      (eF : PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc).comp D := by
    exact cmp99ActiveRegionSourceCovariantD0CLM_comp_gaugeIsometry
      Omega rho u U spacing
  have hL := continuousLinearMap_adjoint_comp_self_intertwines_of_isometries
    D D' eE eF hD
  exact congrArg
    (fun T : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) => T phi) hL

end

end YangMills.RG
