/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionInverseUniqueness
import YangMills.RG.BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalAmbientGreenComplexification

/-!
# PRE-VALIDATION: generated ambient precision dictionary

This source is present, but its `.olean` has not yet been materialized and its
declarations have not yet been verified by the Lean compiler.

The generated real precision has already been transported to the one ambient
carrier used by the regional construction and canonically complexified there.
This file identifies that operator with the literal Step-7b full-box complex
precision.  The carrier map is not inferred from equality of cardinalities:
it is the composite of the sealed full-site equivalence and the exact
one-block coordinate map used by Step 7b.

No inverse or Green operator is accepted as input, and no stabilized field or
terminal contraction is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- The full generated active carrier in the exact one-block coordinates used
by Step 7b.  The coarse side remains `2 * (M * Q)`; it is not replaced by the
arithmetically equal but physically different factorization with coarse side
`2 * Q`. -/
noncomputable def cmp99SourceGeneratedPhysicalStep7bActiveSiteEquiv
    (M Q depth : ℕ) [NeZero M] [NeZero Q] :
    ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M)
          (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) (depth + 1)) ≃
      FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) where
  toFun target :=
    cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) M (2 * (M * Q)) (depth + 1) target.1
  invFun x :=
    ⟨(cmp99GeneratedFineBoxOneBlockEquiv
        (d := 4) M (2 * (M * Q)) (depth + 1)).symm x, by
      rw [cmp99SourceGeneratedPhysicalFullCoarseRegion,
        cmp99IteratedLiftActiveRegion_full_sites_eq_univ]
      exact Finset.mem_univ _⟩
  left_inv target := by
    apply Subtype.ext
    exact (cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) M (2 * (M * Q)) (depth + 1)).symm_apply_apply target.1
  right_inv x :=
    (cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) M (2 * (M * Q)) (depth + 1)).apply_symm_apply x

/-- Exact ambient-to-Step-7b carrier equivalence.  Its first leg is the
sealed physical full-site equivalence; its second leg retains the Step-7b
block/coarse factorization. -/
noncomputable def cmp99SourceGeneratedPhysicalStep7bSiteEquiv
    (M Q depth : ℕ) [NeZero M] [NeZero Q] :
    FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) ≃
      FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) :=
  (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth).symm.trans
    (cmp99SourceGeneratedPhysicalStep7bActiveSiteEquiv M Q depth)

/-- Continuous complex coordinate transport along the exact Step-7b carrier
equivalence. -/
noncomputable def cmp99SourceGeneratedPhysicalStep7bFieldEquiv
    (M Q Nc depth : ℕ) [NeZero M] [NeZero Q] :
    (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        SUNLieComplexCoord Nc) ≃L[ℂ]
      (FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) →
        SUNLieComplexCoord Nc) :=
  ContinuousLinearEquiv.piCongrLeft ℂ
    (fun _ : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))) =>
      SUNLieComplexCoord Nc)
    (cmp99SourceGeneratedPhysicalStep7bSiteEquiv M Q depth)

/-- The source-pinned active field obtained by pulling an ambient real field
back through the already sealed full-site equivalence. -/
noncomputable def cmp99SourceGeneratedPhysicalTerminalDataOfAmbient
    (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
      (SUNLieCoord Nc)) :
    CMP99SourceGeneratedTerminalComplexFieldData
      (M := M) (Nc := Nc)
      (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth :=
  CMP99SourceGeneratedTerminalComplexFieldData.ofActiveField
    (cmp99SourceGeneratedPhysicalFullCoarseRegion M Q) depth
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth).symm
      ).toContinuousLinearEquiv phi)

/-- The canonical complex zero extension of the pulled-back active field is
exactly ordinary coordinate transport of the ambient real field followed by
the physical fibre complexification. -/
theorem cmp99SourceGeneratedPhysicalTerminalDataOfAmbient_complexZeroExtension
    (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
      (SUNLieCoord Nc)) :
    (cmp99SourceGeneratedPhysicalTerminalDataOfAmbient
        (M := M) (Q := Q) (Nc := Nc) depth phi).complexZeroExtension =
      cmp99SourceGeneratedPhysicalStep7bFieldEquiv M Q Nc depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) := by
  classical
  let Omega := cmp99SourceGeneratedPhysicalFullCoarseRegion M Q
  let region := cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)
  let eActive := cmp99SourceGeneratedPhysicalStep7bActiveSiteEquiv M Q depth
  let eFull := cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth
  let D := cmp99SourceGeneratedPhysicalTerminalDataOfAmbient
    (M := M) (Q := Q) (Nc := Nc) depth phi
  funext y
  let target : ActiveGaugeRegion.Site region := eActive.symm y
  have hx : target.1 ∈ region.sites := target.2
  have hpoint :=
    D.complexZeroExtension_apply_eq_complexification_realZeroExtension target.1
  have hbox : cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) M (2 * (M * Q)) (depth + 1) target.1 = y := by
    exact eActive.apply_symm_apply y
  rw [hbox] at hpoint
  rw [hpoint]
  rw [CMP99SourceGeneratedTerminalComplexFieldData.realZeroExtension,
    extendZeroZeroCLM_apply_of_mem region D.activeField target.1 hx]
  have hactive : D.activeField target = phi (eFull target) := by
    simp [D, cmp99SourceGeneratedPhysicalTerminalDataOfAmbient,
      CMP99SourceGeneratedTerminalComplexFieldData.ofActiveField,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have hy : y =
      cmp99SourceGeneratedPhysicalStep7bSiteEquiv M Q depth
        (eFull target) := by
    change y = eActive (eFull.symm (eFull (eActive.symm y)))
    rw [eFull.symm_apply_apply, eActive.apply_symm_apply]
  rw [hactive, hy]
  simp [cmp99SourceGeneratedPhysicalStep7bFieldEquiv,
    ContinuousLinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft,
    Homeomorph.piCongrLeft, Equiv.piCongrLeft]

/-- Literal Step-7b full-box precision, transported only after its physical
block/coarse factorization has been fixed. -/
noncomputable def cmp99SourceGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
    (depth : ℕ) :
    (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox 4 (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q)) →
        SUNLieComplexCoord Nc) :=
  let U := cmp99SourceGeneratedPhysicalStep7bFieldEquiv M Q Nc depth
  let spacing := cmp99SourceGeneratedFullComplexSpacing M (depth + 1)
  let a := cmp99SourceGeneratedFullComplexA 4 M (depth + 1) spacing 0
  U.symm.toContinuousLinearMap.comp
    ((cmp99SourceFlatFullComplexPrecisionCLM
      (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
      (Nc := Nc) 0 a).comp U.toContinuousLinearMap)

/-- The complexified ambient precision agrees with the transported literal
Step-7b precision on every ambient real field. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex_apply_ofReal
    (hM : 2 ≤ M) (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
        (M := M) (Q := Q) (Nc := Nc) hM depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
      cmp99SourceGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (M := M) (Q := Q) (Nc := Nc) depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) := by
  classical
  let D := cmp99SourceGeneratedPhysicalTerminalDataOfAmbient
    (M := M) (Q := Q) (Nc := Nc) depth phi
  let eFull := cmp99SourceGeneratedPhysicalFullSiteEquiv M Q depth
  let U := cmp99SourceGeneratedPhysicalStep7bFieldEquiv M Q Nc depth
  have hfield : D.complexZeroExtension =
      U (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) :=
    cmp99SourceGeneratedPhysicalTerminalDataOfAmbient_complexZeroExtension
      (M := M) (Q := Q) (Nc := Nc) depth phi
  have hambient :
      cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
          (M := M) (Q := Q) (Nc := Nc) hM depth
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
        fun x => cmp99SUNLieCoordComplexificationLM Nc
          (cmp99SourceGeneratedFlatPhysicalAmbientPrecision
            (M := M) (Q := Q) (Nc := Nc) hM depth phi x) := by
    funext y
    ext a
    simp [cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex,
      finitePiLpCanonicalComplexificationOuterCLM,
      finitePiLpCanonicalComplexificationCLM_apply,
      finitePiLpComplexRealPart, finitePiLpComplexImagPart,
      finitePiLpComplexOfReal, finitePiLpComplexOuterEquiv]
  apply funext
  intro x
  rw [congrFun hambient x]
  have hphysical := D.physicalPrecision_complexification_eq_fullComplexAction
    (eFull.symm x)
  rw [hfield] at hphysical
  simpa [cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex,
    cmp99SourceGeneratedFlatPhysicalAmbientPrecision,
    cmp99SourceGeneratedPhysicalAmbientPrecision,
    cmp99SourceGeneratedPhysicalTerminalDataOfAmbient,
    cmp99SourceGeneratedFlatPhysicalStep7bAmbientPrecisionCLM,
    finitePiLpCanonicalComplexificationOuterCLM,
    finitePiLpCanonicalComplexificationCLM_apply,
    finitePiLpComplexRealPart, finitePiLpComplexImagPart,
    finitePiLpComplexOfReal, U, eFull] using hphysical

/-- Exact Step-7b physical dictionary on the ambient carrier.  The operator
equality follows from the pointwise source dictionary and complex linearity;
no independent complex precision equality is supplied by the caller. -/
theorem cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex_eq_step7b
    (hM : 2 ≤ M) (depth : ℕ) :
    cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex
        (M := M) (Q := Q) (Nc := Nc) hM depth =
      cmp99SourceGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (M := M) (Q := Q) (Nc := Nc) depth := by
  apply ContinuousLinearMap.ext
  intro z
  let xr : GaugeZeroCochain 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
      (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun x => WithLp.toLp 2 fun a => (z x a).re
  let xi : GaugeZeroCochain 4
      (cmp99SourceRegionalLargeBlockSide M depth * (2 * Q))
      (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun x => WithLp.toLp 2 fun a => (z x a).im
  have hz : z =
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (xr x)) +
        Complex.I •
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (xi x)) := by
    funext x
    ext a
    simpa [xr, xi, mul_comm] using (Complex.re_add_im (z x a)).symm
  rw [hz, map_add, map_add, map_smul, map_smul]
  rw [cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex_apply_ofReal
      (M := M) (Q := Q) (Nc := Nc) hM depth xr,
    cmp99SourceGeneratedFlatPhysicalAmbientPrecisionComplex_apply_ofReal
      (M := M) (Q := Q) (Nc := Nc) hM depth xi]

end

end YangMills.RG
