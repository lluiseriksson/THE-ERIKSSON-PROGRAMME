/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionInverseUniqueness
import YangMills.RG.BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionary
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary

/-!
# Source-separated generated Step-7b carrier

This is Step 8b.24/S2a.  It exposes the exact physical factorization

```text
fine block side = L^(depth+1)
coarse side     = 2*(K*Q)
```

and relates it to the already sealed source-separated ambient carrier
`(K*L^(depth+1))*(2*Q)` by composing the generated one-block coordinate map
with the source-separated full-site equivalence.  No diagonal `K=L` cast is
used.

The final equality between the complexified physical precision and the
transported Step-7b precision belongs to S2b, after S1 is promoted.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Full generated active carrier in the exact separated Step-7b
coordinates. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := L)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q)
          (depth + 1)) ≃
      FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) where
  toFun target :=
    cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) L (2 * (K * Q)) (depth + 1) target.1
  invFun x :=
    ⟨(cmp99GeneratedFineBoxOneBlockEquiv
        (d := 4) L (2 * (K * Q)) (depth + 1)).symm x, by
      rw [cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion,
        cmp99IteratedLiftActiveRegion_full_sites_eq_univ]
      exact Finset.mem_univ _⟩
  left_inv target := by
    apply Subtype.ext
    exact (cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) L (2 * (K * Q)) (depth + 1)).symm_apply_apply target.1
  right_inv x :=
    (cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) L (2 * (K * Q)) (depth + 1)).apply_symm_apply x

/-- Exact source-separated ambient-to-Step-7b carrier equivalence.  Its two
legs retain the ambient and Fourier factorizations explicitly. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) ≃
      FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) :=
  (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
      L K Q depth).symm.trans
    (cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv
      L K Q depth)

/-- Continuous complex coordinate transport along the exact separated
Step-7b carrier equivalence. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv
    (L K Q Nc depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc) ≃L[ℂ]
    (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
      SUNLieComplexCoord Nc) :=
  ContinuousLinearEquiv.piCongrLeft ℂ
    (fun _ : FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) =>
      SUNLieComplexCoord Nc)
    (cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth)

/-- The source-pinned active field obtained by pulling an ambient real field
back through the source-separated full-site equivalence. -/
noncomputable def cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient
    (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    CMP99SourceGeneratedTerminalComplexFieldData
      (M := L) (Nc := Nc)
      (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth :=
  CMP99SourceGeneratedTerminalComplexFieldData.ofActiveField
    (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
        L K Q depth).symm).toContinuousLinearEquiv phi)

omit [NeZero Nc] in
/-- The canonical zero extension of the pulled-back active field is ordinary
coordinate transport followed by the physical fibre complexification. -/
theorem
    cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient_complexZeroExtension
    (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    (cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth phi
      ).complexZeroExtension =
      cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv
        L K Q Nc depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) := by
  classical
  let Omega := cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q
  let region := cmp99IteratedLiftActiveRegion (M := L) Omega (depth + 1)
  let eActive :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bActiveSiteEquiv L K Q depth
  let eFull :=
    cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let D := cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient
    (L := L) (K := K) (Q := Q) (Nc := Nc) depth phi
  funext y
  let target : ActiveGaugeRegion.Site region := eActive.symm y
  have hx : target.1 ∈ region.sites := target.2
  have hpoint :=
    D.complexZeroExtension_apply_eq_complexification_realZeroExtension target.1
  have hbox : cmp99GeneratedFineBoxOneBlockEquiv
      (d := 4) L (2 * (K * Q)) (depth + 1) target.1 = y := by
    exact eActive.apply_symm_apply y
  rw [hbox] at hpoint
  rw [hpoint]
  rw [CMP99SourceGeneratedTerminalComplexFieldData.realZeroExtension,
    extendZeroZeroCLM_apply_of_mem region D.activeField target.1 hx]
  have hactive : D.activeField target = phi (eFull target) := by
    change
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
          eFull.symm phi) target = phi (eFull target)
    rw [LinearIsometryEquiv.piLpCongrLeft_apply]
    rfl
  have hy : y =
      cmp99SourceSeparatedGeneratedPhysicalStep7bSiteEquiv L K Q depth
        (eFull target) := by
    change y = eActive (eFull.symm (eFull (eActive.symm y)))
    rw [eFull.symm_apply_apply, eActive.apply_symm_apply]
  rw [hactive, hy]
  simp [cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv,
    ContinuousLinearEquiv.piCongrLeft,
    Homeomorph.piCongrLeft, Equiv.piCongrLeft]

/-- Literal Step-7b full-box precision with the independent source
factorization fixed before transport. -/
noncomputable def
    cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
    (depth : ℕ) :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc) →L[ℂ]
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc) :=
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  let spacing := cmp99SourceGeneratedFullComplexSpacing L (depth + 1)
  let a := cmp99SourceGeneratedFullComplexA 4 L (depth + 1) spacing 0
  U.symm.toContinuousLinearMap.comp
    ((cmp99SourceFlatFullComplexPrecisionCLM
      (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (Nc := Nc) 0 a).comp U.toContinuousLinearMap)

end

end YangMills.RG
