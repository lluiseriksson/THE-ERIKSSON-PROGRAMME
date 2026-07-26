/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98PhysicalUbarLieCoordinate
import YangMills.RG.BalabanCMP98Eq122NonlinearLogJet

/-!
# The literal nonlinear CMP98 block is special unitary

CMP98 (118) multiplies the exponential of the local logarithmic average by
the straight coarse contour.  Both factors are physically special unitary.
This file packages their product in `SU(N)` and proves that its underlying
matrix is exactly the nonlinear block curve already used by the ambient
calculus.

The construction consumes only the near-identity and no-winding budgets
required to put the averaged logarithm in `su(N)`.  It does not yet normalize
the block at the background or form the CMP102 correction.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The special-unitary exponential of the literal CMP98 logarithmic block
average along a physical line. -/
noncomputable def cmp98PhysicalUbarFactor
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SUN Nc :=
  cmp99UbarSpecialUnitaryFactorOfNearIdentity
    (blockOf M N' b.1)
    (fun _ => ((M : ℝ) ^ d)⁻¹)
    (fun x => cmp98PhysicalUbarRelativeSUN U A b x t)
    hnear hnoWinding

/-- The preceding special-unitary factor has exactly the ambient matrix
`exp(cmp98UbarLogAverage ...)`. -/
theorem cmp98PhysicalUbarFactor_coe
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    (cmp98PhysicalUbarFactor U A b t hnear hnoWinding :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) := by
  unfold cmp98PhysicalUbarFactor cmp98UbarExpAverage
  rw [cmp99UbarSpecialUnitaryFactorOfNearIdentity_coe]
  rw [← cmp98UbarLogAverage_physicalLine_eq_specialUnitaryExponent]

/-- The literal represented block of CMP98 (118), now retained in `SU(N)`. -/
noncomputable def cmp98PhysicalNonlinearBlockSUN
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SUN Nc :=
  cmp98PhysicalUbarFactor U A b t hnear hnoWinding *
    wilsonLine (cmp98PhysicalSuLeftVariation U A t)
      (cmp98SourceCoarseBondPath (Nc := Nc) b)

/-- Forgetting the determinant certificate recovers exactly the ambient
nonlinear block curve used in equations (118)--(125). -/
theorem cmp98PhysicalNonlinearBlockSUN_coe
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    (cmp98PhysicalNonlinearBlockSUN U A b t hnear hnoWinding :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      cmp98Eq119NonlinearBlockCurve U A b t := by
  unfold cmp98PhysicalNonlinearBlockSUN cmp98Eq119NonlinearBlockCurve
  change
    (cmp98PhysicalUbarFactor U A b t hnear hnoWinding :
        Matrix (Fin Nc) (Fin Nc) ℂ) *
      ((wilsonLine (cmp98PhysicalSuLeftVariation U A t)
        (cmp98SourceCoarseBondPath (Nc := Nc) b) : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
    cmp98UbarExpAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) *
      cmp98ContourMatrixCurve U A
        (cmp98SourceCoarseBondPath (Nc := Nc) b) t
  rw [cmp98PhysicalUbarFactor_coe]
  rw [← cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve]
  rw [cmp98AmbientWilsonLineMatrix_line_eq_specialUnitaryWilsonLine]

/-- The physical nonlinear block normalized on the right by its exact
background value, entirely inside `SU(N)`. -/
noncomputable def cmp98PhysicalNonlinearRelativeSUN
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hnear0 : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding0 : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SUN Nc :=
  cmp98PhysicalNonlinearBlockSUN U A b t hnear hnoWinding *
    (cmp98PhysicalNonlinearBlockSUN
      U A b 0 hnear0 hnoWinding0)⁻¹

/-- The group inverse of the physical background block is the exact
two-factor inverse already used by the ambient right trivialization. -/
theorem cmp98PhysicalNonlinearBlockSUN_zero_inv_coe
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hnear0 : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding0 : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    ((cmp98PhysicalNonlinearBlockSUN
        U A b 0 hnear0 hnoWinding0)⁻¹ : SUN Nc) =
      (cmp98Eq119NonlinearBlockInverseAtZero U A b :
        Matrix (Fin Nc) (Fin Nc) ℂ) := by
  let Y := cmp98UbarLogAverage U b
    ((0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  have hzero :
      (0 : ℝ) • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  have hYskew : Matrix.conjTranspose Y = -Y := by
    have hmem :=
      (cmp98PhysicalUbarLogAverageSuLie
        U A b 0 hnear0 hnoWinding0).property
    have hskew :=
      (mem_suMatrixSubmodule_iff
        (cmp98PhysicalUbarLogAverageSuLie
          U A b 0 hnear0 hnoWinding0).toMatrix).mp hmem |>.1
    rw [cmp98PhysicalUbarLogAverageSuLie_toMatrix] at hskew
    exact hskew
  have hYzero : Y = cmp98UbarLogAverage U b 0 := by
    dsimp only [Y]
    rw [hzero]
  rw [coe_sun_inv_eq_conjTranspose]
  rw [cmp98PhysicalNonlinearBlockSUN_coe]
  unfold cmp98Eq119NonlinearBlockCurve
    cmp98Eq119NonlinearBlockInverseAtZero cmp98UbarExpAverage
  rw [Matrix.conjTranspose_mul]
  rw [← Matrix.exp_conjTranspose, hYskew]
  rw [hYzero]

/-- The existing ambient relative deviation is exactly the matrix deviation
of the preceding physical special-unitary relative block. -/
theorem cmp98Eq119NonlinearRelativeDeviation_eq_relativeSUN_sub_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hnear0 : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding0 : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    cmp98Eq119NonlinearRelativeDeviation U A b t =
      (cmp98PhysicalNonlinearRelativeSUN U A b t
        hnear hnoWinding hnear0 hnoWinding0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1 := by
  unfold cmp98Eq119NonlinearRelativeDeviation
    cmp98PhysicalNonlinearRelativeSUN
  change
    cmp98Eq119NonlinearBlockCurve U A b t *
        cmp98Eq119NonlinearBlockInverseAtZero U A b - 1 =
      (cmp98PhysicalNonlinearBlockSUN U A b t hnear hnoWinding :
          Matrix (Fin Nc) (Fin Nc) ℂ) *
        (((cmp98PhysicalNonlinearBlockSUN
          U A b 0 hnear0 hnoWinding0)⁻¹ : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1
  rw [cmp98PhysicalNonlinearBlockSUN_coe]
  rw [cmp98PhysicalNonlinearBlockSUN_zero_inv_coe]

/-- The exact normalized nonlinear logarithm, restored to its physical
`su(N)` codomain. -/
noncomputable def cmp98PhysicalNonlinearLogSuLie
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hnear0 : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding0 : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hrelativeNear :
      ‖(cmp98PhysicalNonlinearRelativeSUN U A b t
          hnear hnoWinding hnear0 hnoWinding0 :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hrelativeNoWinding : (Nc : ℝ) *
      ‖nearLog
        ((cmp98PhysicalNonlinearRelativeSUN U A b t
          hnear hnoWinding hnear0 hnoWinding0 :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SuLie Nc := by
  let D : SUN Nc :=
    cmp98PhysicalNonlinearRelativeSUN U A b t
      hnear hnoWinding hnear0 hnoWinding0
  let s : Finset Unit := {()}
  let w : Unit → ℝ := fun _ => 1
  let Ds : Unit → SUN Nc := fun _ => D
  have hD : ∀ i ∈ s,
      ‖(Ds i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1 := by
    intro i hi
    simpa only [Ds, D] using hrelativeNear
  have hwind : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((Ds i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi := by
    intro i hi
    simpa only [Ds, D] using hrelativeNoWinding
  have hskew :=
    cmp99UbarSpecialUnitaryExponent_mem_skewAdjoint s w Ds hD
  have htrace :=
    trace_cmp99UbarSpecialUnitaryExponent_eq_zero
      s w Ds hD hwind
  have hexponent :
      cmp99UbarSpecialUnitaryExponent s w Ds =
        nearLog ((D : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := by
    simp [cmp99UbarSpecialUnitaryExponent, cmp99UbarUnitaryExponent,
      cmp99UbarExponent, s, w, Ds]
    exact one_smul ℝ _
  refine ⟨nearLog
    ((cmp98PhysicalNonlinearRelativeSUN U A b t
      hnear hnoWinding hnear0 hnoWinding0 :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1), ?_⟩
  rw [mem_suMatrixSubmodule_iff]
  rw [hexponent] at hskew htrace
  exact ⟨skewAdjoint.mem_iff.mp hskew, htrace⟩

/-- The exact nonlinear block coordinate in the canonical real Lie
coordinates used by CMP102. -/
noncomputable def cmp98PhysicalNonlinearLogCoordinate
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hnear0 : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding0 : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hrelativeNear :
      ‖(cmp98PhysicalNonlinearRelativeSUN U A b t
          hnear hnoWinding hnear0 hnoWinding0 :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hrelativeNoWinding : (Nc : ℝ) *
      ‖nearLog
        ((cmp98PhysicalNonlinearRelativeSUN U A b t
          hnear hnoWinding hnear0 hnoWinding0 :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SUNLieCoord Nc :=
  suLieCoordIso Nc
    (cmp98PhysicalNonlinearLogSuLie U A b t
      hnear hnoWinding hnear0 hnoWinding0
      hrelativeNear hrelativeNoWinding)

/-- Decoding the physical nonlinear coordinate gives exactly the ambient
nonlinear log coordinate of CMP98 (122). -/
theorem cmp98PhysicalNonlinearLogCoordinate_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hnear0 : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding0 : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x 0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi)
    (hrelativeNear :
      ‖(cmp98PhysicalNonlinearRelativeSUN U A b t
          hnear hnoWinding hnear0 hnoWinding0 :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hrelativeNoWinding : (Nc : ℝ) *
      ‖nearLog
        ((cmp98PhysicalNonlinearRelativeSUN U A b t
          hnear hnoWinding hnear0 hnoWinding0 :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    ((suLieCoordIso Nc).symm
      (cmp98PhysicalNonlinearLogCoordinate U A b t
        hnear hnoWinding hnear0 hnoWinding0
        hrelativeNear hrelativeNoWinding)).toMatrix =
      cmp98Eq119NonlinearLogCoordinate U A b t := by
  rw [cmp98PhysicalNonlinearLogCoordinate]
  rw [(suLieCoordIso Nc).symm_apply_apply]
  change nearLog
      ((cmp98PhysicalNonlinearRelativeSUN U A b t
        hnear hnoWinding hnear0 hnoWinding0 :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1) =
    cmp98Eq119NonlinearLogCoordinate U A b t
  unfold cmp98Eq119NonlinearLogCoordinate
  rw [cmp98Eq119NonlinearRelativeDeviation_eq_relativeSUN_sub_one]

end

end YangMills.RG
