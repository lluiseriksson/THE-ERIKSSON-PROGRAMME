/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalCorrectionChartIndependence

/-!
# Sup-norm realization of physical one-cochains

The physical cochain types are stored with their finite `L²` norm.  The
CMP98/CMP102 fixed-point argument instead uses the volume-uniform maximum
over bonds.  This file transports the same finite family of coordinates to
`PiLp ∞` and identifies its norm exactly with the explicit source and
correction sup norms already used by the analytic estimates.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- The same physical one-cochain coordinates equipped with the maximum
norm rather than the ambient finite `L²` norm. -/
abbrev PhysicalGaugeOneCochainSup (d N Nc : ℕ) [NeZero N] :=
  PiLp ⊤ (fun _ : PhysicalBond d N => SUNLieCoord Nc)

/-- Canonical finite-dimensional transport from the stored `L²` cochain to
the source-facing sup-norm cochain. -/
noncomputable def physicalGaugeOneCochainSupEquiv :
    PhysicalGaugeOneCochain d N Nc ≃L[ℝ]
      PhysicalGaugeOneCochainSup d N Nc :=
  (((WithLp.linearEquiv 2 ℝ
      (PhysicalBond d N → SUNLieCoord Nc)).trans
    (WithLp.linearEquiv ⊤ ℝ
      (PhysicalBond d N → SUNLieCoord Nc)).symm)).toContinuousLinearEquiv

@[simp] theorem physicalGaugeOneCochainSupEquiv_apply
    (A : PhysicalGaugeOneCochain d N Nc)
    (b : PhysicalBond d N) :
    physicalGaugeOneCochainSupEquiv A b = A b := by
  rfl

@[simp] theorem physicalGaugeOneCochainSupEquiv_symm_apply
    (A : PhysicalGaugeOneCochainSup d N Nc)
    (b : PhysicalBond d N) :
    physicalGaugeOneCochainSupEquiv.symm A b = A b := by
  rfl

section Source

variable {M N' : ℕ} [NeZero M] [NeZero N'] [NeZero (M * N')]

/-- The explicit source sup norm is exactly the transported `PiLp ∞` norm. -/
theorem norm_physicalGaugeOneCochainSupEquiv_eq_sourceSupNorm
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    ‖physicalGaugeOneCochainSupEquiv A‖ =
      cmp98SourceFieldSupNorm A := by
  rw [← PiLp.norm_ofLp (physicalGaugeOneCochainSupEquiv A), Pi.norm_def]
  apply le_antisymm
  · let m : NNReal :=
      ⟨cmp98SourceFieldSupNorm A, cmp98SourceFieldSupNorm_nonneg A⟩
    change
      (↑(Finset.univ.sup fun b : PhysicalBond d (M * N') => ‖A b‖₊) : ℝ) ≤
        (m : ℝ)
    exact_mod_cast (Finset.sup_le fun b _ => by
      apply (NNReal.coe_le_coe).mp
      exact norm_apply_le_cmp98SourceFieldSupNorm A b)
  · unfold cmp98SourceFieldSupNorm
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨b, _, rfl⟩
    change
      ‖A b‖ ≤
        (↑(Finset.univ.sup fun b : PhysicalBond d (M * N') => ‖A b‖₊) : ℝ)
    exact_mod_cast Finset.le_sup (s := Finset.univ)
      (f := fun b : PhysicalBond d (M * N') => ‖A b‖₊)
      (Finset.mem_univ b)

end Source

section Correction

variable {N' : ℕ} [NeZero N']

/-- The correction sup norm is nonnegative. -/
theorem cmp102PhysicalCorrectionSupNorm_nonneg
    (A : CoarsePhysicalOneCochain d N' Nc) :
    0 ≤ cmp102PhysicalCorrectionSupNorm A := by
  exact (norm_nonneg (A (Classical.choice inferInstance))).trans
    (norm_apply_le_cmp102PhysicalCorrectionSupNorm A _)

/-- The explicit correction sup norm is the same transported maximum norm. -/
theorem norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm
    (A : CoarsePhysicalOneCochain d N' Nc) :
    ‖physicalGaugeOneCochainSupEquiv A‖ =
      cmp102PhysicalCorrectionSupNorm A := by
  rw [← PiLp.norm_ofLp (physicalGaugeOneCochainSupEquiv A), Pi.norm_def]
  apply le_antisymm
  · let m : NNReal :=
      ⟨cmp102PhysicalCorrectionSupNorm A,
        cmp102PhysicalCorrectionSupNorm_nonneg A⟩
    change
      (↑(Finset.univ.sup fun b : PhysicalBond d N' => ‖A b‖₊) : ℝ) ≤
        (m : ℝ)
    exact_mod_cast (Finset.sup_le fun b _ => by
      apply (NNReal.coe_le_coe).mp
      exact norm_apply_le_cmp102PhysicalCorrectionSupNorm A b)
  · unfold cmp102PhysicalCorrectionSupNorm
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨b, _, rfl⟩
    change
      ‖A b‖ ≤
        (↑(Finset.univ.sup fun b : PhysicalBond d N' => ‖A b‖₊) : ℝ)
    exact_mod_cast Finset.le_sup (s := Finset.univ)
      (f := fun b : PhysicalBond d N' => ‖A b‖₊) (Finset.mem_univ b)

end Correction

end

end YangMills.RG
