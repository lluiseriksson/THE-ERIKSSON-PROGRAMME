/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedSectionCCutFactor

/-!
# The source partition cutoffs in CMP99 Section C

CMP99, printed p. 408, imports a partition of unity `h_Pi` from Sect. A of
Balaban's preceding propagator paper and records the normalization

`sum_Pi h_Pi(x)^2 = 1`.

The characteristic function in (3.95)--(3.97) and the smooth partition
function play different roles.  This file keeps them distinct.  The former is
the literal characteristic of the source cell `Pi = tilde Pi^0`; the latter is
the restriction of one global square partition.  Their pointwise
contractivity is derived, rather than supplied transition by transition.
-/

namespace YangMills.RG

noncomputable section

universe v

/-- The source datum selected in CMP99: one square partition of unity on the
large-block lattice, indexed by the literal source cells `Pi`. -/
structure CMP99SourceSquarePartition (Q : ℕ) [NeZero Q] where
  value : FinBox 4 Q → FinBox 4 (2 * Q) → ℝ
  square_sum : ∀ block,
    ∑ cell : FinBox 4 Q, (value cell block) ^ 2 = 1

namespace CMP99SourceSquarePartition

/-- Every member of a square partition of unity has absolute value at most
one.  This is the source of the cutoff contraction used in (3.97). -/
theorem norm_value_le_one {Q : ℕ} [NeZero Q]
    (P : CMP99SourceSquarePartition Q)
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) :
    ‖P.value cell block‖ ≤ 1 := by
  classical
  have hterm : (P.value cell block) ^ 2 ≤
      ∑ other : FinBox 4 Q, (P.value other block) ^ 2 := by
    exact Finset.single_le_sum
      (fun other _ => sq_nonneg (P.value other block))
      (Finset.mem_univ cell)
  rw [P.square_sum block] at hterm
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa only [sq_abs, one_pow] using hterm

end CMP99SourceSquarePartition

/-- The characteristic multiplier attached to the literal source cell `Pi`.
The equality `tilde Pi^0 = Pi` is proved in
`BalabanCMP99SourceConcentricLargeBlockCube`. -/
def cmp99SourcePiCharacteristic {Q : ℕ} [NeZero Q]
    (cell : FinBox 4 Q) (block : FinBox 4 (2 * Q)) : ℝ :=
  if block ∈ cmp99SourceTildePiLargeBlocks cell 0 then 1 else 0

theorem norm_cmp99SourcePiCharacteristic_le_one
    {Q : ℕ} [NeZero Q] (cell : FinBox 4 Q)
    (block : FinBox 4 (2 * Q)) :
    ‖cmp99SourcePiCharacteristic cell block‖ ≤ 1 := by
  classical
  unfold cmp99SourcePiCharacteristic
  split <;> norm_num

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- The transition cut data of (3.97), generated from the literal source-cell
characteristic and one global square partition.  No transition-specific
function or contraction proof remains in the interface. -/
noncomputable def generatedSectionCSourceTransitionCutData
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (P : CMP99SourceSquarePartition Q)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) :
    D.GeneratedSectionCTransitionCutData hpi5 r where
  exterior := fun x => cmp99SourcePiCharacteristic cell x.1
  partition := fun x => P.value cell x.1
  exterior_norm_le_one := fun x =>
    norm_cmp99SourcePiCharacteristic_le_one cell x.1
  partition_norm_le_one := fun x => P.norm_value_le_one cell x.1

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
