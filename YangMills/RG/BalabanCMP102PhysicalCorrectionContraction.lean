/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalCorrectionSourceBound
import YangMills.RG.BalabanCMP102PhysicalCorrectionNorm

/-!
# Physical CMP102 correction contraction

The matrix remainder estimate is transported back to canonical `su(N)`
coordinates and then maximized over coarse bonds.  The only dimensional loss
is the already audited color factor `Nc`.  Consequently the visible scalar
condition `Nc * correctionRate < 1` gives a strict contraction on every
nonzero pair in the physical source sup metric.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The explicit contraction ratio after transporting the decoded matrix
remainder to canonical `su(N)` coordinates. -/
def cmp102PhysicalCorrectionContractionRate
    (Nc d M : ℕ) (r s : ℝ) : ℝ :=
  (Nc : ℝ) * cmp102SourceCorrectionLinearRate d M r s

set_option maxHeartbeats 10000000 in
/-- Pointwise coordinate form of the complete two-field correction bound. -/
theorem norm_cmp102PhysicalNonlinearCorrectionField_sub_apply_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (ChartA : CMP102PhysicalNonlinearFieldChart U A)
    (ChartB : CMP102PhysicalNonlinearFieldChart U B)
    (b : PhysicalBond d N') (r s : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : cmp98SourceFieldSupNorm B ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A 1 ≤ r)
    (hrB : 1 / 3 + cmp98SourceContourDisplacementBudget B 1 ≤ r)
    (hr1 : r < 1)
    (hsA : cmp98SourcePhysicalBlockDisplacementBudget A 1 r ≤ s)
    (hsB : cmp98SourcePhysicalBlockDisplacementBudget B 1 r ≤ s)
    (hs1 : s < 1) :
    ‖cmp102PhysicalNonlinearCorrectionField U A ChartA b -
        cmp102PhysicalNonlinearCorrectionField U B ChartB b‖ ≤
      cmp102PhysicalCorrectionContractionRate Nc d M r s *
        cmp98SourceFieldSupNorm (A - B) := by
  let CA := cmp102PhysicalNonlinearCorrectionField U A ChartA b
  let CB := cmp102PhysicalNonlinearCorrectionField U B ChartB b
  have hmatrix :
      ‖cmp98LieCoordToAmbientCLM Nc (CA - CB)‖ ≤
        cmp102SourceCorrectionLinearRate d M r s *
          cmp98SourceFieldSupNorm (A - B) := by
    rw [map_sub]
    change
      ‖cmp98LieCoordToAmbientCLM Nc
          (cmp102PhysicalNonlinearCorrectionField U A ChartA b) -
        cmp98LieCoordToAmbientCLM Nc
          (cmp102PhysicalNonlinearCorrectionField U B ChartB b)‖ ≤ _
    rw [cmp102PhysicalNonlinearCorrectionField_toMatrix U A ChartA b,
      cmp102PhysicalNonlinearCorrectionField_toMatrix U B ChartB b]
    simpa using
      norm_cmp98Eq122NonlinearLogRemainder_twoField_sub_le_sourceSupNorm
        U A B b 1 r s hbase (by simpa using hA) (by simpa using hB)
          hrA hrB hr1 hsA hsB hs1
  change ‖CA - CB‖ ≤ _
  calc
    ‖CA - CB‖
        ≤ (Nc : ℝ) * ‖cmp98LieCoordToAmbientCLM Nc (CA - CB)‖ :=
      norm_lieCoord_le_card_mul_norm_toMatrix (CA - CB)
    _ ≤ (Nc : ℝ) *
          (cmp102SourceCorrectionLinearRate d M r s *
            cmp98SourceFieldSupNorm (A - B)) := by
      exact mul_le_mul_of_nonneg_left hmatrix (Nat.cast_nonneg Nc)
    _ = cmp102PhysicalCorrectionContractionRate Nc d M r s *
          cmp98SourceFieldSupNorm (A - B) := by
      unfold cmp102PhysicalCorrectionContractionRate
      ring

set_option maxHeartbeats 10000000 in
/-- Volume-independent sup-metric Lipschitz bound for the assembled physical
correction fields.  Field-specific chart certificates disappear from the
right-hand side. -/
theorem cmp102PhysicalCorrectionSupNorm_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (ChartA : CMP102PhysicalNonlinearFieldChart U A)
    (ChartB : CMP102PhysicalNonlinearFieldChart U B)
    (r s : ℝ)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : cmp98SourceFieldSupNorm B ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A 1 ≤ r)
    (hrB : 1 / 3 + cmp98SourceContourDisplacementBudget B 1 ≤ r)
    (hr1 : r < 1)
    (hsA : cmp98SourcePhysicalBlockDisplacementBudget A 1 r ≤ s)
    (hsB : cmp98SourcePhysicalBlockDisplacementBudget B 1 r ≤ s)
    (hs1 : s < 1) :
    cmp102PhysicalCorrectionSupNorm
        (cmp102PhysicalNonlinearCorrectionField U A ChartA -
          cmp102PhysicalNonlinearCorrectionField U B ChartB) ≤
      cmp102PhysicalCorrectionContractionRate Nc d M r s *
        cmp98SourceFieldSupNorm (A - B) := by
  unfold cmp102PhysicalCorrectionSupNorm
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
  simpa only [Pi.sub_apply] using
    norm_cmp102PhysicalNonlinearCorrectionField_sub_apply_le
      U A B ChartA ChartB b r s (hbase b) hA hB
        hrA hrB hr1 hsA hsB hs1

/-- Under the explicit scalar smallness condition, the correction strictly
decreases every positive physical source distance. -/
theorem cmp102PhysicalCorrectionSupNorm_sub_lt_sourceSupNorm
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (ChartA : CMP102PhysicalNonlinearFieldChart U A)
    (ChartB : CMP102PhysicalNonlinearFieldChart U B)
    (r s : ℝ)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hA : cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hB : cmp98SourceFieldSupNorm B ≤ 1 / 2)
    (hrA : 1 / 3 + cmp98SourceContourDisplacementBudget A 1 ≤ r)
    (hrB : 1 / 3 + cmp98SourceContourDisplacementBudget B 1 ≤ r)
    (hr1 : r < 1)
    (hsA : cmp98SourcePhysicalBlockDisplacementBudget A 1 r ≤ s)
    (hsB : cmp98SourcePhysicalBlockDisplacementBudget B 1 r ≤ s)
    (hs1 : s < 1)
    (hcontract : cmp102PhysicalCorrectionContractionRate Nc d M r s < 1)
    (hdist : 0 < cmp98SourceFieldSupNorm (A - B)) :
    cmp102PhysicalCorrectionSupNorm
        (cmp102PhysicalNonlinearCorrectionField U A ChartA -
          cmp102PhysicalNonlinearCorrectionField U B ChartB) <
      cmp98SourceFieldSupNorm (A - B) := by
  refine lt_of_le_of_lt
    (cmp102PhysicalCorrectionSupNorm_sub_le U A B ChartA ChartB r s
      hbase hA hB hrA hrB hr1 hsA hsB hs1) ?_
  nlinarith

end

end YangMills.RG
