/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceUbarContours
import YangMills.RG.BalabanCMP99CovariantPathControl
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint
import YangMills.RG.AveragingL2

/-!
# Energy of the literal CMP99 straight coarse transport

The middle contour in the physical `Ubar` construction is a straight path of
exactly `M` fine bonds.  Summed over all possible starting sites, its path
energy is exactly `M` times the fine covariant energy in that direction.  In
particular no ambient-volume factor is introduced.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Adding one bond to a straight path adds exactly the corresponding
positive-bond covariant energy. -/
theorem covariantPathEnergy_cmp99StraightPositivePath_succ
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (x : FinBox d (M * N')) (mu : Fin d) (n : ℕ) :
    covariantPathEnergy rho U phi
        (cmp99StraightPositivePath (G := SUN Nc)
          (M := M) (N' := N') x mu (n + 1)).edges =
      covariantPathEnergy rho U phi
        (cmp99StraightPositivePath (G := SUN Nc)
          (M := M) (N' := N') x mu n).edges +
      ‖covariantD0CLM rho U phi (((fun y => FinBox.shift y mu)^[n] x), mu)‖ ^ 2 := by
  simp [cmp99StraightPositivePath, covariantPathEnergy,
    OrientedLatticePath.trans, positiveCoordinatePath,
    norm_covariantEdgeDefect_eq, physicalBondOfEdge]

/-- A finite sum over the periodic box is invariant under any iterate of one
coordinate shift. -/
theorem FinBox.sum_iterate_shift
    {N : ℕ} [NeZero N]
    (f : FinBox d N → ℝ) (mu : Fin d) (n : ℕ) :
    ∑ x : FinBox d N, f ((fun y => FinBox.shift y mu)^[n] x) =
      ∑ x : FinBox d N, f x :=
  (iterShift_bijective N mu n).sum_comp f

/-- Global straight-path energy identity.  Every positive bond in direction
`mu` occurs exactly `n` times when all starting sites are summed. -/
theorem sum_covariantPathEnergy_cmp99StraightPositivePath
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (mu : Fin d) (n : ℕ) :
    (∑ x : FinBox d (M * N'),
      covariantPathEnergy rho U phi
        (cmp99StraightPositivePath (G := SUN Nc)
          (M := M) (N' := N') x mu n).edges) =
      (n : ℝ) * ∑ x : FinBox d (M * N'),
        ‖covariantD0CLM rho U phi (x, mu)‖ ^ 2 := by
  induction n with
  | zero =>
      simp [cmp99StraightPositivePath, covariantPathEnergy,
        OrientedLatticePath.refl]
  | succ n ih =>
      simp_rw [covariantPathEnergy_cmp99StraightPositivePath_succ]
      rw [Finset.sum_add_distrib, ih]
      have hshift :
          (∑ x : FinBox d (M * N'),
            ‖covariantD0CLM rho U phi
              (((fun y => FinBox.shift y mu)^[n] x), mu)‖ ^ 2) =
            ∑ x : FinBox d (M * N'),
              ‖covariantD0CLM rho U phi (x, mu)‖ ^ 2 :=
        FinBox.sum_iterate_shift
          (fun x : FinBox d (M * N') =>
            ‖covariantD0CLM rho U phi (x, mu)‖ ^ 2) mu n
      rw [hshift]
      push_cast
      ring

/-- Summing also over directions recovers exactly `n` times the full
covariant derivative energy. -/
theorem sum_covariantPathEnergy_cmp99StraightPositivePath_all
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (n : ℕ) :
    (∑ mu : Fin d, ∑ x : FinBox d (M * N'),
      covariantPathEnergy rho U phi
        (cmp99StraightPositivePath (G := SUN Nc)
          (M := M) (N' := N') x mu n).edges) =
      (n : ℝ) * ‖covariantD0CLM rho U phi‖ ^ 2 := by
  simp_rw [sum_covariantPathEnergy_cmp99StraightPositivePath]
  rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Cauchy--Schwarz for a normalized finite mean, in the exact squared form
used by the source block average. -/
theorem norm_normalized_fintype_sum_sq_le
    {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ℝ) (hw : 0 ≤ w)
    (hnorm : w * (Fintype.card I : ℝ) = 1)
    (v : I → E) :
    ‖w • ∑ i : I, v i‖ ^ 2 ≤ w * ∑ i : I, ‖v i‖ ^ 2 := by
  have hsum : ‖∑ i : I, v i‖ ≤ ∑ i : I, ‖v i‖ := norm_sum_le _ _
  have hnonneg : 0 ≤ ∑ i : I, ‖v i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsq : ‖∑ i : I, v i‖ ^ 2 ≤ (∑ i : I, ‖v i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hsum
  have hcs : (∑ i : I, ‖v i‖) ^ 2 ≤
      (Fintype.card I : ℝ) * ∑ i : I, ‖v i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset I)) (f := fun i : I => ‖v i‖)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, mul_pow]
  calc
    w ^ 2 * ‖∑ i : I, v i‖ ^ 2 ≤
        w ^ 2 * ((Fintype.card I : ℝ) * ∑ i : I, ‖v i‖ ^ 2) := by
      gcongr
      exact hsq.trans hcs
    _ = w * ∑ i : I, ‖v i‖ ^ 2 := by
      have hcoef : w ^ 2 * (Fintype.card I : ℝ) = w := by
        calc
          w ^ 2 * (Fintype.card I : ℝ) =
              w * (w * (Fintype.card I : ℝ)) := by ring
          _ = w := by rw [hnorm, mul_one]
      calc
        w ^ 2 * ((Fintype.card I : ℝ) * ∑ i : I, ‖v i‖ ^ 2) =
            (w ^ 2 * (Fintype.card I : ℝ)) *
              ∑ i : I, ‖v i‖ ^ 2 := by ring
        _ = w * ∑ i : I, ‖v i‖ ^ 2 := by rw [hcoef]

/-- The covariant straight-line defect averaged over one source block and
transported back to its basepoint.  This is the exact linear quantity that
precedes comparison with the physical `Ubar` coarse derivative. -/
noncomputable def cmp99SourceParallelAverageDefectValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d) : SUNLieCoord Nc :=
  cmp99SourceBlockAverageWeight M d •
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
      rho.adCLM
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
        (phi x.1 -
          rho.adCLM
            ((cmp99SourceParallelTransportPath (G := SUN Nc)
              (M := M) (N' := N') x.1 mu).holonomy U)
            (phi (cmp99SourceTranslatedSite x.1 mu)))

/-- One block-direction averaged straight defect is controlled by the sum of
the physical path energies starting in that block. -/
theorem norm_cmp99SourceParallelAverageDefectValue_sq_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') (mu : Fin d) :
    ‖cmp99SourceParallelAverageDefectValue rho U phi y mu‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d * (M : ℝ) *
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
          covariantPathEnergy rho U phi
            (cmp99SourceParallelTransportPath (G := SUN Nc)
              (M := M) (N' := N') x.1 mu).edges := by
  let I := {x : FinBox d (M * N') // x ∈ blockOf M N' y}
  let v : I → SUNLieCoord Nc := fun x =>
    rho.adCLM
      (cmp99ContourHolonomy
        (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
      (phi x.1 -
        rho.adCLM
          ((cmp99SourceParallelTransportPath (G := SUN Nc)
            (M := M) (N' := N') x.1 mu).holonomy U)
          (phi (cmp99SourceTranslatedSite x.1 mu)))
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
    unfold cmp99SourceBlockAverageWeight
    positivity
  have hnorm : cmp99SourceBlockAverageWeight M d *
      (Fintype.card I : ℝ) = 1 := by
    change cmp99SourceBlockAverageWeight M d *
      (Fintype.card {x : FinBox d (M * N') // x ∈ blockOf M N' y} : ℝ) = 1
    rw [Fintype.card_coe, blockOf_card, Nat.cast_pow]
    exact cmp99SourceBlockAverageWeight_mul_card
  have hmean := norm_normalized_fintype_sum_sq_le
    (cmp99SourceBlockAverageWeight M d) hw hnorm v
  change ‖cmp99SourceBlockAverageWeight M d • ∑ x : I, v x‖ ^ 2 ≤ _
  calc
    ‖cmp99SourceBlockAverageWeight M d • ∑ x : I, v x‖ ^ 2 ≤
        cmp99SourceBlockAverageWeight M d * ∑ x : I, ‖v x‖ ^ 2 := hmean
    _ ≤ cmp99SourceBlockAverageWeight M d *
        ∑ x : I, (M : ℝ) *
          covariantPathEnergy rho U phi
            (cmp99SourceParallelTransportPath (G := SUN Nc)
              (M := M) (N' := N') x.1 mu).edges := by
      gcongr with x
      rw [rho.norm_ad]
      simpa only [cmp99SourceParallelTransportPath_length] using
        norm_covariantPathDefect_sq_le_length_mul_energy rho U phi
          (cmp99SourceParallelTransportPath (G := SUN Nc)
            (M := M) (N' := N') x.1 mu)
    _ = cmp99SourceBlockAverageWeight M d * (M : ℝ) *
        ∑ x : I,
          covariantPathEnergy rho U phi
            (cmp99SourceParallelTransportPath (G := SUN Nc)
              (M := M) (N' := N') x.1 mu).edges := by
      rw [← Finset.mul_sum]
      ring

/-- Global no-volume-loss estimate for the averaged straight defects.  Its
coefficient is exactly `M^(2-d)` in the source normalization. -/
theorem sum_norm_cmp99SourceParallelAverageDefectValue_sq_le
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    (∑ y : FinBox d N', ∑ mu : Fin d,
      ‖cmp99SourceParallelAverageDefectValue rho U phi y mu‖ ^ 2) ≤
      ((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2 *
        ‖covariantD0CLM rho U phi‖ ^ 2 := by
  calc
    (∑ y : FinBox d N', ∑ mu : Fin d,
        ‖cmp99SourceParallelAverageDefectValue rho U phi y mu‖ ^ 2) ≤
      ∑ y : FinBox d N', ∑ mu : Fin d,
        cmp99SourceBlockAverageWeight M d * (M : ℝ) *
          ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
            covariantPathEnergy rho U phi
              (cmp99SourceParallelTransportPath (G := SUN Nc)
                (M := M) (N' := N') x.1 mu).edges := by
      gcongr with y _ mu _
      exact norm_cmp99SourceParallelAverageDefectValue_sq_le
        rho U phi y mu
    _ = cmp99SourceBlockAverageWeight M d * (M : ℝ) *
        ∑ mu : Fin d, ∑ x : FinBox d (M * N'),
          covariantPathEnergy rho U phi
            (cmp99SourceParallelTransportPath (G := SUN Nc)
              (M := M) (N' := N') x mu).edges := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro mu _hmu
      rw [← sum_blockOf M N']
      apply Finset.sum_congr rfl
      intro y _hy
      exact (Finset.sum_subtype (blockOf M N' y) (fun _ => Iff.rfl)
        (fun x => covariantPathEnergy rho U phi
          (cmp99SourceParallelTransportPath (G := SUN Nc)
            (M := M) (N' := N') x mu).edges)).symm
    _ = cmp99SourceBlockAverageWeight M d * (M : ℝ) *
        ((M : ℝ) * ‖covariantD0CLM rho U phi‖ ^ 2) := by
      simp only [cmp99SourceParallelTransportPath]
      rw [sum_covariantPathEnergy_cmp99StraightPositivePath_all
        (M := M) (N' := N') rho U phi M]
    _ = ((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2 *
        ‖covariantD0CLM rho U phi‖ ^ 2 := by
      unfold cmp99SourceBlockAverageWeight
      ring

end

end YangMills.RG
