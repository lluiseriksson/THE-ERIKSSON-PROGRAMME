/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CoarseDerivativeDecomposition
import YangMills.RG.BalabanCMP99SourceUbarSmallFieldPropagation
import YangMills.RG.BalabanCMP116AdjointSmallBridge

/-!
# Quantitative control of the CMP99 coarse-transport remainder

The exact coarse-derivative decomposition leaves the difference between a
site-dependent three-contour transport and the physical coarse link.  Here
that difference is controlled in the concrete matrix adjoint model directly
from fundamental-link smallness.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Fundamental matrix distance from the identity controls the concrete
coordinate adjoint action with the sharp factor two supplied by conjugation. -/
theorem norm_matrixSUNAdjointModel_ad_sub_self_le
    (g : SUN Nc) (X : SUNLieCoord Nc) {epsilon : ℝ}
    (hsmall :
      ‖(g : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ‖(matrixSUNAdjointModel Nc).adCLM g X - X‖ ≤
      2 * epsilon * ‖X‖ := by
  let Y : SuLie Nc := (suLieCoordIso Nc).symm X
  have hsu :
      ‖suAdActLin g Y - Y‖ ≤ 2 * epsilon * ‖Y‖ :=
    norm_suAdActLin_sub_self_le g Y hsmall
  have hcoord :
      ‖(suLieCoordIso Nc) (suAdActLin g Y - Y)‖ ≤
        2 * epsilon * ‖(suLieCoordIso Nc) Y‖ := by
    simpa only [(suLieCoordIso Nc).norm_map] using hsu
  change
    ‖(suLieCoordIso Nc)
        (suAdActLin g ((suLieCoordIso Nc).symm X)) - X‖ ≤
      2 * epsilon * ‖X‖
  simpa [Y, map_sub] using hcoord

/-- Two near-identity group elements have nearby concrete adjoint actions. -/
theorem norm_matrixSUNAdjointModel_ad_sub_ad_le
    (g h : SUN Nc) (X : SUNLieCoord Nc) {epsilonG epsilonH : ℝ}
    (hg : ‖(g : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonG)
    (hh : ‖(h : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonH) :
    ‖(matrixSUNAdjointModel Nc).adCLM g X -
        (matrixSUNAdjointModel Nc).adCLM h X‖ ≤
      2 * (epsilonG + epsilonH) * ‖X‖ := by
  calc
    _ ≤ ‖(matrixSUNAdjointModel Nc).adCLM g X - X‖ +
        ‖X - (matrixSUNAdjointModel Nc).adCLM h X‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          ((matrixSUNAdjointModel Nc).adCLM g X - X)
          (X - (matrixSUNAdjointModel Nc).adCLM h X)
    _ = ‖(matrixSUNAdjointModel Nc).adCLM g X - X‖ +
        ‖(matrixSUNAdjointModel Nc).adCLM h X - X‖ := by
      rw [← norm_neg (X - (matrixSUNAdjointModel Nc).adCLM h X)]
      simp only [neg_sub]
    _ ≤ 2 * epsilonG * ‖X‖ + 2 * epsilonH * ‖X‖ :=
      add_le_add
        (norm_matrixSUNAdjointModel_ad_sub_self_le g X hg)
        (norm_matrixSUNAdjointModel_ad_sub_self_le h X hh)
    _ = 2 * (epsilonG + epsilonH) * ‖X‖ := by ring

/-- Radius of the literal source-to-target three-contour holonomy. -/
def cmp99SourceTripleHolonomyRadius
    (d M : ℕ) (epsilonFine : ℝ) : ℝ :=
  ((2 * d * (M - 1) + M : ℕ) : ℝ) * epsilonFine

theorem norm_sun_mul_three_sub_one_le
    (g h k : SUN Nc) :
    ‖((g * h * k : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      ‖(g : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
      ‖(h : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
      ‖(k : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ :=
  (norm_sun_mul_sub_one_le (g * h) k).trans
    (add_le_add (norm_sun_mul_sub_one_le g h) le_rfl)

/-- Uniform fine-link smallness controls the literal three-contour holonomy,
without using the distinct four-factor deviation radius. -/
theorem norm_cmp99SourceTripleHolonomy_sub_one_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    ‖(cmp99SourceTripleHolonomy U y mu x :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceTripleHolonomyRadius d M epsilonFine := by
  let Gamma1 := cmp99SourceUbarGamma1 (G := SUN Nc) (y, mu) x.1
  let Gamma2 := cmp99SourceUbarGamma2 (G := SUN Nc) (y, mu) x.1
  let Gamma3 := cmp99SourceUbarGamma3 (G := SUN Nc) (y, mu) x.1
  have h1 := norm_wilsonLine_sub_one_le_length_mul U Gamma1 epsilonFine
    (fun e _ => fine_small e)
  have h2 := norm_wilsonLine_sub_one_le_length_mul U Gamma2 epsilonFine
    (fun e _ => fine_small e)
  have h3 := norm_wilsonLine_sub_one_le_length_mul U Gamma3 epsilonFine
    (fun e _ => fine_small e)
  have hlen1 : Gamma1.length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma1_length_le (G := SUN Nc) (y, mu) x.1 x.2
  have hlen2 : Gamma2.length = M :=
    cmp99SourceUbarGamma2_length (G := SUN Nc) (y, mu) x.1
  have hlen3 : Gamma3.length ≤ d * (M - 1) :=
    cmp99SourceUbarGamma3_length_le (G := SUN Nc) (y, mu) x.1 x.2
  have htriple :
      ‖(cmp99SourceTripleHolonomy U y mu x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        ‖((wilsonLine U Gamma1 : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖((wilsonLine U Gamma2 : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ +
        ‖((wilsonLine U Gamma3 : SUN Nc) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
    rw [cmp99SourceTripleHolonomy_eq_three_wilsonLines]
    exact norm_sun_mul_three_sub_one_le
      (wilsonLine U Gamma1 : SUN Nc)
      (wilsonLine U Gamma2 : SUN Nc)
      (wilsonLine U Gamma3 : SUN Nc)
  calc
    _ ≤ ((Gamma1.length : ℝ) * epsilonFine +
          (Gamma2.length : ℝ) * epsilonFine) +
        (Gamma3.length : ℝ) * epsilonFine :=
      htriple.trans (add_le_add (add_le_add h1 h2) h3)
    _ ≤ (((d * (M - 1) : ℕ) : ℝ) * epsilonFine +
          (M : ℝ) * epsilonFine) +
        ((d * (M - 1) : ℕ) : ℝ) * epsilonFine := by
      have h1' : (Gamma1.length : ℝ) * epsilonFine ≤
          ((d * (M - 1) : ℕ) : ℝ) * epsilonFine :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlen1) epsilonFine_nonneg
      have h2' : (Gamma2.length : ℝ) * epsilonFine =
          (M : ℝ) * epsilonFine := by rw [hlen2]
      have h3' : (Gamma3.length : ℝ) * epsilonFine ≤
          ((d * (M - 1) : ℕ) : ℝ) * epsilonFine :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlen3) epsilonFine_nonneg
      exact add_le_add (add_le_add h1' h2'.le) h3'
    _ = cmp99SourceTripleHolonomyRadius d M epsilonFine := by
      simp only [cmp99SourceTripleHolonomyRadius, Nat.cast_add, Nat.cast_mul]
      ring

/-- Pointwise physical control of the exact coarse-transport mismatch. -/
theorem norm_cmp99SourceCoarseTransportRemainderValue_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse)
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    ‖cmp99SourceCoarseTransportRemainderValue
        (matrixSUNAdjointModel Nc) U V phi y mu x‖ ≤
      2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine + epsilonCoarse) *
        ‖phi (cmp99SourceTranslatedSite x.1 mu)‖ := by
  have htriple := norm_cmp99SourceTripleHolonomy_sub_one_le
    U epsilonFine epsilonFine_nonneg fine_small y mu x
  have h := norm_matrixSUNAdjointModel_ad_sub_ad_le
    (cmp99SourceTripleHolonomy U y mu x)
    (V (positiveEdgeOfPhysicalBond (y, mu)))
    (cmp99SourceTargetTransportedValue
      (matrixSUNAdjointModel Nc) U phi y mu x)
    htriple (coarse_small (y, mu))
  unfold cmp99SourceCoarseTransportRemainderValue
  unfold cmp99SourceTargetTransportedValue at h
  rw [(matrixSUNAdjointModel Nc).norm_ad] at h
  exact h

/-- One source block and direction: the averaged remainder costs only the
source normalization times the fine target-field energy. -/
theorem norm_cmp99SourceCoarseTransportRemainder_sq_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse)
    (y : FinBox d N') (mu : Fin d) :
    ‖cmp99SourceCoarseTransportRemainder
        (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 *
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
          ‖phi (cmp99SourceTranslatedSite x.1 mu)‖ ^ 2 := by
  let I := {x : FinBox d (M * N') // x ∈ blockOf M N' y}
  let kappa := 2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
    epsilonCoarse)
  let v : I → SUNLieCoord Nc := fun x =>
    cmp99SourceCoarseTransportRemainderValue
      (matrixSUNAdjointModel Nc) U V phi y mu x
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
    unfold cmp99SourceBlockAverageWeight
    positivity
  have hnorm : cmp99SourceBlockAverageWeight M d *
      (Fintype.card I : ℝ) = 1 := by
    change cmp99SourceBlockAverageWeight M d *
      (Fintype.card {x : FinBox d (M * N') // x ∈ blockOf M N' y} : ℝ) = 1
    rw [Fintype.card_coe, blockOf_card, Nat.cast_pow]
    exact cmp99SourceBlockAverageWeight_mul_card
  have hkappa : 0 ≤ kappa := by
    dsimp [kappa, cmp99SourceTripleHolonomyRadius]
    positivity
  have hmean := norm_normalized_fintype_sum_sq_le
    (cmp99SourceBlockAverageWeight M d) hw hnorm v
  change ‖cmp99SourceBlockAverageWeight M d • ∑ x : I, v x‖ ^ 2 ≤ _
  calc
    ‖cmp99SourceBlockAverageWeight M d • ∑ x : I, v x‖ ^ 2 ≤
        cmp99SourceBlockAverageWeight M d * ∑ x : I, ‖v x‖ ^ 2 := hmean
    _ ≤ cmp99SourceBlockAverageWeight M d *
        ∑ x : I, (kappa * ‖phi (cmp99SourceTranslatedSite x.1 mu)‖) ^ 2 := by
      gcongr with x
      simpa only [v, kappa] using
        norm_cmp99SourceCoarseTransportRemainderValue_le
          U V phi epsilonFine epsilonCoarse epsilonFine_nonneg
          fine_small coarse_small y mu x
    _ = cmp99SourceBlockAverageWeight M d * kappa ^ 2 *
        ∑ x : I, ‖phi (cmp99SourceTranslatedSite x.1 mu)‖ ^ 2 := by
      simp only [mul_pow, ← Finset.mul_sum]
      ring
    _ = _ := rfl

/-- Global no-volume-loss estimate for the coarse-transport remainder.  The
only multiplicity is the physical number of directions; translation of the
target field and the source-block partition are both exact reindexings. -/
theorem sum_norm_cmp99SourceCoarseTransportRemainder_sq_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse) :
    (∑ y : FinBox d N', ∑ mu : Fin d,
      ‖cmp99SourceCoarseTransportRemainder
        (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2) ≤
      cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) * ‖phi‖ ^ 2 := by
  let kappa := 2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
    epsilonCoarse)
  calc
    (∑ y : FinBox d N', ∑ mu : Fin d,
        ‖cmp99SourceCoarseTransportRemainder
          (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2) ≤
      ∑ y : FinBox d N', ∑ mu : Fin d,
        cmp99SourceBlockAverageWeight M d * kappa ^ 2 *
          ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
            ‖phi (cmp99SourceTranslatedSite x.1 mu)‖ ^ 2 := by
      gcongr with y _ mu _
      simpa only [kappa] using
        norm_cmp99SourceCoarseTransportRemainder_sq_le
          U V phi epsilonFine epsilonCoarse epsilonFine_nonneg
          epsilonCoarse_nonneg fine_small coarse_small y mu
    _ = cmp99SourceBlockAverageWeight M d * kappa ^ 2 *
        ∑ mu : Fin d, ∑ x : FinBox d (M * N'),
          ‖phi (cmp99SourceTranslatedSite x mu)‖ ^ 2 := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro mu _hmu
      rw [← sum_blockOf M N']
      apply Finset.sum_congr rfl
      intro y _hy
      exact (Finset.sum_subtype (blockOf M N' y) (fun _ => Iff.rfl)
        (fun x => ‖phi (cmp99SourceTranslatedSite x mu)‖ ^ 2)).symm
    _ = cmp99SourceBlockAverageWeight M d * kappa ^ 2 *
        ∑ mu : Fin d, ∑ x : FinBox d (M * N'), ‖phi x‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro mu _hmu
      exact FinBox.sum_iterate_shift
        (fun x : FinBox d (M * N') => ‖phi x‖ ^ 2) mu M
    _ = cmp99SourceBlockAverageWeight M d * kappa ^ 2 *
        (d : ℝ) * ‖phi‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp
      ring
    _ = _ := rfl

/-- Squared triangle inequality in the uniform form used to combine the exact
straight defect and transport remainder. -/
theorem norm_add_sq_le_two {E : Type*} [NormedAddCommGroup E]
    (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hnorm : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- One-scale physical gradient bound for the literal CMP99 block average.
The first term is the exact straight-path energy; the second is the explicit
small-background transport mismatch.  No coefficient depends on `N'`. -/
theorem norm_covariantD0_cmp99FullSourceBlockAverage_sq_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse) :
    ‖covariantD0CLM (matrixSUNAdjointModel Nc) V
        (cmp99FullSourceBlockAverage (matrixSUNAdjointModel Nc) U phi)‖ ^ 2 ≤
      2 * (((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2) *
          ‖covariantD0CLM (matrixSUNAdjointModel Nc) U phi‖ ^ 2 +
        2 * (cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            epsilonCoarse)) ^ 2 * (d : ℝ)) * ‖phi‖ ^ 2 := by
  have hpoint (y : FinBox d N') (mu : Fin d) :
      ‖covariantD0CLM (matrixSUNAdjointModel Nc) V
          (cmp99FullSourceBlockAverage (matrixSUNAdjointModel Nc) U phi)
          (y, mu)‖ ^ 2 ≤
        2 * ‖cmp99SourceParallelAverageDefectValue
          (matrixSUNAdjointModel Nc) U phi y mu‖ ^ 2 +
        2 * ‖cmp99SourceCoarseTransportRemainder
          (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2 := by
    rw [covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder]
    exact norm_add_sq_le_two _ _
  have hsum :
      (∑ y : FinBox d N', ∑ mu : Fin d,
        ‖covariantD0CLM (matrixSUNAdjointModel Nc) V
          (cmp99FullSourceBlockAverage (matrixSUNAdjointModel Nc) U phi)
          (y, mu)‖ ^ 2) ≤
        2 * (∑ y : FinBox d N', ∑ mu : Fin d,
          ‖cmp99SourceParallelAverageDefectValue
            (matrixSUNAdjointModel Nc) U phi y mu‖ ^ 2) +
        2 * (∑ y : FinBox d N', ∑ mu : Fin d,
          ‖cmp99SourceCoarseTransportRemainder
            (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2) := by
    calc
      _ ≤ ∑ y : FinBox d N', ∑ mu : Fin d,
          (2 * ‖cmp99SourceParallelAverageDefectValue
              (matrixSUNAdjointModel Nc) U phi y mu‖ ^ 2 +
            2 * ‖cmp99SourceCoarseTransportRemainder
              (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2) := by
        gcongr with y _ mu _
        exact hpoint y mu
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    ‖covariantD0CLM (matrixSUNAdjointModel Nc) V
        (cmp99FullSourceBlockAverage (matrixSUNAdjointModel Nc) U phi)‖ ^ 2 =
      ∑ y : FinBox d N', ∑ mu : Fin d,
        ‖covariantD0CLM (matrixSUNAdjointModel Nc) V
          (cmp99FullSourceBlockAverage (matrixSUNAdjointModel Nc) U phi)
          (y, mu)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    _ ≤ 2 * (∑ y : FinBox d N', ∑ mu : Fin d,
          ‖cmp99SourceParallelAverageDefectValue
            (matrixSUNAdjointModel Nc) U phi y mu‖ ^ 2) +
        2 * (∑ y : FinBox d N', ∑ mu : Fin d,
          ‖cmp99SourceCoarseTransportRemainder
            (matrixSUNAdjointModel Nc) U V phi y mu‖ ^ 2) := hsum
    _ ≤ 2 * (((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2) *
          ‖covariantD0CLM (matrixSUNAdjointModel Nc) U phi‖ ^ 2 +
        2 * (cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            epsilonCoarse)) ^ 2 * (d : ℝ)) * ‖phi‖ ^ 2 := by
      have hdef := sum_norm_cmp99SourceParallelAverageDefectValue_sq_le
        (M := M) (N' := N') (matrixSUNAdjointModel Nc) U phi
      have hrem := sum_norm_cmp99SourceCoarseTransportRemainder_sq_le
        U V phi epsilonFine epsilonCoarse epsilonFine_nonneg
        epsilonCoarse_nonneg fine_small coarse_small
      linarith

/-- The printed logarithmic smallness condition makes the generated coarse
radius nonnegative; no separate sign premise is needed by the physical
specialization. -/
theorem cmp99SourceUbarNextFineRadius_nonneg_of_logSmall
    (epsilonFine : ℝ) (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1) :
    0 ≤ cmp99SourceUbarNextFineRadius d M epsilonFine := by
  let B := cmp99SourceUbarFineNoWindingBudget
    (d := d) (M := M) (Nc := Nc) epsilonFine noWinding
  let delta := cmp99SourceUbarFineDeviationRadius d M epsilonFine
  let theta := delta / (1 - delta)
  have hdelta : 0 ≤ delta := by
    dsimp only [delta, cmp99SourceUbarFineDeviationRadius]
    positivity
  have hdelta_lt_one : delta < 1 := by
    simpa only [B, cmp99SourceUbarFineNoWindingBudget_delta, delta] using
      B.δ_lt_one
  have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta_lt_one
  have htheta : 0 ≤ theta := div_nonneg hdelta hdenDelta.le
  have htheta_lt_one : theta < 1 := by
    simpa only [cmp99UbarLogRadius, B,
      cmp99SourceUbarFineNoWindingBudget_delta, theta, delta] using logSmall
  have hdenTheta : 0 < 1 - theta := sub_pos.mpr htheta_lt_one
  unfold cmp99SourceUbarNextFineRadius
  change 0 ≤ theta + theta ^ 2 / (1 - theta) + (M : ℝ) * epsilonFine
  positivity

/-- Fully physical one-scale gradient bound.  The coarse background is the
canonical source `Ubar` generated from the fine background, and its radius is
discharged internally by the same no-winding/logarithmic budget. -/
theorem norm_covariantD0_cmp99FullSourceBlockAverage_physicalUbar_sq_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d (M * N'))
    (background : GaugeConfig d (M * N') (SUN Nc))
    (weight epsilonFine : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (noWinding : cmp99SourceUbarFineDeviationRadius d M epsilonFine <
      cmp99UbarNoWindingThreshold Nc)
    (logSmall :
      cmp99UbarLogRadius
          (cmp99SourceUbarFineNoWindingBudget
            (d := d) (M := M) (Nc := Nc) epsilonFine noWinding) < 1)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    let data := cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
      weight epsilonFine epsilonFine_nonneg noWinding fine_small
    ‖covariantD0CLM (matrixSUNAdjointModel Nc) data.nextBackground
        (cmp99FullSourceBlockAverage
          (matrixSUNAdjointModel Nc) background phi)‖ ^ 2 ≤
      2 * (((M : ℝ) ^ d)⁻¹ * (M : ℝ) ^ 2) *
          ‖covariantD0CLM (matrixSUNAdjointModel Nc) background phi‖ ^ 2 +
        2 * (cmp99SourceBlockAverageWeight M d *
          (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
            cmp99SourceUbarNextFineRadius d M epsilonFine)) ^ 2 *
            (d : ℝ)) * ‖phi‖ ^ 2 := by
  dsimp only
  apply norm_covariantD0_cmp99FullSourceBlockAverage_sq_le
    background
    (cmp99SourceRegionalScaleDataOfFineSmall hd hM Omega background
      weight epsilonFine epsilonFine_nonneg noWinding fine_small).nextBackground
    phi epsilonFine (cmp99SourceUbarNextFineRadius d M epsilonFine)
    epsilonFine_nonneg
    (cmp99SourceUbarNextFineRadius_nonneg_of_logSmall
      epsilonFine epsilonFine_nonneg noWinding logSmall)
    fine_small
  intro b
  exact norm_cmp99SourceRegionalScaleDataOfFineSmall_nextBackground_sub_one_le
    hd hM Omega background weight epsilonFine epsilonFine_nonneg noWinding
    logSmall fine_small (positiveEdgeOfPhysicalBond b)

end

end YangMills.RG
