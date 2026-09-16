/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientFourContourUniformBudget
import YangMills.RG.BalabanCMP102AmbientWilsonLineThirdJetBound

/-!
# Physical third jets of the CMP98 four-contour deviation

The literal four-contour deviation has already been identified with one
ordered Wilson line along the source contour word, minus the identity.
For every positive derivative order the constant disappears.  This file
therefore transfers the source-generated Wilson-line jet bound without
introducing a second four-factor majorant.

The terminal budget uses the source length `2 * (d + 1) * M`; it is
independent of the fine periodic volume.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
  [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientFourContourThirdJetCMLSeminormed (n : ℕ) :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc [×n]→L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousMultilinearMap.seminormedAddCommGroup

/-- At every positive order, the derivative of the literal four-contour
deviation is exactly the derivative of its source Wilson-line word. -/
theorem iteratedFDeriv_cmp98UbarAmbientDeviationMatrix_eq_sourceFourContour
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (i : ℕ) (hi : i ≠ 0) :
    iteratedFDeriv ℝ i
        (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z =
      iteratedFDeriv ℝ i
        (fun W =>
          cmp98AmbientWilsonLineMatrix U W
            (cmp98SourceFourContourEdges (Nc := Nc) b x)) Z := by
  let line :
      PhysicalAmbientMatrixTangent d (M * N') Nc →
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun W =>
      cmp98AmbientWilsonLineMatrix U W
        (cmp98SourceFourContourEdges (Nc := Nc) b x)
  change
    iteratedFDeriv ℝ i
        (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z =
      iteratedFDeriv ℝ i line Z
  have hline : ContDiffAt ℝ i line Z :=
    (analyticAt_cmp98AmbientWilsonLineMatrix U Z
      (cmp98SourceFourContourEdges (Nc := Nc) b x)).contDiffAt.of_le
      le_top
  have hconst :
      ContDiffAt ℝ i
        (fun _ : PhysicalAmbientMatrixTangent d (M * N') Nc =>
          (1 : Matrix (Fin Nc) (Fin Nc) ℂ)) Z :=
    contDiffAt_const
  have hfun :
      (fun W : PhysicalAmbientMatrixTangent d (M * N') Nc =>
        cmp98UbarAmbientDeviationMatrix U b x W) =
      line - fun _ => (1 : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    funext W
    exact cmp98UbarAmbientDeviationMatrix_eq_sourceFourContour U b x W
  rw [hfun, iteratedFDeriv_sub_apply hline hconst,
    iteratedFDeriv_const_of_ne hi]
  exact sub_zero _

/-- Exact-length order-three jet bound for the physical four-contour
deviation. -/
theorem norm_iteratedFDeriv_cmp98UbarAmbientDeviationMatrix_le_lineBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r : NNReal)
    (hZ : ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
      ‖Z (physicalBondOfEdge e)‖ < r)
    (i : ℕ) (hi0 : i ≠ 0) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i
        (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z‖ ≤
      cmp102AmbientWilsonLineOrderThreeJetBudget
        (Nc := Nc) r
        (cmp98SourceFourContourEdges (Nc := Nc) b x).length := by
  rw [iteratedFDeriv_cmp98UbarAmbientDeviationMatrix_eq_sourceFourContour
    U b x Z i hi0]
  exact
    norm_iteratedFDeriv_cmp98AmbientWilsonLineMatrix_le_orderThreeBudget
      U Z (cmp98SourceFourContourEdges (Nc := Nc) b x) r hZ i hi3

/-- The common Wilson-line jet budget is monotone in contour length. -/
theorem cmp102AmbientWilsonLineOrderThreeJetBudget_monotone
    (r : NNReal) {n m : ℕ} (hnm : n ≤ m) :
    cmp102AmbientWilsonLineOrderThreeJetBudget (Nc := Nc) r n ≤
      cmp102AmbientWilsonLineOrderThreeJetBudget (Nc := Nc) r m := by
  have hEdgeOne :
      1 ≤ cmp102AmbientEdgeOrderThreeJetBudget (Nc := Nc) r :=
    (one_le_cmp102AmbientEdgeValueBudget r.2).trans (le_max_left _ _)
  have hFactor :
      1 ≤ 8 * cmp102AmbientEdgeOrderThreeJetBudget (Nc := Nc) r := by
    nlinarith
  induction m with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact le_rfl
  | succ m ih =>
      by_cases hnm' : n = m + 1
      · subst n
        exact le_rfl
      · have hnm0 : n ≤ m := by omega
        calc
          cmp102AmbientWilsonLineOrderThreeJetBudget
                (Nc := Nc) r n
              ≤ cmp102AmbientWilsonLineOrderThreeJetBudget
                  (Nc := Nc) r m := ih hnm0
          _ ≤ cmp102AmbientWilsonLineOrderThreeJetBudget
                  (Nc := Nc) r (m + 1) := by
            rw [cmp102AmbientWilsonLineOrderThreeJetBudget]
            have hnonneg :=
              cmp102AmbientWilsonLineOrderThreeJetBudget_nonneg
                (Nc := Nc) r m
            nlinarith

/-- Uniform source-length budget for every positive jet through order
three of the local four-contour deviation. -/
def cmp102SourceFourContourOrderThreeJetBudget
    (d M : ℕ) (r : NNReal) : ℝ :=
  cmp102AmbientWilsonLineOrderThreeJetBudget
    (Nc := Nc) r (cmp102SourceFourContourMaxLength d M)

/-- Every positive jet through order three of the literal local deviation
has a source-length bound independent of the fine periodic volume. -/
theorem norm_iteratedFDeriv_cmp98UbarAmbientDeviationMatrix_le_sourceLengthBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r : NNReal) (hZ : ‖Z‖ < r)
    (i : ℕ) (hi0 : i ≠ 0) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i
        (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z‖ ≤
      cmp102SourceFourContourOrderThreeJetBudget
        (Nc := Nc) d M r := by
  have hpath :
      ∀ e ∈ cmp98SourceFourContourEdges (Nc := Nc) b x,
        ‖Z (physicalBondOfEdge e)‖ < r := by
    intro e _he
    exact (norm_physicalAmbientMatrixTangent_apply_le
      Z (physicalBondOfEdge e)).trans_lt hZ
  exact
    (norm_iteratedFDeriv_cmp98UbarAmbientDeviationMatrix_le_lineBudget
      U b x Z r hpath i hi0 hi3).trans
      (cmp102AmbientWilsonLineOrderThreeJetBudget_monotone
        (Nc := Nc) r
        (cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx))

/-- In particular, the literal third derivative has the uniform physical
source-length budget. -/
theorem norm_iteratedFDeriv_three_cmp98UbarAmbientDeviationMatrix_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1)
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (r : NNReal) (hZ : ‖Z‖ < r) :
    ‖iteratedFDeriv ℝ 3
        (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z‖ ≤
      cmp102SourceFourContourOrderThreeJetBudget
        (Nc := Nc) d M r :=
  norm_iteratedFDeriv_cmp98UbarAmbientDeviationMatrix_le_sourceLengthBudget
    U b x hx Z r hZ 3 (by norm_num) (by norm_num)

end

end YangMills.RG
