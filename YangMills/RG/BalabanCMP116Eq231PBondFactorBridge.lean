/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226SourceLedger
import YangMills.RG.BalabanCMP116Eq231

/-!
# The literal equation-(2.26) `P` factor supplies the equation-(2.31) weight

The equation-(2.26) ledger contains ten units of the equation-(2.31)
cardinality rate.  If the source gap mass is covered by the two endpoints of
the selected bonds, two units pay for the gap term and two units pay for the
cardinality term in `cmp116Eq231PWeight`; six units remain in reserve.

This module records only that source-facing comparison.  It does not prove the
pointwise fluctuation-residual estimate carrying the `epsilon2` amplitude.
-/

namespace YangMills.RG

/-- The source rate is nonnegative whenever the literal equation-(2.31)
bracket inequality holds. -/
theorem cmp116Eq226PSourceRate_nonneg_of_sourceBracket
    (localizationScale : ℕ)
    (gamma2 epsilon1 gk : ℝ)
    (hsourceBracket :
      4 * ((localizationScale : ℝ) ^ 4) *
          Real.exp (-(gamma2 * epsilon1 ^ 2 / (10 * gk ^ 2))) ≤
        gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2)) :
    0 ≤ cmp116Eq226PSourceRate gamma2 epsilon1 gk := by
  have hlhs :
      0 ≤
        4 * ((localizationScale : ℝ) ^ 4) *
          Real.exp (-(gamma2 * epsilon1 ^ 2 / (10 * gk ^ 2))) := by
    positivity
  simpa [cmp116Eq226PSourceRate] using hlhs.trans hsourceBracket

/-- The literal equation-(2.26) `P` penalty is bounded by the complete
equation-(2.31) weight once endpoint coverage bounds the normalized gap mass.

The source bound `gapMass ≤ 2 * |P|` is deliberately weaker than the
scale-normalized endpoint-cover theorem already available in
`BalabanCMP116Eq231`: it is exactly the algebraic input needed here. -/
theorem cmp116Eq226PBondFactor_le_eq231PWeight_of_gapMass_le_two_mul_card
    {σ ιD ιP β : Type*}
    (gamma2 epsilon1 gk : ℝ)
    (gapMass : σ → ιD → ℝ)
    (pBonds : σ → ιD → ιP → Finset β)
    (Z : σ) (D : ιD) (P : ιP)
    (hrate_nonneg :
      0 ≤ cmp116Eq226PSourceRate gamma2 epsilon1 gk)
    (hgap :
      gapMass Z D ≤ 2 * ((pBonds Z D P).card : ℝ)) :
    cmp116Eq226PBondFactor gamma2 epsilon1 gk (pBonds Z D P) ≤
      cmp116Eq231PWeight
        (cmp116Eq226PSourceRate gamma2 epsilon1 gk)
        gapMass pBonds Z D P := by
  rw [cmp116Eq226PBondFactor_eq_exp_ten_mul_sourceRate]
  unfold cmp116Eq231PWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcard_nonneg : 0 ≤ ((pBonds Z D P).card : ℝ) := by
    positivity
  have hgap_scaled :
      cmp116Eq226PSourceRate gamma2 epsilon1 gk * gapMass Z D ≤
        cmp116Eq226PSourceRate gamma2 epsilon1 gk *
          (2 * ((pBonds Z D P).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap hrate_nonneg
  nlinarith

/-- Source-specialized form of the comparison: coverage of every gap cube by
one of the two endpoints of a selected bond produces the required gap-mass
bound.  The division by `localizationScale^4` is retained in the resulting
Eq. (2.31) weight; `1 ≤ localizationScale` is used only to weaken the endpoint
count to the algebraic comparison above. -/
theorem cmp116Eq226PBondFactor_le_eq231PWeight_of_endpointCover
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (gamma2 epsilon1 gk : ℝ)
    (gapCubes : σ → ιD → Finset Cube)
    (localizationScale : ℕ)
    (Z : σ) (D : ιD)
    (P : Finset (Cube × Fin 4))
    (endpoint : (Cube × Fin 4) × Fin 2 → Cube)
    (hrate_nonneg :
      0 ≤ cmp116Eq226PSourceRate gamma2 epsilon1 gk)
    (hlocalizationScale : 1 ≤ localizationScale)
    (hcover :
      gapCubes Z D ⊆
        (P ×ˢ (Finset.univ : Finset (Fin 2))).image endpoint) :
    cmp116Eq226PBondFactor gamma2 epsilon1 gk P ≤
      cmp116Eq231PWeight
        (cmp116Eq226PSourceRate gamma2 epsilon1 gk)
        (cmp116Eq231GapMass gapCubes localizationScale)
        (fun _ _ P => P) Z D P := by
  have hscaled :
      cmp116Eq231GapMass gapCubes localizationScale Z D ≤
        (2 * (P.card : ℝ)) / ((localizationScale : ℝ) ^ 4) :=
    cmp116Eq231_gapMass_le_two_mul_pBonds_card_div_scale4_of_endpointCover
      gapCubes localizationScale Z D P endpoint hcover
  have hden :
      1 ≤ ((localizationScale : ℝ) ^ 4) := by
    have hscale_real : 1 ≤ (localizationScale : ℝ) := by
      exact_mod_cast hlocalizationScale
    nlinarith [sq_nonneg ((localizationScale : ℝ) ^ 2 - 1)]
  have hweak :
      (2 * (P.card : ℝ)) / ((localizationScale : ℝ) ^ 4) ≤
        2 * (P.card : ℝ) := by
    exact div_le_self (by positivity) hden
  exact
    cmp116Eq226PBondFactor_le_eq231PWeight_of_gapMass_le_two_mul_card
      gamma2 epsilon1 gk
      (cmp116Eq231GapMass gapCubes localizationScale)
      (fun _ _ P => P) Z D P hrate_nonneg
      (hscaled.trans hweak)

end YangMills.RG
