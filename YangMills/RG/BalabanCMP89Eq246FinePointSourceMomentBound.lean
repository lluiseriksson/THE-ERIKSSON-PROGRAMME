/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246FinePointSourceStripBound
import YangMills.RG.BalabanCMP89Eq246FinePointSourceHolomorphy
import YangMills.RG.BalabanCMP89Eq248MassUniformGreenBound
import YangMills.RG.BalabanCMP89Eq245EntireAverageAliasWeightedVariation

/-!
# Scale-uniform point-source moment bound for CMP89 (2.46)

The source phase is kept separate from the target phase.  The noncentral row
quotient uses the same strictly summable `alpha = -1` weight as the sealed
Green quotient, but its opposite-momentum averaging factor is bounded
directly at `(-p,-m)` after exposing the coordinate zone.  No negation
closure of the half-open alias carrier is assumed.

Cold compiler evidence for exact source checkpoint
`a645d2b833979360f4c62c2b67a34fbec9d3704e` is recorded in Verification
Ledger Addendum 1023. The focal and its exact four-declaration audit passed in
a fresh Colab Pro+ CPU checkout without restoring project `.lake/build`.

This is only the second item of the post-synthesis Eq. (2.46) bridge. It does
not bound the full stabilized solution, construct the continuous Green
kernel, prove CMP89 (2.42), produce uniform `B0`/`delta0`, attain window 15,
move `20/41`, or construct a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- The opposite complex alias amplitude carries the same reciprocal-alias
weight as the direct amplitude. -/
theorem norm_cmp89Eq245EntireAverageAmplitude_neg_alias_le
    {d N : ℕ} (hN : 0 < N) {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    {rho : ℝ} (hrho : 0 ≤ rho)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin d → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hsmall : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude d N
        (-cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq245EntireAverageAliasStripConstant rho ^ d *
        cmp89Eq251MultidimensionalAliasWeight 1 m := by
  have hzone : ∀ mu,
      |(N : ℝ)⁻¹ * (p mu + 2 * Real.pi * (m mu : ℝ))| ≤
        3 * Real.pi / 2 := by
    intro mu
    exact abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
      hN (by
        rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
        exact hm mu) (hp mu)
  have hneg :=
    norm_cmp89Eq245EntireAverageAmplitude_scaled_alias_le_of_zone
      (d := d) (N := N) hN (m := -m) (rho := rho) hrho
      (p := -p) (fun mu => by simpa using hp mu)
      (z := -cmp89Eq248EntireAliasMomentum z m)
      (fun mu => by
        simp [cmp89Eq248EntireAliasMomentum, cmp89Eq245AliasShift, hreal mu]
        ring)
      (fun mu => by
        simpa [cmp89Eq248EntireAliasMomentum,
          cmp89Eq245AliasShift] using himag mu)
      (fun mu => by
        have heq :
            (N : ℝ)⁻¹ *
                ((-p) mu + 2 * Real.pi * ((-m) mu : ℝ)) =
              -((N : ℝ)⁻¹ *
                (p mu + 2 * Real.pi * (m mu : ℝ))) := by
          simp
          ring
        rw [heq, abs_neg]
        exact hzone mu)
      hsmall
  simpa only [cmp89Eq251MultidimensionalAliasWeight_neg] using hneg

/-- One opposite-row Green quotient uses the same summable source weight as
the direct Green quotient. -/
theorem norm_cmp89Eq246EntireAliasRowGreenQuotient_le_sourceWeight
    {N : ℕ} (hN : 0 < N) {mass rho : ℝ} (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {m : Fin 4 → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors 4 N) (hm0 : m ≠ 0)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) :
    ‖cmp89Eq245EntireAverageAmplitude 4 N
          (-cmp89Eq248EntireAliasMomentum z m) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (N : ℝ)⁻¹ mass
          (cmp89Eq248EntireAliasMomentum z m)‖ ≤
      cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
  let q : Fin 4 → ℝ := fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  let aliasZ : Fin 4 → ℂ := cmp89Eq248EntireAliasMomentum z m
  have havg :=
    norm_cmp89Eq245EntireAverageAmplitude_neg_alias_le
      hN hm hrho hp hreal himag hamplitude
  have hden :
      ((1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q) / 2 ≤
        ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖ := by
    have haliasReal : ∀ nu, (aliasZ nu).re = q nu := by
      intro nu
      simp [aliasZ, q, cmp89Eq248EntireAliasMomentum,
        cmp89Eq245AliasShift, hreal nu]
    have haliasImag : ∀ nu, |(aliasZ nu).im| ≤ rho := by
      intro nu
      simpa [aliasZ, cmp89Eq248EntireAliasMomentum,
        cmp89Eq245AliasShift] using himag nu
    simpa only [q] using
      half_momentum_gap_le_norm_cmp89Eq245EntireScaledLaplacianSymbol_of_uniformRadius
        hN hrho hradius hm hm0 hp haliasReal haliasImag
  have hqNorm : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le (pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp)
  have hqSquare : 0 < cmp89Eq251MomentumSquare q := by
    rw [← sq_cmp89Eq251EuclideanNorm]
    positivity
  have hgap :
      0 < ((1 / (3 * Real.pi)) ^ 2 *
        cmp89Eq251MomentumSquare q) / 2 := by positivity
  have hdenInv :
      ‖cmp89Eq245EntireScaledLaplacianSymbol
          4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
        (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hgap hden
  have hpower :
      cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) =
        (cmp89Eq251MomentumSquare q)⁻¹ := by
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      Real.rpow_neg hqNorm.le, Real.rpow_two,
      sq_cmp89Eq251EuclideanNorm]
  have hgapInv :
      (((1 / (3 * Real.pi)) ^ 2 *
          cmp89Eq251MomentumSquare q) / 2)⁻¹ =
        2 * (3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare q)⁻¹ := by
    field_simp [Real.pi_ne_zero, ne_of_gt hqSquare]
  have hstripNonneg :
      0 ≤ cmp89Eq245EntireAverageAliasStripConstant rho := by
    rw [cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hradial :
      ‖cmp89Eq245EntireAverageAmplitude 4 N (-aliasZ) /
          cmp89Eq245EntireScaledLaplacianSymbol
            4 (N : ℝ)⁻¹ mass aliasZ‖ ≤
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
          (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
            cmp89Eq251MultidimensionalAliasWeight 1 m) := by
    rw [norm_div, div_eq_mul_inv]
    calc
      ‖cmp89Eq245EntireAverageAmplitude 4 N (-aliasZ)‖ *
          ‖cmp89Eq245EntireScaledLaplacianSymbol
            4 (N : ℝ)⁻¹ mass aliasZ‖⁻¹ ≤
        (cmp89Eq245EntireAverageAliasStripConstant rho ^ 4 *
            cmp89Eq251MultidimensionalAliasWeight 1 m) *
          (((1 / (3 * Real.pi)) ^ 2 *
            cmp89Eq251MomentumSquare q) / 2)⁻¹ := by
          gcongr
          exact mul_nonneg (pow_nonneg hstripNonneg 4)
            (cmp89Eq251MultidimensionalAliasWeight_nonneg 1 m)
      _ = cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
          (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
            cmp89Eq251MultidimensionalAliasWeight 1 m) := by
        rw [hgapInv, hpower,
          cmp89Eq248ComplexNoncentralGreenRadialConstant_draft]
        ring
  have hredistribute :
      cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m ≤
        3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
    exact cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
      (d := 4) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num) hm0 hp
  have hconstant :
      0 ≤ cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho := by
    rw [cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  change ‖cmp89Eq245EntireAverageAmplitude 4 N (-aliasZ) /
      cmp89Eq245EntireScaledLaplacianSymbol
        4 (N : ℝ)⁻¹ mass aliasZ‖ ≤ _
  calc
    _ ≤ cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
        (cmp89Eq251EuclideanNorm q ^ ((-1 : ℝ) - 1) *
          cmp89Eq251MultidimensionalAliasWeight 1 m) := hradial
    _ ≤ cmp89Eq248ComplexNoncentralGreenRadialConstant_draft rho *
        (3 ^ (1 - (-1 : ℝ)) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m) :=
      mul_le_mul_of_nonneg_left hredistribute hconstant
    _ = cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
      rw [cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft]
      ring

/-- The complete noncentral source moment is scale-uniform; the physical
source endpoint appears only through its explicit strip-growth factor. -/
theorem norm_cmp89Eq246StabilizedAliasNoncentralFinePointSourceMoment_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (sourceEndpoint : Fin 4 → ℝ) :
    ‖cmp89Eq246StabilizedAliasNoncentralSourceMoment 4 L j mass z
        (cmp89Eq246FinePointSourceAliasVector
          4 L j z sourceEndpoint)‖ ≤
      cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
  classical
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let weight : CMP89Eq246AliasIndex 4 L j → ℝ := fun n =>
    cmp89Eq251MultidimensionalAliasWeight
      (cmp89Eq251AliasSeriesExponent 4 (-1)) n.1
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  let constant := cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho
  have hgrowth : 0 ≤ growth := by
    dsimp [growth, cmp89Eq251ContourPhaseGrowth]
    positivity
  have hconstant : 0 ≤ constant := by
    dsimp [constant, cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
      cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
      cmp89Eq245EntireAverageAliasStripConstant]
    positivity
  have hpointwise : ∀ n ∈ Finset.univ.erase central,
      ‖cmp89Eq246EntireAliasAverageRow 4 L j z n *
          cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint n /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z n‖ ≤
        growth * (constant * weight n) := by
    intro n hn
    have hnc : n ≠ central := (Finset.mem_erase.mp hn).1
    have hm0 : n.1 ≠ cmp89Eq249ZeroAlias 4 := by
      intro hz
      apply hnc
      apply Subtype.ext
      exact hz
    have hquot :=
      norm_cmp89Eq246EntireAliasRowGreenQuotient_le_sourceWeight
        (N := L ^ j)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        (mass := mass) hrho hradius n.2 hm0 hp hreal himag hamplitude
    have hsource :=
      norm_cmp89Eq246FinePointSourceAliasVector_le_growth
        himag sourceEndpoint n
    rw [norm_div, norm_mul]
    have hmul := mul_le_mul hsource hquot (norm_nonneg _) hgrowth
    simpa [cmp89Eq246EntireAliasAverageRow,
      cmp89Eq246EntireAliasFineSymbol, weight, growth, constant,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have heraseWeight :
      (∑ n ∈ Finset.univ.erase central, weight n) ≤ ∑ n, weight n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset central Finset.univ)
      (fun n _ _ => cmp89Eq251MultidimensionalAliasWeight_nonneg _ n.1)
  have hsubtype :
      (∑ n : CMP89Eq246AliasIndex 4 L j, weight n) =
        ∑ m ∈ cmp89Eq245CenteredAliasVectors 4 (L ^ j),
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent 4 (-1)) m := by
    rw [Finset.sum_subtype
      (cmp89Eq245CenteredAliasVectors 4 (L ^ j)) (fun _ => Iff.rfl)]
  have hseries :
      (∑ n : CMP89Eq246AliasIndex 4 L j, weight n) ≤
        (∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4 := by
    rw [hsubtype]
    exact cmp89Eq251CenteredMultidimensionalAliasSum_source_le_tsum_pow
      (d := 4) (L ^ j) (alpha := (-1 : ℝ)) (by norm_num) (by norm_num)
  rw [cmp89Eq246StabilizedAliasNoncentralSourceMoment]
  calc
    ‖∑ n ∈ Finset.univ.erase central,
        cmp89Eq246EntireAliasAverageRow 4 L j z n *
          cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint n /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z n‖ ≤
      ∑ n ∈ Finset.univ.erase central,
        ‖cmp89Eq246EntireAliasAverageRow 4 L j z n *
          cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint n /
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.univ.erase central,
        growth * (constant * weight n) := Finset.sum_le_sum hpointwise
    _ = growth * (constant *
        ∑ n ∈ Finset.univ.erase central, weight n) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ growth * (constant * ∑ n, weight n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heraseWeight hconstant) hgrowth
    _ ≤ growth * (constant *
        (∑' n : ℤ, cmp89Eq251OneDimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent 4 (-1)) n) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseries hconstant) hgrowth
    _ = cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft]

/-- Explicit scale-uniform coefficient for the exact source moment. -/
def cmp89Eq246FinePointSourceMomentAmplitudeBound
    (a rho : ℝ) : ℝ :=
  (Real.exp rho ^ 4 +
      cmp89Eq251CentralFineSymbolStripUpperBound rho *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) *
    cmp89Eq249CentralStabilizedComplexReciprocalBound a rho

/-- The exact stabilized source moment has no alias-cardinality loss. -/
theorem norm_cmp89Eq246StabilizedFinePointSourceSolutionMoment_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin 4 → ℝ) :
    ‖cmp89Eq246StabilizedFinePointSourceSolutionMoment
        4 L j mass a sourceEndpoint z‖ ≤
      cmp89Eq251ContourPhaseGrowth rho sourceEndpoint *
        cmp89Eq246FinePointSourceMomentAmplitudeBound a rho := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let source := cmp89Eq246FinePointSourceAliasVector 4 L j z sourceEndpoint
  let base := cmp89Eq246StabilizedAliasNoncentralSourceMoment
    4 L j mass z source
  let growth := cmp89Eq251ContourPhaseGrowth rho sourceEndpoint
  have hgrowth : 0 ≤ growth := by
    dsimp [growth, cmp89Eq251ContourPhaseGrowth]
    positivity
  have hrow :
      ‖cmp89Eq246EntireAliasAverageRow 4 L j z central‖ ≤
        Real.exp rho ^ 4 := by
    simpa [central, cmp89Eq246EntireAliasAverageRow,
      cmp89Eq248EntireAliasMomentum_zero] using
      (norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow
        (d := 4) (N := L ^ j)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        hrho (fun mu => by simpa using himag mu))
  have hsource : ‖source central‖ ≤ growth := by
    exact norm_cmp89Eq246FinePointSourceAliasVector_le_growth
      himag sourceEndpoint central
  have hcentral : ‖cmp89Eq246EntireAliasAverageRow 4 L j z central *
      source central‖ ≤ growth * Real.exp rho ^ 4 := by
    rw [norm_mul]
    have hmul := mul_le_mul hrow hsource (norm_nonneg _)
      (by positivity : 0 ≤ Real.exp rho ^ 4)
    simpa [mul_comm] using hmul
  have hfine :=
    norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
      (L := L) (j := j) hmass hrho hp hreal himag
  have hbase :
      ‖base‖ ≤ growth *
        cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
    simpa [base, source, growth] using
      norm_cmp89Eq246StabilizedAliasNoncentralFinePointSourceMoment_le
        (L := L) (j := j) (mass := mass) hrho hradius hp hreal himag
        hamplitude sourceEndpoint
  have hfineNonneg :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hnoncentral :
      ‖cmp89Eq246EntireAliasFineSymbol 4 L j mass z central * base‖ ≤
        growth * (cmp89Eq251CentralFineSymbolStripUpperBound rho *
          cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    have hcentralFine :
        cmp89Eq246EntireAliasFineSymbol 4 L j mass z central =
          cmp89Eq249CentralEntireFineSymbol 4 L j mass z := by
      simp [central, cmp89Eq246EntireAliasFineSymbol,
        cmp89Eq249CentralEntireFineSymbol,
        cmp89Eq248EntireAliasMomentum_zero]
    rw [norm_mul, hcentralFine]
    have hmul := mul_le_mul hfine hbase (norm_nonneg _) hfineNonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hnum :
      ‖cmp89Eq246EntireAliasAverageRow 4 L j z central * source central +
          cmp89Eq246EntireAliasFineSymbol 4 L j mass z central * base‖ ≤
        growth * (Real.exp rho ^ 4 +
          cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    calc
      _ ≤ ‖cmp89Eq246EntireAliasAverageRow 4 L j z central * source central‖ +
          ‖cmp89Eq246EntireAliasFineSymbol 4 L j mass z central * base‖ :=
        norm_add_le _ _
      _ ≤ growth * Real.exp rho ^ 4 +
          growth * (cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) :=
        add_le_add hcentral hnoncentral
      _ = _ := by ring
  have hrecip :=
    norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform
      (L := L) (j := j) (mass := mass) ha hrho hradius hmass hwindow
      hp hreal himag hamplitude
  have hnumNonneg :
      0 ≤ growth * (Real.exp rho ^ 4 +
        cmp89Eq251CentralFineSymbolStripUpperBound rho *
          cmp89Eq248ComplexNoncentralGreenSumBound_draft rho) := by
    refine mul_nonneg hgrowth (add_nonneg (by positivity) ?_)
    have hsum : 0 ≤ cmp89Eq248ComplexNoncentralGreenSumBound_draft rho := by
      rw [cmp89Eq248ComplexNoncentralGreenSumBound_draft,
        cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft,
        cmp89Eq248ComplexNoncentralGreenRadialConstant_draft,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    exact mul_nonneg hfineNonneg hsum
  rw [cmp89Eq246StabilizedFinePointSourceSolutionMoment_eq,
    cmp89Eq246StabilizedAliasFullSolutionMoment, norm_div,
    div_eq_mul_inv,
    cmp89Eq246FinePointSourceMomentAmplitudeBound]
  have hmul := mul_le_mul hnum hrecip (norm_nonneg _) hnumNonneg
  simpa [central, source, base, growth, mul_assoc] using hmul

end

end YangMills.RG
