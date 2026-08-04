/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalGaugeFlatPoincare

/-!
# The volume-uniform Poincaré WALL — the CT route's obstruction, as theorems
(`hRpoly` campaign — the post-P4-ADJ lane registered in ledger Addendum 492)

The fixed-volume Combes–Thomas endpoint (`CT_fixedVolume`, Addendum 476)
runs on the coercivity constant `c = min 1 a / CP`, where `CP` is a flat
Hodge/block-Poincaré constant.  The audit theorem
`flatGaugeHodgePoincare_constantSector_lower_bound` already showed, at
fixed volume, that ANY such constant obeys `L^d / L^2 ≤ CP` under the
current unscaled line-integral block normalization.  This module turns
that audit into the honest VOLUME-UNIFORM obstruction:

* **`exists_pos_constantSector`** — the nonzero constant-sector witness
  (`Nc ≥ 2`; for `Nc = 1`, `su(1) = 0` and the sector is empty — recorded
  as a hypothesis, not hidden);
* **`flatPoincare_constantSector_lower_bound`** — the wall with the
  explicit witness discharged: `L^d / L^2 ≤ CP`;
* **`flatPoincare_linear_lower_bound`** — the linear form `L ≤ CP` for
  `d ≥ 3` (the physical case `d = 4` included; `d = 2` is exactly the
  scale-invariant exemption, `L^0 = 1`, and is NOT claimed);
* **`flatPoincare_coercivity_upper_bound`** — the CT coercivity through
  this route obeys `min 1 a / CP ≤ min 1 a * L^2 / L^d`;
* **`no_volumeUniform_coercivity_via_flatPoincare`** — THE WALL: for
  `d ≥ 3`, `Nc ≥ 2`, no `c₀ > 0` survives all volumes through per-volume
  flat Poincaré constants (any such `c₀` is forced `≤ 0`);
* **`VolumeUniformFlatPoincareGate`** + **`volumeUniformFlatPoincareGate_false`**
  — the uniform-constant gate, stated with the constant BEFORE the volume
  quantifier (the Addendum-487/491 quantifier-order lesson), is PROVED
  FALSE for `d ≥ 3`, `Nc ≥ 2`;
* **`perVolume_flatPoincare_family`** — non-vacuity of the obstruction's
  hypothesis family: the per-volume constants DO exist (the obstruction
  kills a real route, not an empty one).

**Honest scope.**  The wall is a theorem about THE FLAT BLOCK-POINCARÉ
ROUTE under the CURRENT block-map normalization (`linAvg` sends constants
to `L` times constants; the `L^2` in the sector identity is that choice).
It does NOT prove that no volume-uniform Combes–Thomas bound exists; it
proves that the route consumed by `CT_fixedVolume` cannot supply one for
`d ≥ 3`.  Any volume-uniform continuation must either rescale the block
map (changing the harmonic-sector normalization and re-auditing), quotient
the constant/harmonic sector before the Poincaré step, or route the
coercivity through the interacting Hessian directly.  NOT `hRpoly`, NOT
the mass gap; Clay distance unchanged, ~0% (<0.1%).

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open Matrix Module

/-! ## The nonzero constant-sector witness (`Nc ≥ 2`) -/

/-- For `Nc ≥ 2` the coordinate space `SUNLieCoord Nc` is a Euclidean space
of positive dimension, so the direction-wise constant sector of the fine
cochain space contains a vector family of positive total norm.  (For
`Nc = 1`, `su(1) = 0`: the sector is trivial and the wall argument does
not start — hence the explicit hypothesis.) -/
theorem exists_pos_constantSector (d Nc : ℕ) [NeZero d] (hNc : 2 ≤ Nc) :
    ∃ v : Fin d → SUNLieCoord Nc, 0 < ∑ i : Fin d, ‖v i‖ ^ 2 := by
  have hdim : 0 < Nc ^ 2 - 1 := by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    omega
  refine ⟨fun _ => EuclideanSpace.single ⟨0, hdim⟩ (1 : ℝ), ?_⟩
  have hnorm : ∀ i : Fin d,
      ‖(EuclideanSpace.single (⟨0, hdim⟩ : Fin (Nc ^ 2 - 1))
          (1 : ℝ) : SUNLieCoord Nc)‖ ^ 2 = 1 := by
    intro i
    rw [EuclideanSpace.norm_single]
    norm_num
  rw [Finset.sum_congr rfl (fun i _ => hnorm i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hd

/-! ## The wall at fixed volume, witness discharged -/

/-- **The Poincaré wall, fixed volume** (`Nc ≥ 2`): every flat Hodge/block
Poincaré constant obeys `L^d / L^2 ≤ CP` under the current block-map
normalization.  This is `flatGaugeHodgePoincare_constantSector_lower_bound`
with the constant-sector witness discharged. -/
theorem flatPoincare_constantSector_lower_bound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    {CP : ℝ} (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) :
    ((L : ℝ) ^ d / (L : ℝ) ^ 2) ≤ CP := by
  obtain ⟨v, hv⟩ := exists_pos_constantSector d Nc hNc
  exact flatGaugeHodgePoincare_constantSector_lower_bound ρ hP v hv

/-- **The wall, linear form** (`d ≥ 3`, `Nc ≥ 2`): `L ≤ CP`.  For the
physical dimension `d = 4` the true forced growth is `L^2`; the linear
form is all the divergence the volume-uniform obstruction needs.  The
case `d = 2` is the scale-invariant exemption (`L^d / L^2 = 1`) and is
deliberately NOT covered. -/
theorem flatPoincare_linear_lower_bound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (hd : 3 ≤ d) (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    {CP : ℝ} (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) :
    (L : ℝ) ≤ CP := by
  have hwall := flatPoincare_constantSector_lower_bound hNc ρ hP
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hLne : (L : ℝ) ≠ 0 := by positivity
  have hpow : ((L : ℝ) ^ d / (L : ℝ) ^ 2) = (L : ℝ) ^ (d - 2) :=
    (pow_sub₀ (L : ℝ) hLne (by omega)).symm
  have hgrow : (L : ℝ) ≤ (L : ℝ) ^ (d - 2) := by
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ (d - 2) := by
          apply pow_le_pow_right₀ hL1
          omega
  calc (L : ℝ) ≤ (L : ℝ) ^ (d - 2) := hgrow
    _ = (L : ℝ) ^ d / (L : ℝ) ^ 2 := hpow.symm
    _ ≤ CP := hwall

/-! ## The CT coercivity through this route dies with the volume -/

/-- The Combes–Thomas coercivity constant `min 1 a / CP` consumed by
`CT_fixedVolume` obeys `min 1 a / CP ≤ min 1 a * L^2 / L^d` through any
flat Poincaré constant (`Nc ≥ 2`).  For `d ≥ 3` the right side vanishes
as `L → ∞`: the route's rate is NOT volume-uniform. -/
theorem flatPoincare_coercivity_upper_bound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    {a CP : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) :
    min 1 a / CP ≤ min 1 a * (L : ℝ) ^ 2 / (L : ℝ) ^ d := by
  have hwall := flatPoincare_constantSector_lower_bound hNc ρ hP
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hsector : (0 : ℝ) < (L : ℝ) ^ d / (L : ℝ) ^ 2 := by positivity
  have hmin : (0 : ℝ) ≤ min 1 a := le_min zero_le_one ha.le
  have h1 : min 1 a / CP ≤ min 1 a / ((L : ℝ) ^ d / (L : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left hmin hsector hwall
  calc min 1 a / CP
      ≤ min 1 a / ((L : ℝ) ^ d / (L : ℝ) ^ 2) := h1
    _ = min 1 a * (L : ℝ) ^ 2 / (L : ℝ) ^ d := by
        rw [div_div_eq_mul_div]

/-! ## THE WALL: no volume-uniform coercivity through per-volume constants -/

/-- **The volume-uniform Poincaré wall** (`d ≥ 3`, `Nc ≥ 2`): if a single
`c₀` is dominated, at EVERY volume `L + 1`, by the CT coercivity
`min 1 a / CP L` of some per-volume flat Poincaré constant, then
`c₀ ≤ 0`.  Equivalently: no positive coercivity survives all volumes
through this route.  The hypothesis family is NON-VACUOUS
(`perVolume_flatPoincare_family`): the obstruction kills a real route. -/
theorem no_volumeUniform_coercivity_via_flatPoincare
    {d N' Nc : ℕ}
    [NeZero d] [NeZero N'] [NeZero Nc]
    (hd : 3 ≤ d) (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    {a c₀ : ℝ} (ha : 0 < a)
    (h : ∀ L : ℕ, ∃ CP : ℝ,
        FlatGaugeHodgePoincare d (L + 1) N' Nc ρ CP ∧
          c₀ ≤ min 1 a / CP) :
    c₀ ≤ 0 := by
  by_contra hc₀
  push_neg at hc₀
  have hminpos : (0 : ℝ) < min 1 a := lt_min one_pos ha
  obtain ⟨n, hn⟩ := exists_nat_gt (min 1 a / c₀)
  obtain ⟨CP, hP, hle⟩ := h n
  have hCPpos : (0 : ℝ) < CP := hP.1
  have hlin : ((n : ℝ) + 1) ≤ CP := by
    have := flatPoincare_linear_lower_bound hd hNc ρ hP
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hbig : min 1 a / c₀ < CP :=
    lt_of_lt_of_le (hn.trans_le (by linarith)) hlin
  have hcontra : min 1 a / CP < c₀ := by
    rw [div_lt_iff₀ hCPpos]
    rw [div_lt_iff₀ hc₀] at hbig
    linarith [hbig]
  linarith [hle, hcontra]

/-! ## The uniform-constant gate is FALSE -/

/-- The volume-uniform flat Poincaré gate: ONE constant `CP` valid at every
volume, the constant quantified BEFORE the volume (the Addendum-487/491
quantifier-order discipline; the reversed order is the trivially satisfiable
per-volume statement, which is exactly what the wall theorems consume). -/
def VolumeUniformFlatPoincareGate
    (d N' Nc : ℕ) [NeZero d] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) : Prop :=
  ∃ CP : ℝ, 0 < CP ∧
    ∀ L : ℕ, FlatGaugeHodgePoincare d (L + 1) N' Nc ρ CP

/-- **The gate is FALSE** for `d ≥ 3`, `Nc ≥ 2`: the wall forces
`L + 1 ≤ CP` at every volume, and no real number dominates every natural.
This is the registered NEGATIVE result of the volume-uniform lane: the
flat block-Poincaré route, as consumed by `CT_fixedVolume`, terminates
here.  A volume-uniform CT must be re-routed (rescaled block map,
sector quotient, or interacting-Hessian coercivity). -/
theorem volumeUniformFlatPoincareGate_false
    {d N' Nc : ℕ}
    [NeZero d] [NeZero N'] [NeZero Nc]
    (hd : 3 ≤ d) (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) :
    ¬ VolumeUniformFlatPoincareGate d N' Nc ρ := by
  rintro ⟨CP, _hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt CP
  have hlin : ((n : ℝ) + 1) ≤ CP := by
    have := flatPoincare_linear_lower_bound hd hNc ρ (hall n)
    simpa [Nat.cast_add, Nat.cast_one] using this
  linarith [hn, hlin]

/-! ## Non-vacuity of the per-volume family -/

/-- The per-volume flat Poincaré constants EXIST at every volume: the
wall's hypothesis family is non-vacuous, so the obstruction theorems
above kill a real route, not an empty one. -/
theorem perVolume_flatPoincare_family
    (d N' Nc : ℕ) [NeZero d] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    ∀ L : ℕ, ∃ CP : ℝ,
      FlatGaugeHodgePoincare d (L + 1) N' Nc ρ CP := by
  intro L
  exact exists_flatGaugeHodgePoincare
    (d := d) (L := L + 1) (N' := N') (Nc := Nc) ρ

end YangMills.RG
