/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalGramKernel

/-!
# Concrete locality of the flat curl term `D1†D1`
(`hRpoly` campaign — P4-CT, owner obligation 2, first shell term)

The first concrete stencil input to the Gram-kernel calculus: at the trivial
background, the plaquette curl `D1 = covariantD1CLM ρ triv` couples the bond
probe `δ_p v` only to plaquettes having `p` among their four bond slots
(`covariantD1CLM_trivial_apply`).  Since all four slots of a plaquette lie
within `physicalBondDist ≤ 1` of the base slot `(site, dir1)`, two probes at
bond distance `> 2` have orthogonal `D1`-images, and each probe image has at
most `4d` supporting plaquettes with per-plaquette value `≤ ‖v‖` per matching
slot.  Through `adjointCompSelf_finiteRange` / `adjointCompSelf_kernelBound`
this yields, for the CONCRETE operator and the CONCRETE distance:

* `flatCurl_adjointCompSelf_finiteRange` —
  `PhysicalCovarianceFiniteRange (D1†D1) physicalBondDist 2`;
* `flatCurl_adjointCompSelf_kernelBound` —
  `PhysicalCovarianceKernelBound (D1†D1) (fun _ _ => ((4d)²))`.

**Honest scope.**  This is ONE of the three shell terms.  The backward
divergence (`div†div`) and the block constraint (`a·Q†Q`) are the next
bricks; then `Sigma := 0`, CT3, CT4, the positive-`θ` witness, and the
`CT_fixedVolume` endpoint.  Constants are explicit but deliberately crude
(`4d`, range `2`); sharpness is not required by the CT budget.  Nothing here
is `hRpoly`, mass gap, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d N Nc : ℕ} [NeZero N]

/-! ## Geometry: plaquette bond slots sit within distance 1 of the base -/

/-- The four bond slots of a plaquette, in the order of the trivial curl
stencil `covariantD1CLM_trivial_apply`. -/
def plaquetteBondSlots (π : ConcretePlaquette d N) : Fin 4 → PhysicalBond d N
  | ⟨0, _⟩ => (π.site, π.dir1)
  | ⟨1, _⟩ => (FinBox.shift π.site π.dir1, π.dir2)
  | ⟨2, _⟩ => (FinBox.shift π.site π.dir2, π.dir1)
  | ⟨3, _⟩ => (π.site, π.dir2)

/-- One coordinate step has circular distance at most 1. -/
theorem finTorusDist_succ_le (a : Fin N) :
    finTorusDist a ⟨(a.val + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ ≤ 1 := by
  unfold finTorusDist zmodCircDist
  have hcast : (((a.val + 1) % N : ℕ) : ZMod N) = ((a.val : ℕ) : ZMod N) + 1 := by
    rw [ZMod.natCast_mod]
    push_cast
    ring
  have harg : ((a.val : ℕ) : ZMod N) - (((a.val + 1) % N : ℕ) : ZMod N)
      = -1 := by
    rw [hcast]
    ring
  rw [harg]
  have hneg : zmodCircVal (-1 : ZMod N) = zmodCircVal (1 : ZMod N) :=
    zmodCircVal_neg 1
  rw [hneg]
  calc zmodCircVal (1 : ZMod N) ≤ (1 : ZMod N).val := zmodCircVal_le_val _
    _ = ((1 : ℕ) : ZMod N).val := by rw [Nat.cast_one]
    _ = 1 % N := ZMod.val_natCast N 1
    _ ≤ 1 := Nat.mod_le 1 N

/-- Shifting one direction moves a site by Chebyshev distance at most 1. -/
theorem finBoxDist_shift_le (x : FinBox d N) (j : Fin d) :
    finBoxDist x (FinBox.shift x j) ≤ 1 := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _
  by_cases hij : i = j
  · subst hij
    have hcoord : FinBox.shift x i i = ⟨(x i + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ := by
      unfold FinBox.shift
      rw [if_pos rfl]
    rw [hcoord]
    exact finTorusDist_succ_le (x i)
  · have hcoord : FinBox.shift x j i = x i := by
      unfold FinBox.shift
      rw [if_neg hij]
    rw [hcoord, finTorusDist_self]
    exact Nat.zero_le _

/-- The direction indicator is at most 1. -/
theorem dir_indicator_le_one (μ ν : Fin d) :
    (if μ = ν then 0 else 1) ≤ 1 := by
  by_cases h : μ = ν
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]

/-- Every bond slot of a plaquette lies within distance 1 of the base slot
`(site, dir1)`. -/
theorem plaquetteBondSlots_dist_base_le (π : ConcretePlaquette d N) (k : Fin 4) :
    physicalBondDist (plaquetteBondSlots π k) (π.site, π.dir1) ≤ 1 := by
  fin_cases k
  · -- (site, dir1) itself
    show physicalBondDist (π.site, π.dir1) (π.site, π.dir1) ≤ 1
    rw [physicalBondDist_self]
    exact Nat.zero_le _
  · -- (shift site dir1, dir2)
    show physicalBondDist (FinBox.shift π.site π.dir1, π.dir2) (π.site, π.dir1) ≤ 1
    apply max_le
    · show finBoxDist (FinBox.shift π.site π.dir1) π.site ≤ 1
      rw [finBoxDist_comm]
      exact finBoxDist_shift_le π.site π.dir1
    · exact dir_indicator_le_one _ _
  · -- (shift site dir2, dir1)
    show physicalBondDist (FinBox.shift π.site π.dir2, π.dir1) (π.site, π.dir1) ≤ 1
    apply max_le
    · show finBoxDist (FinBox.shift π.site π.dir2) π.site ≤ 1
      rw [finBoxDist_comm]
      exact finBoxDist_shift_le π.site π.dir2
    · exact dir_indicator_le_one _ _
  · -- (site, dir2)
    show physicalBondDist (π.site, π.dir2) (π.site, π.dir1) ≤ 1
    apply max_le
    · show finBoxDist π.site π.site ≤ 1
      rw [finBoxDist_self]
      exact Nat.zero_le _
    · exact dir_indicator_le_one _ _

/-- Any two bond slots of one plaquette lie within distance 2 (via the base
slot and the triangle inequality). -/
theorem plaquetteBondSlots_dist_le (π : ConcretePlaquette d N) (k l : Fin 4) :
    physicalBondDist (plaquetteBondSlots π k) (plaquetteBondSlots π l) ≤ 2 := by
  calc physicalBondDist (plaquetteBondSlots π k) (plaquetteBondSlots π l)
      ≤ physicalBondDist (plaquetteBondSlots π k) (π.site, π.dir1) +
        physicalBondDist ((π.site, π.dir1) : PhysicalBond d N)
          (plaquetteBondSlots π l) :=
        physicalBondDist_triangle _ _ _
    _ ≤ 1 + 1 := by
        apply Nat.add_le_add (plaquetteBondSlots_dist_base_le π k)
        rw [physicalBondDist_comm]
        exact plaquetteBondSlots_dist_base_le π l
    _ = 2 := rfl

/-! ## The probe image of the trivial curl -/

section TrivialCurl

variable [NeZero d] [NeZero Nc]

/-- The trivial curl of a single-bond probe, slot by slot. -/
theorem covariantD1_trivial_single_apply
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (π : ConcretePlaquette d N) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) π =
      (if ((π.site, π.dir1) : PhysicalBond d N) = p then v else 0)
      + (if ((FinBox.shift π.site π.dir1, π.dir2) : PhysicalBond d N) = p then v else 0)
      - (if ((FinBox.shift π.site π.dir2, π.dir1) : PhysicalBond d N) = p then v else 0)
      - (if ((π.site, π.dir2) : PhysicalBond d N) = p then v else 0) := by
  rw [covariantD1CLM_trivial_apply]
  rfl

/-- If no slot of `π` equals `p`, the probe image vanishes at `π`. -/
theorem covariantD1_trivial_single_eq_zero
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (π : ConcretePlaquette d N)
    (h : ∀ k : Fin 4, plaquetteBondSlots π k ≠ p) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) π = 0 := by
  rw [covariantD1_trivial_single_apply]
  have h0 : ¬(((π.site, π.dir1) : PhysicalBond d N) = p) := h 0
  have h1 : ¬(((FinBox.shift π.site π.dir1, π.dir2) : PhysicalBond d N) = p) := h 1
  have h2 : ¬(((FinBox.shift π.site π.dir2, π.dir1) : PhysicalBond d N) = p) := h 2
  have h3 : ¬(((π.site, π.dir2) : PhysicalBond d N) = p) := h 3
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
  simp

/-- **Gram orthogonality for the trivial curl**: probes at bond distance
`> 2` have orthogonal curl images. -/
theorem covariantD1_trivial_gram_orthogonal
    (ρ : SUNAdjointModel Nc) (p q : PhysicalBond d N) (v w : SUNLieCoord Nc)
    (hfar : 2 < physicalBondDist q p) :
    inner ℝ (covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
      (covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q w)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro π _
  by_cases hp : ∀ k : Fin 4, plaquetteBondSlots π k ≠ p
  · rw [covariantD1_trivial_single_eq_zero ρ p v π hp, inner_zero_left]
  · push_neg at hp
    obtain ⟨k, hk⟩ := hp
    by_cases hq : ∀ l : Fin 4, plaquetteBondSlots π l ≠ q
    · rw [covariantD1_trivial_single_eq_zero ρ q w π hq, inner_zero_right]
    · push_neg at hq
      obtain ⟨l, hl⟩ := hq
      exfalso
      have hd : physicalBondDist q p ≤ 2 := by
        rw [← hk, ← hl]
        exact plaquetteBondSlots_dist_le π l k
      omega

/-! ## Probe-image norm bound -/

/-- `ℓ² ≤ ℓ¹` on finite `PiLp 2` blocks. -/
theorem piLp_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (f : PiLp 2 (fun _ : ι => SUNLieCoord Nc)) :
    ‖f‖ ≤ ∑ i, ‖f i‖ := by
  have hsq : ‖f‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ f
  have hle : ∑ i, ‖f i‖ ^ 2 ≤ (∑ i, ‖f i‖) ^ 2 := by
    have hterm : ∀ i : ι, i ∈ Finset.univ → ‖f i‖ ^ 2 ≤ ‖f i‖ * ∑ j, ‖f j‖ := by
      intro i _
      rw [sq]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)
    calc ∑ i, ‖f i‖ ^ 2 ≤ ∑ i, ‖f i‖ * ∑ j, ‖f j‖ :=
        Finset.sum_le_sum hterm
      _ = (∑ i, ‖f i‖) * ∑ j, ‖f j‖ := by rw [← Finset.sum_mul]
      _ = (∑ i, ‖f i‖) ^ 2 := (sq _).symm
  have h2 : ‖f‖ ^ 2 ≤ (∑ i, ‖f i‖) ^ 2 := by rw [hsq]; exact hle
  have h1 : (0:ℝ) ≤ ‖f‖ := norm_nonneg f
  have h0 : (0:ℝ) ≤ ∑ i, ‖f i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg (f i))
  have hs := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h0] at hs

set_option maxHeartbeats 800000 in
/-- Per-plaquette value bound: at most one `‖v‖` per matching slot. -/
theorem covariantD1_trivial_single_norm_apply_le
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (π : ConcretePlaquette d N) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) π‖ ≤
      ∑ k : Fin 4, (if plaquetteBondSlots π k = p then ‖v‖ else 0) := by
  rw [covariantD1_trivial_single_apply]
  set t0 := (if ((π.site, π.dir1) : PhysicalBond d N) = p then v else 0) with ht0
  set t1 := (if ((FinBox.shift π.site π.dir1, π.dir2) : PhysicalBond d N) = p
    then v else 0) with ht1
  set t2 := (if ((FinBox.shift π.site π.dir2, π.dir1) : PhysicalBond d N) = p
    then v else 0) with ht2
  set t3 := (if ((π.site, π.dir2) : PhysicalBond d N) = p then v else 0) with ht3
  have hchain : ‖t0 + t1 - t2 - t3‖ ≤ ‖t0‖ + ‖t1‖ + ‖t2‖ + ‖t3‖ := by
    have h1 := norm_sub_le (t0 + t1 - t2) t3
    have h2 := norm_sub_le (t0 + t1) t2
    have h3 := norm_add_le t0 t1
    linarith
  have e0 : ‖t0‖ = (if ((π.site, π.dir1) : PhysicalBond d N) = p then ‖v‖ else 0) := by
    rw [ht0]
    by_cases h : ((π.site, π.dir1) : PhysicalBond d N) = p
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, norm_zero]
  have e1 : ‖t1‖ = (if ((FinBox.shift π.site π.dir1, π.dir2) : PhysicalBond d N) = p
      then ‖v‖ else 0) := by
    rw [ht1]
    by_cases h : ((FinBox.shift π.site π.dir1, π.dir2) : PhysicalBond d N) = p
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, norm_zero]
  have e2 : ‖t2‖ = (if ((FinBox.shift π.site π.dir2, π.dir1) : PhysicalBond d N) = p
      then ‖v‖ else 0) := by
    rw [ht2]
    by_cases h : ((FinBox.shift π.site π.dir2, π.dir1) : PhysicalBond d N) = p
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, norm_zero]
  have e3 : ‖t3‖ = (if ((π.site, π.dir2) : PhysicalBond d N) = p then ‖v‖ else 0) := by
    rw [ht3]
    by_cases h : ((π.site, π.dir2) : PhysicalBond d N) = p
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, norm_zero]
  have hsum : ∑ k : Fin 4, (if plaquetteBondSlots π k = p then ‖v‖ else 0)
      = ‖t0‖ + ‖t1‖ + ‖t2‖ + ‖t3‖ := by
    rw [Fin.sum_univ_four]
    show (if ((π.site, π.dir1) : PhysicalBond d N) = p then ‖v‖ else 0)
        + (if ((FinBox.shift π.site π.dir1, π.dir2) : PhysicalBond d N) = p
            then ‖v‖ else 0)
        + (if ((FinBox.shift π.site π.dir2, π.dir1) : PhysicalBond d N) = p
            then ‖v‖ else 0)
        + (if ((π.site, π.dir2) : PhysicalBond d N) = p then ‖v‖ else 0)
      = ‖t0‖ + ‖t1‖ + ‖t2‖ + ‖t3‖
    rw [e0, e1, e2, e3]
  rw [hsum]
  exact hchain

/-- Slot-equation counting: for each slot index the number of matching
plaquettes is at most `d` (the remaining direction is free; the site is
pinned directly or through the bijective shift). -/
theorem card_plaquettes_slot_eq_le (p : PhysicalBond d N) (k : Fin 4) :
    (Finset.univ.filter
      (fun π : ConcretePlaquette d N => plaquetteBondSlots π k = p)).card ≤ d := by
  classical
  fin_cases k
  · -- slot 0: site = p.1, dir1 = p.2, dir2 free
    have hinj : Set.InjOn (fun π : ConcretePlaquette d N => π.dir2)
        (Finset.univ.filter
          (fun π : ConcretePlaquette d N => plaquetteBondSlots π 0 = p)) := by
      intro π hπ π' hπ' hd2
      obtain ⟨-, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ)
      obtain ⟨-, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ')
      have e1 : (π.site, π.dir1) = p := h1
      have e2 : (π'.site, π'.dir1) = p := h2
      have hs : π.site = π'.site := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.1
      have h1d : π.dir1 = π'.dir1 := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.2
      cases π; cases π'
      simp_all
    calc (Finset.univ.filter
        (fun π : ConcretePlaquette d N => plaquetteBondSlots π 0 = p)).card
        ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  · -- slot 1: dir2 = p.2, site = shiftBack of p.1 along dir1; dir1 free
    have hinj : Set.InjOn (fun π : ConcretePlaquette d N => π.dir1)
        (Finset.univ.filter
          (fun π : ConcretePlaquette d N => plaquetteBondSlots π 1 = p)) := by
      intro π hπ π' hπ' hd1
      obtain ⟨-, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ)
      obtain ⟨-, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ')
      have e1 : (FinBox.shift π.site π.dir1, π.dir2) = p := h1
      have e2 : (FinBox.shift π'.site π'.dir1, π'.dir2) = p := h2
      have hshift : FinBox.shift π.site π.dir1 = FinBox.shift π'.site π'.dir1 := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.1
      have hdir2 : π.dir2 = π'.dir2 := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.2
      have hsite : π.site = π'.site := by
        have hd1' : π.dir1 = π'.dir1 := hd1
        have hbij := FinBox.shift_bijective (d := d) (N := N) π.dir1
        apply hbij.injective
        show FinBox.shift π.site π.dir1 = FinBox.shift π'.site π.dir1
        rw [hshift, hd1']
      cases π; cases π'
      simp_all
    calc (Finset.univ.filter
        (fun π : ConcretePlaquette d N => plaquetteBondSlots π 1 = p)).card
        ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  · -- slot 2: dir1 = p.2, site = shiftBack of p.1 along dir2; dir2 free
    have hinj : Set.InjOn (fun π : ConcretePlaquette d N => π.dir2)
        (Finset.univ.filter
          (fun π : ConcretePlaquette d N => plaquetteBondSlots π 2 = p)) := by
      intro π hπ π' hπ' hd2
      obtain ⟨-, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ)
      obtain ⟨-, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ')
      have e1 : (FinBox.shift π.site π.dir2, π.dir1) = p := h1
      have e2 : (FinBox.shift π'.site π'.dir2, π'.dir1) = p := h2
      have hshift : FinBox.shift π.site π.dir2 = FinBox.shift π'.site π'.dir2 := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.1
      have hdir1 : π.dir1 = π'.dir1 := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.2
      have hsite : π.site = π'.site := by
        have hd2' : π.dir2 = π'.dir2 := hd2
        have hbij := FinBox.shift_bijective (d := d) (N := N) π.dir2
        apply hbij.injective
        show FinBox.shift π.site π.dir2 = FinBox.shift π'.site π.dir2
        rw [hshift, hd2']
      cases π; cases π'
      simp_all
    calc (Finset.univ.filter
        (fun π : ConcretePlaquette d N => plaquetteBondSlots π 2 = p)).card
        ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  · -- slot 3: site = p.1, dir2 = p.2, dir1 free
    have hinj : Set.InjOn (fun π : ConcretePlaquette d N => π.dir1)
        (Finset.univ.filter
          (fun π : ConcretePlaquette d N => plaquetteBondSlots π 3 = p)) := by
      intro π hπ π' hπ' hd1
      obtain ⟨-, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ)
      obtain ⟨-, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hπ')
      have e1 : (π.site, π.dir2) = p := h1
      have e2 : (π'.site, π'.dir2) = p := h2
      have hs : π.site = π'.site := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.1
      have hd2 : π.dir2 = π'.dir2 := by
        have := e1.trans e2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.2
      cases π; cases π'
      simp_all
    calc (Finset.univ.filter
        (fun π : ConcretePlaquette d N => plaquetteBondSlots π 3 = p)).card
        ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]

/-- **Probe-image norm bound for the trivial curl**: `‖D1 δ_p v‖ ≤ 4d·‖v‖`. -/
theorem covariantD1_trivial_single_norm_le
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖ ≤
      ((4 * d : ℕ) : ℝ) * ‖v‖ := by
  classical
  calc ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖
      ≤ ∑ π : ConcretePlaquette d N,
          ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)
            (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) π‖ :=
        piLp_norm_le_sum_norm _
    _ ≤ ∑ π : ConcretePlaquette d N,
          ∑ k : Fin 4, (if plaquetteBondSlots π k = p then ‖v‖ else 0) :=
        Finset.sum_le_sum
          (fun π _ => covariantD1_trivial_single_norm_apply_le ρ p v π)
    _ = ∑ k : Fin 4, ∑ π : ConcretePlaquette d N,
          (if plaquetteBondSlots π k = p then ‖v‖ else 0) := Finset.sum_comm
    _ = ∑ k : Fin 4,
          ((Finset.univ.filter
            (fun π : ConcretePlaquette d N => plaquetteBondSlots π k = p)).card : ℝ)
            * ‖v‖ := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        calc ∑ π : ConcretePlaquette d N,
              (if plaquetteBondSlots π k = p then ‖v‖ else 0)
            = ∑ π ∈ Finset.univ.filter
                (fun π : ConcretePlaquette d N => plaquetteBondSlots π k = p),
                ‖v‖ := (Finset.sum_filter _ _).symm
          _ = ((Finset.univ.filter
                (fun π : ConcretePlaquette d N => plaquetteBondSlots π k = p)).card : ℝ)
                * ‖v‖ := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _k : Fin 4, (d : ℝ) * ‖v‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact_mod_cast card_plaquettes_slot_eq_le p k
    _ = ((4 * d : ℕ) : ℝ) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        ring

/-! ## The Gram-package endpoints for the curl term -/

/-- **Concrete finite range of the flat curl term**:
`D1†D1` has kernel range `2` in `physicalBondDist`. -/
theorem flatCurl_adjointCompSelf_finiteRange
    (ρ : SUNAdjointModel Nc) :
    PhysicalCovarianceFiniteRange
      ((covariantD1CLM (d := d) (N := N) ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
        (covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)))
      physicalBondDist 2 :=
  adjointCompSelf_finiteRange _ physicalBondDist
    (fun p q v w hR => covariantD1_trivial_gram_orthogonal ρ p q v w hR)

/-- **Concrete kernel bound of the flat curl term**:
`D1†D1` has entrywise block bound `(4d)²`. -/
theorem flatCurl_adjointCompSelf_kernelBound
    (ρ : SUNAdjointModel Nc) :
    PhysicalCovarianceKernelBound
      ((covariantD1CLM (d := d) (N := N) ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
        (covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc)))
      (fun _ _ => ((4 * d : ℕ) : ℝ) ^ 2) :=
  adjointCompSelf_kernelBound _
    (fun p v => covariantD1_trivial_single_norm_le ρ p v)

end TrivialCurl

end YangMills.RG
