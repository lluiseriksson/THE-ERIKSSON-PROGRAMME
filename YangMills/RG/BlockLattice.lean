/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L0_Lattice.FiniteLattice

/-!
# Balaban block-lattice geometry (gauge-RG campaign, brick B1)

`docs/BALABAN-RG-PLAN.md` B1.  The order-1 block-averaging site map of
Bałaban's renormalization group for lattice gauge theories, built
against the existing `FinBox` lattice core.

**Source.** T. Bałaban, *Averaging Operations for Lattice Gauge
Theories*, Commun. Math. Phys. **98** (1985) 17–51, equations (1)–(3):
the fine lattice `ηℤ^d` is partitioned into order-1 blocks
`B(y) = {x : yμ ≤ xμ < yμ + L}` (`L` the fixed block size), and the
coarse lattice is the lattice of blocks.  On the periodic torus
`FinBox d N = (ℤ/N)^d` with `N = L·N'`, this is coordinatewise integer
division by `L`, mapping `(ℤ/(L·N'))^d → (ℤ/N')^d`.

**Strategy / framing.** Lluis Eriksson, *Exponential Clustering and
Mass Gap for 4D SU(N) Lattice Yang–Mills via Balaban's Renormalization
Group and Multiscale Correlator Decoupling* (ai.viXra:2602.0088).

This brick is pure lattice geometry — no gauge field, no measure — and
is reused by every later brick (coarse edges/plaquettes, the averaging
operator).  Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry, no axioms.
-/

namespace YangMills.RG

variable {d : ℕ}

/-- **Block-averaging site map** (Bałaban CMP 98, eqs (1)–(3)): a fine
site of the torus `(ℤ/(L·N'))^d` maps to its order-1 block — a site of
the coarse torus `(ℤ/N')^d` — by coordinatewise division by the block
size `L`. -/
def blockSite (L N' : ℕ) [NeZero L] (x : FinBox d (L * N')) : FinBox d N' :=
  fun i => ⟨(x i).val / L, Nat.div_lt_of_lt_mul (x i).isLt⟩

@[simp] theorem blockSite_val (L N' : ℕ) [NeZero L]
    (x : FinBox d (L * N')) (i : Fin d) :
    (blockSite L N' x i).val = (x i).val / L := rfl

/-- The block map equals `y` iff each coordinate divides into `yᵢ`. -/
theorem blockSite_eq_iff (L N' : ℕ) [NeZero L]
    (x : FinBox d (L * N')) (y : FinBox d N') :
    blockSite L N' x = y ↔ ∀ i, (x i).val / L = (y i).val := by
  constructor
  · intro h i
    have := congrFun h i
    exact congrArg Fin.val this
  · intro h
    funext i
    exact Fin.ext (h i)

/-- **The cube characterisation** (CMP 98 eq (2)): a fine site lies in
the block of `y` exactly when each coordinate is in the half-open
`L`-interval `[L·yᵢ, L·yᵢ + L)`. -/
theorem blockSite_eq_iff_cube (L N' : ℕ) [NeZero L]
    (x : FinBox d (L * N')) (y : FinBox d N') :
    blockSite L N' x = y ↔
      ∀ i, L * (y i).val ≤ (x i).val ∧ (x i).val < L * (y i).val + L := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  rw [blockSite_eq_iff]
  refine forall_congr' fun i => ?_
  have hdm := Nat.div_add_mod (x i).val L
  have hmod := Nat.mod_lt (x i).val hL
  constructor
  · intro h
    rw [← h]
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.mul_comm]; exact h1
    · rw [Nat.succ_mul, Nat.mul_comm (y i).val L]; exact h2

/-- **The block map is surjective** (every coarse site is the block of
some fine site — e.g. the block's lower corner). -/
theorem blockSite_surjective (L N' : ℕ) [NeZero L] :
    Function.Surjective (blockSite L N' : FinBox d (L * N') → FinBox d N') := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  intro y
  refine ⟨fun i => ⟨L * (y i).val, mul_lt_mul_of_pos_left (y i).isLt hL⟩, ?_⟩
  rw [blockSite_eq_iff]
  intro i
  exact Nat.mul_div_cancel_left _ hL

open scoped Classical in
/-- The order-1 **block** of a coarse site `y`: the `L`-cube of fine
sites mapping to it (CMP 98 eq (2)). -/
noncomputable def blockOf (L N' : ℕ) [NeZero L] (y : FinBox d N') :
    Finset (FinBox d (L * N')) :=
  Finset.univ.filter (fun x => blockSite L N' x = y)

open scoped Classical in
@[simp] theorem mem_blockOf (L N' : ℕ) [NeZero L]
    (y : FinBox d N') (x : FinBox d (L * N')) :
    x ∈ blockOf L N' y ↔ blockSite L N' x = y := by
  simp [blockOf]

open scoped Classical in
/-- **Every order-1 block has exactly `Lᵈ` fine sites** (CMP 98 eq (2):
the block is an `L`-cube).  The quantitative geometry fact underlying
the `L^{d/2}` field rescaling of the renormalization step. -/
theorem blockOf_card (L N' : ℕ) [NeZero L] (y : FinBox d N') :
    (blockOf L N' y).card = L ^ d := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  -- the offset embedding `(Fin d → Fin L) ↪ block of y`
  let g : (Fin d → Fin L) → FinBox d (L * N') :=
    fun r i => ⟨L * (y i).val + (r i).val, by
      have hr := (r i).isLt
      have hub : L * (y i).val + L ≤ L * N' := by
        calc L * (y i).val + L = L * ((y i).val + 1) := by ring
          _ ≤ L * N' := Nat.mul_le_mul_left L (y i).isLt
      omega⟩
  have hginj : Function.Injective g := by
    intro r r' h
    funext i
    have hi : L * (y i).val + (r i).val = L * (y i).val + (r' i).val :=
      congrArg Fin.val (congrFun h i)
    exact Fin.ext (by omega)
  have himg : blockOf L N' y = Finset.univ.image g := by
    ext x
    rw [mem_blockOf, blockSite_eq_iff_cube, Finset.mem_image]
    constructor
    · intro h
      refine ⟨fun i => ⟨(x i).val - L * (y i).val, ?_⟩, Finset.mem_univ _, ?_⟩
      · have h1 := (h i).1; have h2 := (h i).2; omega
      · funext i
        have h1 := (h i).1
        exact Fin.ext (by simp only [g]; omega)
    · rintro ⟨r, -, rfl⟩ i
      have hr := (r i).isLt
      exact ⟨by simp only [g]; omega, by simp only [g]; omega⟩
  rw [himg, Finset.card_image_of_injective _ hginj, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end YangMills.RG
