/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalGaugeCochains

/-!
# The concrete physical bond distance (`hRpoly` campaign — P4-CT, owner obligation 1)

`docs/HRPOLY-CAMPAIGN-PLAN.md` §3ter, owner correction of 2026-07-12,
obligation (1): a CONCRETE distance on `PhysicalBond d N`, not an abstract
parameter, with symmetry, the triangle inequality, `dist p p = 0`, and an
explicit ball-cardinality bound `N_R`.

**Construction.**
* `zmodCircVal z = min z.val (−z).val` — the circular magnitude on `ZMod N`;
  `zmodCircDist x y = zmodCircVal (x − y)` is the torus distance on the
  cyclic group.  The triangle inequality is proved by the four-way min case
  split, using only `ZMod.val_add_le`, `ZMod.val_sub`, and `neg_sub`.
* `finTorusDist a b` — the same distance on `Fin N` coordinates via the
  canonical cast into `ZMod N`.
* `finBoxDist x y = sup_i finTorusDist (x i) (y i)` — the `ℓ∞` (Chebyshev)
  torus distance on sites `FinBox d N`, matching the king-move geometry of
  `cubeAdj`.
* `physicalBondDist (x,μ) (y,ν) = max (finBoxDist x y) (if μ = ν then 0 else 1)`
  — the bond distance: site distance joined with the discrete direction
  distance.

**Ball bound.**  Each coordinate ball of radius `R` has at most `2(R+1)`
points (forward/backward arc injections into `range (R+1)`), so
`#{q : physicalBondDist p q ≤ R} ≤ (2(R+1))^d · d` — the explicit `N_R`
constant consumed by the CT2 Schur bound
(`physicalOpNorm_le_of_kernelBound_finiteRange`).

**Honest scope.**  Geometry only: no operator is proved local here.  The
term-by-term locality of `flatGaugeHodgeK0CLM`, `a•Q†Q`, and the `Sigma`
family in this distance is the next brick (owner obligation 2); nothing here
touches the interacting integral, `hRpoly`, mass gap, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

/-! ## Circular distance on `ZMod N` -/

/-- Circular magnitude on `ZMod N`: the shorter of the two arc lengths. -/
def zmodCircVal {N : ℕ} (z : ZMod N) : ℕ :=
  min z.val (-z).val

theorem zmodCircVal_neg {N : ℕ} (z : ZMod N) :
    zmodCircVal (-z) = zmodCircVal z := by
  unfold zmodCircVal
  rw [neg_neg]
  exact min_comm _ _

/-- Swapping the difference does not change the circular magnitude. -/
theorem zmodCircVal_sub_comm {N : ℕ} (x y : ZMod N) :
    zmodCircVal (x - y) = zmodCircVal (y - x) := by
  have h : y - x = -(x - y) := (neg_sub x y).symm
  rw [h, zmodCircVal_neg]

@[simp]
theorem zmodCircVal_zero {N : ℕ} [NeZero N] :
    zmodCircVal (0 : ZMod N) = 0 := by
  unfold zmodCircVal
  rw [neg_zero, ZMod.val_zero]
  simp

theorem zmodCircVal_le_val {N : ℕ} (z : ZMod N) : zmodCircVal z ≤ z.val :=
  min_le_left _ _

/-- The circular magnitude of a sum is at most the sum of the raw values. -/
theorem zmodCircVal_add_le {N : ℕ} (x y : ZMod N) :
    zmodCircVal (x + y) ≤ x.val + y.val :=
  le_trans (zmodCircVal_le_val _) (ZMod.val_add_le x y)

/-- The circular magnitude of a difference is at most the sum of the raw
values (two-sided, via `ZMod.val_sub` on the larger side). -/
theorem zmodCircVal_sub_le {N : ℕ} [NeZero N] (x y : ZMod N) :
    zmodCircVal (x - y) ≤ x.val + y.val := by
  rcases le_total y.val x.val with h | h
  · calc zmodCircVal (x - y) ≤ (x - y).val := zmodCircVal_le_val _
      _ = x.val - y.val := ZMod.val_sub h
      _ ≤ x.val + y.val := by omega
  · calc zmodCircVal (x - y) = zmodCircVal (y - x) := zmodCircVal_sub_comm x y
      _ ≤ (y - x).val := zmodCircVal_le_val _
      _ = y.val - x.val := ZMod.val_sub h
      _ ≤ x.val + y.val := by omega

/-- Circular distance on `ZMod N`. -/
def zmodCircDist {N : ℕ} (x y : ZMod N) : ℕ :=
  zmodCircVal (x - y)

theorem zmodCircDist_comm {N : ℕ} (x y : ZMod N) :
    zmodCircDist x y = zmodCircDist y x :=
  zmodCircVal_sub_comm x y

@[simp]
theorem zmodCircDist_self {N : ℕ} [NeZero N] (x : ZMod N) :
    zmodCircDist x x = 0 := by
  unfold zmodCircDist
  rw [sub_self]
  exact zmodCircVal_zero

/-- **Triangle inequality for the circular distance** — the four-way min case
split.  Each case expresses `x − z` in the combination matching the chosen
min sides and applies the add/sub bound. -/
theorem zmodCircDist_triangle {N : ℕ} [NeZero N] (x y z : ZMod N) :
    zmodCircDist x z ≤ zmodCircDist x y + zmodCircDist y z := by
  unfold zmodCircDist
  have hxy : zmodCircVal (x - y) = min (x - y).val (-(x - y)).val := rfl
  have hyz : zmodCircVal (y - z) = min (y - z).val (-(y - z)).val := rfl
  rw [hxy, hyz]
  rcases le_total (x - y).val (-(x - y)).val with hu | hu <;>
    rcases le_total (y - z).val (-(y - z)).val with hv | hv
  · -- forward + forward
    rw [min_eq_left hu, min_eq_left hv]
    have hxz : x - z = (x - y) + (y - z) := by ring
    calc zmodCircVal (x - z) = zmodCircVal ((x - y) + (y - z)) := by rw [hxz]
      _ ≤ (x - y).val + (y - z).val := zmodCircVal_add_le _ _
  · -- forward + backward
    rw [min_eq_left hu, min_eq_right hv]
    have hneg : -(y - z) = z - y := neg_sub _ _
    have hxz : x - z = (x - y) - (z - y) := by ring
    calc zmodCircVal (x - z) = zmodCircVal ((x - y) - (z - y)) := by rw [hxz]
      _ ≤ (x - y).val + (z - y).val := zmodCircVal_sub_le _ _
      _ = (x - y).val + (-(y - z)).val := by rw [hneg]
  · -- backward + forward
    rw [min_eq_right hu, min_eq_left hv]
    have hneg : -(x - y) = y - x := neg_sub _ _
    have hxz : x - z = -((y - x) - (y - z)) := by ring
    calc zmodCircVal (x - z) = zmodCircVal (-((y - x) - (y - z))) := by rw [hxz]
      _ = zmodCircVal ((y - x) - (y - z)) := zmodCircVal_neg _
      _ ≤ (y - x).val + (y - z).val := zmodCircVal_sub_le _ _
      _ = (-(x - y)).val + (y - z).val := by rw [hneg]
  · -- backward + backward
    rw [min_eq_right hu, min_eq_right hv]
    have hnegu : -(x - y) = y - x := neg_sub _ _
    have hnegv : -(y - z) = z - y := neg_sub _ _
    have hxz : x - z = -((y - x) + (z - y)) := by ring
    calc zmodCircVal (x - z) = zmodCircVal (-((y - x) + (z - y))) := by rw [hxz]
      _ = zmodCircVal ((y - x) + (z - y)) := zmodCircVal_neg _
      _ ≤ (y - x).val + (z - y).val := zmodCircVal_add_le _ _
      _ = (-(x - y)).val + (-(y - z)).val := by rw [hnegu, hnegv]

/-! ## Torus distance on `Fin N` coordinates -/

/-- Torus distance on `Fin N` via the canonical cast into `ZMod N`. -/
def finTorusDist {N : ℕ} (a b : Fin N) : ℕ :=
  zmodCircDist ((a.val : ZMod N)) ((b.val : ZMod N))

theorem finTorusDist_comm {N : ℕ} (a b : Fin N) :
    finTorusDist a b = finTorusDist b a :=
  zmodCircDist_comm _ _

@[simp]
theorem finTorusDist_self {N : ℕ} [NeZero N] (a : Fin N) :
    finTorusDist a a = 0 :=
  zmodCircDist_self _

theorem finTorusDist_triangle {N : ℕ} [NeZero N] (a b c : Fin N) :
    finTorusDist a c ≤ finTorusDist a b + finTorusDist b c :=
  zmodCircDist_triangle _ _ _

/-- The cast `Fin N → ZMod N` by value is injective. -/
theorem finToZMod_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun a : Fin N => (a.val : ZMod N)) := by
  intro a b hab
  have hab' : (a.val : ZMod N) = (b.val : ZMod N) := hab
  have ha : ((a.val : ZMod N)).val = a.val := ZMod.val_cast_of_lt a.isLt
  have hb : ((b.val : ZMod N)).val = b.val := ZMod.val_cast_of_lt b.isLt
  have hval : a.val = b.val := by
    rw [← ha, ← hb, hab']
  exact Fin.ext hval

/-- **Explicit coordinate ball bound**: at most `2(R+1)` points of `Fin N`
lie within circular distance `R` of a fixed point (forward and backward arc
injections into `range (R+1)`). -/
theorem finTorusDist_ball_card_le {N : ℕ} [NeZero N] (a : Fin N) (R : ℕ) :
    (Finset.univ.filter (fun b : Fin N => finTorusDist a b ≤ R)).card
      ≤ 2 * (R + 1) := by
  classical
  set Fwd : Finset (Fin N) :=
    Finset.univ.filter
      (fun b : Fin N => ((a.val : ZMod N) - (b.val : ZMod N)).val ≤ R) with hFwd
  set Bwd : Finset (Fin N) :=
    Finset.univ.filter
      (fun b : Fin N => ((b.val : ZMod N) - (a.val : ZMod N)).val ≤ R) with hBwd
  have hsub : Finset.univ.filter (fun b : Fin N => finTorusDist a b ≤ R)
      ⊆ Fwd ∪ Bwd := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have hmin : min ((a.val : ZMod N) - (b.val : ZMod N)).val
        ((b.val : ZMod N) - (a.val : ZMod N)).val ≤ R := by
      have h := hb.2
      unfold finTorusDist zmodCircDist zmodCircVal at h
      rwa [neg_sub] at h
    rw [Finset.mem_union, hFwd, hBwd, Finset.mem_filter, Finset.mem_filter]
    rcases min_le_iff.mp hmin with h | h
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  have hFwd_card : Fwd.card ≤ R + 1 := by
    have hinj : Set.InjOn (fun b : Fin N =>
        ((a.val : ZMod N) - (b.val : ZMod N)).val) Fwd := by
      intro b _ b' _ hbb'
      have heq : (a.val : ZMod N) - (b.val : ZMod N)
          = (a.val : ZMod N) - (b'.val : ZMod N) :=
        ZMod.val_injective N hbb'
      exact finToZMod_injective (sub_right_inj.mp heq)
    have hmaps : ∀ b ∈ Fwd, (fun b : Fin N =>
        ((a.val : ZMod N) - (b.val : ZMod N)).val) b ∈ Finset.range (R + 1) := by
      intro b hb
      rw [hFwd, Finset.mem_filter] at hb
      obtain ⟨-, hb2⟩ := hb
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le hb2
    calc Fwd.card ≤ (Finset.range (R + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
      _ = R + 1 := Finset.card_range _
  have hBwd_card : Bwd.card ≤ R + 1 := by
    have hinj : Set.InjOn (fun b : Fin N =>
        ((b.val : ZMod N) - (a.val : ZMod N)).val) Bwd := by
      intro b _ b' _ hbb'
      have heq : (b.val : ZMod N) - (a.val : ZMod N)
          = (b'.val : ZMod N) - (a.val : ZMod N) :=
        ZMod.val_injective N hbb'
      exact finToZMod_injective (sub_left_inj.mp heq)
    have hmaps : ∀ b ∈ Bwd, (fun b : Fin N =>
        ((b.val : ZMod N) - (a.val : ZMod N)).val) b ∈ Finset.range (R + 1) := by
      intro b hb
      rw [hBwd, Finset.mem_filter] at hb
      obtain ⟨-, hb2⟩ := hb
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le hb2
    calc Bwd.card ≤ (Finset.range (R + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
      _ = R + 1 := Finset.card_range _
  calc (Finset.univ.filter (fun b : Fin N => finTorusDist a b ≤ R)).card
      ≤ (Fwd ∪ Bwd).card := Finset.card_le_card hsub
    _ ≤ Fwd.card + Bwd.card := Finset.card_union_le _ _
    _ ≤ (R + 1) + (R + 1) := Nat.add_le_add hFwd_card hBwd_card
    _ = 2 * (R + 1) := by ring

/-! ## Chebyshev torus distance on sites and the bond distance -/

/-- `ℓ∞` (Chebyshev) torus distance on lattice sites. -/
def finBoxDist {d N : ℕ} (x y : FinBox d N) : ℕ :=
  Finset.univ.sup (fun i => finTorusDist (x i) (y i))

theorem finBoxDist_comm {d N : ℕ} (x y : FinBox d N) :
    finBoxDist x y = finBoxDist y x := by
  unfold finBoxDist
  exact Finset.sup_congr rfl (fun i _ => finTorusDist_comm _ _)

@[simp]
theorem finBoxDist_self {d N : ℕ} [NeZero N] (x : FinBox d N) :
    finBoxDist x x = 0 := by
  unfold finBoxDist
  simp

theorem finTorusDist_le_finBoxDist {d N : ℕ} (x y : FinBox d N) (i : Fin d) :
    finTorusDist (x i) (y i) ≤ finBoxDist x y :=
  Finset.le_sup (f := fun j => finTorusDist (x j) (y j)) (Finset.mem_univ i)

theorem finBoxDist_triangle {d N : ℕ} [NeZero N] (x y z : FinBox d N) :
    finBoxDist x z ≤ finBoxDist x y + finBoxDist y z := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _
  calc finTorusDist (x i) (z i)
      ≤ finTorusDist (x i) (y i) + finTorusDist (y i) (z i) :=
        finTorusDist_triangle _ _ _
    _ ≤ Finset.univ.sup (fun j => finTorusDist (x j) (y j)) +
          Finset.univ.sup (fun j => finTorusDist (y j) (z j)) :=
        Nat.add_le_add
          (Finset.le_sup (f := fun j => finTorusDist (x j) (y j))
            (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => finTorusDist (y j) (z j))
            (Finset.mem_univ i))

/-- **The concrete physical bond distance** (owner obligation 1): Chebyshev
torus distance between the sites, joined with the discrete distance between
the directions. -/
def physicalBondDist {d N : ℕ} [NeZero N] (p q : PhysicalBond d N) : ℕ :=
  max (finBoxDist p.1 q.1) (if p.2 = q.2 then 0 else 1)

theorem physicalBondDist_comm {d N : ℕ} [NeZero N] (p q : PhysicalBond d N) :
    physicalBondDist p q = physicalBondDist q p := by
  unfold physicalBondDist
  rw [finBoxDist_comm]
  by_cases h : p.2 = q.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

@[simp]
theorem physicalBondDist_self {d N : ℕ} [NeZero N] (p : PhysicalBond d N) :
    physicalBondDist p p = 0 := by
  unfold physicalBondDist
  simp

theorem physicalBondDist_triangle {d N : ℕ} [NeZero N]
    (p q r : PhysicalBond d N) :
    physicalBondDist p r ≤ physicalBondDist p q + physicalBondDist q r := by
  unfold physicalBondDist
  apply max_le
  · calc finBoxDist p.1 r.1
        ≤ finBoxDist p.1 q.1 + finBoxDist q.1 r.1 := finBoxDist_triangle _ _ _
      _ ≤ max (finBoxDist p.1 q.1) (if p.2 = q.2 then 0 else 1) +
            max (finBoxDist q.1 r.1) (if q.2 = r.2 then 0 else 1) :=
          Nat.add_le_add (le_max_left _ _) (le_max_left _ _)
  · by_cases hpr : p.2 = r.2
    · rw [if_pos hpr]
      exact Nat.zero_le _
    · rw [if_neg hpr]
      by_cases hpq : p.2 = q.2
      · have hqr : q.2 ≠ r.2 := fun h => hpr (hpq.trans h)
        calc (1 : ℕ) = 0 + 1 := by ring
          _ ≤ max (finBoxDist p.1 q.1) (if p.2 = q.2 then 0 else 1) +
                max (finBoxDist q.1 r.1) (if q.2 = r.2 then 0 else 1) := by
              refine Nat.add_le_add (Nat.zero_le _) ?_
              rw [if_neg hqr]
              exact le_max_right _ _
      · calc (1 : ℕ) = 1 + 0 := by ring
          _ ≤ max (finBoxDist p.1 q.1) (if p.2 = q.2 then 0 else 1) +
                max (finBoxDist q.1 r.1) (if q.2 = r.2 then 0 else 1) := by
              refine Nat.add_le_add ?_ (Nat.zero_le _)
              rw [if_neg hpq]
              exact le_max_right _ _

/-- **Explicit ball bound for the bond distance** (owner obligation 1, the
`N_R` constant): `#{q : physicalBondDist p q ≤ R} ≤ (2(R+1))^d · d`.  The
site part injects into the product of coordinate balls (each of size
`≤ 2(R+1)`), and the direction part is bounded by `d`. -/
theorem physicalBondDist_ball_card_le {d N : ℕ} [NeZero N]
    (p : PhysicalBond d N) (R : ℕ) :
    (Finset.univ.filter (fun q : PhysicalBond d N => physicalBondDist p q ≤ R)).card
      ≤ (2 * (R + 1)) ^ d * d := by
  classical
  have hsub : Finset.univ.filter
      (fun q : PhysicalBond d N => physicalBondDist p q ≤ R)
      ⊆ (Fintype.piFinset (fun i =>
          Finset.univ.filter (fun b : Fin N => finTorusDist (p.1 i) b ≤ R))) ×ˢ
        (Finset.univ : Finset (Fin d)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hd : physicalBondDist p q ≤ R := hq.2
    unfold physicalBondDist at hd
    have hbox : finBoxDist p.1 q.1 ≤ R := le_trans (le_max_left _ _) hd
    rw [Finset.mem_product]
    constructor
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        le_trans (finTorusDist_le_finBoxDist p.1 q.1 i) hbox⟩
    · exact Finset.mem_univ _
  calc (Finset.univ.filter
        (fun q : PhysicalBond d N => physicalBondDist p q ≤ R)).card
      ≤ ((Fintype.piFinset (fun i =>
            Finset.univ.filter (fun b : Fin N => finTorusDist (p.1 i) b ≤ R))) ×ˢ
          (Finset.univ : Finset (Fin d))).card := Finset.card_le_card hsub
    _ = (Fintype.piFinset (fun i =>
            Finset.univ.filter (fun b : Fin N => finTorusDist (p.1 i) b ≤ R))).card *
          (Finset.univ : Finset (Fin d)).card := Finset.card_product _ _
    _ ≤ (2 * (R + 1)) ^ d * d := by
        refine Nat.mul_le_mul ?_ ?_
        · calc (Fintype.piFinset (fun i =>
                Finset.univ.filter (fun b : Fin N => finTorusDist (p.1 i) b ≤ R))).card
              = ∏ i : Fin d, (Finset.univ.filter
                  (fun b : Fin N => finTorusDist (p.1 i) b ≤ R)).card :=
                Fintype.card_piFinset _
            _ ≤ ∏ _i : Fin d, (2 * (R + 1)) :=
                Finset.prod_le_prod' (fun i _ => finTorusDist_ball_card_le (p.1 i) R)
            _ = (2 * (R + 1)) ^ d := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        · rw [Finset.card_univ, Fintype.card_fin]

end YangMills.RG
