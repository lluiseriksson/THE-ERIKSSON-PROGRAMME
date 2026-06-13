/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.BlockLattice
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# Coarse/fine block maps (gauge-RG campaign, brick B2)

`docs/BALABAN-RG-PLAN.md` B2.  The fine↔coarse maps the averaging
operator consumes: the canonical block representative (lower corner),
and the iterated-shift coordinate formula realising the
block-translated site `x(c) = x + L·e_μ` of the renormalization step.

**Source.** T. Bałaban, *Averaging Operations for Lattice Gauge
Theories*, Commun. Math. Phys. **98** (1985) eqs (1)–(5); *RG Approach
I*, Commun. Math. Phys. **109** (1987) eqs (0.4)/(0.12) — the
translation `x(c) = x + L·e_μ`.  Strategy: Lluis Eriksson
(ai.viXra:2602.0088).

Pure lattice geometry; reused by the averaging operator (B3).
Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

variable {d : ℕ}

/-- **The canonical block representative** (lower corner): a section of
`blockSite` sending each coarse site to the `(L·yᵢ)` corner of its
block.  This is the axial-gauge basepoint of the renormalization step
(CMP 98; CMP 109 §0). -/
def blockBasepoint (L N' : ℕ) [NeZero L] (y : FinBox d N') :
    FinBox d (L * N') :=
  fun i => ⟨L * (y i).val,
    mul_lt_mul_of_pos_left (y i).isLt (Nat.pos_of_ne_zero (NeZero.ne L))⟩

/-- `blockBasepoint` is a right inverse of `blockSite`: the lower corner
of `y`'s block sits in `y`'s block. -/
@[simp] theorem blockSite_blockBasepoint (L N' : ℕ) [NeZero L]
    (y : FinBox d N') : blockSite L N' (blockBasepoint L N' y) = y := by
  rw [blockSite_eq_iff]
  intro i
  exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne L))

/-- **Iterated-shift coordinate formula:** shifting a site `k` times in
direction `μ` advances its `μ`-coordinate by `k` (mod the torus size).
The arithmetic core of the block-translated site `x(c) = x + L·e_μ`. -/
theorem iterShift_apply_self {M : ℕ} [NeZero M]
    (x : FinBox d M) (μ : Fin d) (k : ℕ) :
    (((fun y => FinBox.shift y μ)^[k] x) μ).val = ((x μ).val + k) % M := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt (x μ).isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hstep : (((fun y => FinBox.shift y μ)^[k] x).shift μ μ).val
        = ((((fun y => FinBox.shift y μ)^[k] x) μ).val + 1) % M := by
      simp [FinBox.shift]
    rw [hstep, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- Shifting in direction `μ` leaves the other coordinates fixed. -/
theorem iterShift_apply_ne {M : ℕ} [NeZero M]
    (x : FinBox d M) (μ : Fin d) (k : ℕ) {ν : Fin d} (h : ν ≠ μ) :
    ((fun y => FinBox.shift y μ)^[k] x) ν = x ν := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show ((fun y => FinBox.shift y μ)^[k] x).shift μ ν = _
    rw [FinBox.shift, if_neg h, ih]

end YangMills.RG
