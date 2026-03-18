import Mathlib

namespace YangMills.ClayCore

/-!
# BlockSpin — Layer 0: Infinite Lattice Kinematics

Pure infinite-lattice geometry using Set, not Finset.
No measure theory. No averages yet. No gauge theory.
Reference: E26 P86 (2602.0131), Section 2.
-/

abbrev LatticeSite (d : ℕ) := Fin d → ℤ

def InBlock {d : ℕ} (L : ℤ) (corner s : LatticeSite d) : Prop :=
  ∀ i, corner i ≤ s i ∧ s i < corner i + L

def Block (d : ℕ) (L : ℤ) (corner : LatticeSite d) : Set (LatticeSite d) :=
  {s | InBlock L corner s}

def CoarseSite (d : ℕ) (L : ℤ) :=
  {s : LatticeSite d // ∀ i, L ∣ s i}

def canonicalCorner {d : ℕ} (L : ℤ) (hL : 0 < L) (s : LatticeSite d) :
    LatticeSite d :=
  fun i => (s i / L) * L

def sameBlock {d : ℕ} (L : ℤ) (hL : 0 < L) (s t : LatticeSite d) : Prop :=
  ∀ i, s i / L = t i / L

theorem sameBlock_refl {d : ℕ} (L : ℤ) (hL : 0 < L) (s : LatticeSite d) :
    sameBlock L hL s s := fun i => rfl

theorem sameBlock_symm {d : ℕ} (L : ℤ) (hL : 0 < L) {s t : LatticeSite d}
    (h : sameBlock L hL s t) : sameBlock L hL t s := fun i => (h i).symm

theorem sameBlock_trans {d : ℕ} (L : ℤ) (hL : 0 < L) {s t u : LatticeSite d}
    (hst : sameBlock L hL s t) (htu : sameBlock L hL t u) :
    sameBlock L hL s u := fun i => (hst i).trans (htu i)

theorem sameBlock_equiv {d : ℕ} (L : ℤ) (hL : 0 < L) :
    Equivalence (sameBlock (d := d) L hL) :=
  ⟨sameBlock_refl L hL, fun h => sameBlock_symm L hL h,
   fun h1 h2 => sameBlock_trans L hL h1 h2⟩

/-- A site is in the block of its canonical corner.
    Proof: pure Euclidean division identity + linarith. -/
theorem mem_own_block {d : ℕ} (L : ℤ) (hL : 0 < L) (s : LatticeSite d) :
    s ∈ Block d L (canonicalCorner L hL s) := by
  intro i
  simp only [Block, Set.mem_setOf_eq, InBlock, canonicalCorner]
  -- infer heq type from Mathlib (avoids Type mismatch)
  have heq := Int.ediv_add_emod (s i) L
  have hpos : 0 ≤ s i % L := Int.emod_nonneg (s i) (ne_of_gt hL)
  have hlt : s i % L < L := Int.emod_lt_of_pos (s i) hL
  constructor <;> linarith [heq]

theorem sameBlock_iff_sameCorner {d : ℕ} (L : ℤ) (hL : 0 < L)
    (s t : LatticeSite d) :
    sameBlock L hL s t ↔ canonicalCorner L hL s = canonicalCorner L hL t := by
  constructor
  · intro h; funext i; simp [canonicalCorner, h i]
  · intro h i
    have h1 : s i / L * L = t i / L * L := congr_fun h i
    have h_s := Int.mul_ediv_cancel (s i / L) (ne_of_gt hL)
    have h_t := Int.mul_ediv_cancel (t i / L) (ne_of_gt hL)
    linarith [h_s, h_t, mul_right_cancel₀ (ne_of_gt hL) h1]

def scaleSize (L : ℤ) (hL : 1 < L) : ℕ → ℤ := fun k => L ^ k

theorem scaleSize_zero (L : ℤ) (hL : 1 < L) : scaleSize L hL 0 = 1 := by
  simp [scaleSize]

theorem scaleSize_pos (L : ℤ) (hL : 1 < L) (k : ℕ) : 0 < scaleSize L hL k := by
  dsimp [scaleSize]; positivity

theorem scaleSize_succ (L : ℤ) (hL : 1 < L) (k : ℕ) :
    scaleSize L hL (k + 1) = L * scaleSize L hL k := by
  simp [scaleSize, pow_succ, mul_comm]

theorem block_coarser_scale {d : ℕ} (L : ℤ) (hL : 1 < L) (k : ℕ) :
    ∀ corner : LatticeSite d,
    Block d (scaleSize L hL k) corner ⊆
    Block d (scaleSize L hL (k + 1)) corner := by
  intro corner s hs i
  simp only [Block, Set.mem_setOf_eq, InBlock] at *
  refine ⟨(hs i).1, ?_⟩
  have hk_pos : 0 ≤ scaleSize L hL k := le_of_lt (scaleSize_pos L hL k)
  have hstep : scaleSize L hL k ≤ scaleSize L hL (k + 1) := by
    rw [scaleSize_succ]; nlinarith [scaleSize_pos L hL k]
  linarith [(hs i).2]

end YangMills.ClayCore
