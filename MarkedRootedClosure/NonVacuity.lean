/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import MarkedRootedClosure.PaperTheorems

/-!
# Non-vacuity witnesses (charter judge J-C1-3)

A CONCRETE hole family — `d = 2`, `L = 8`, two singleton holes at
sup-distance 4 — exhibited as an instance term (not an existential),
together with proofs of every geometric hypothesis of the paper
endpoints and the smallness gate `hCq` at the certified table point
`κ₀ = 16` (companion transcript: `scripts/c1_admissibility_transcript.txt`,
certified `G ∈ 0.0093341175 ± 3.2e-11 < 1`; the Lean proof below is the
EXACT counterpart of that certified row, via `e > 2.7`).

Both paper endpoints are then instantiated at this witness with the
genuine exponential weight — no zero-weight degeneracy on the marked-root
endpoint, so the conclusions bound a sum of strictly positive terms.
-/

namespace MarkedRootedClosure
namespace NonVacuity

open YangMills.RG

/-- Cube at the origin. -/
def c0 : Cube 2 8 := fun _ => 0

/-- Cube at sup-distance 4 from the origin (in `ZMod 8`, the farthest
possible), so the two singleton holes below share no `cubeAdj` edge. -/
def c4 : Cube 2 8 := fun _ => 4

/-- A cube in neither hole (for the target-preserving endpoint's
skeleton-membership hypothesis). -/
def c2 : Cube 2 8 := fun _ => 2

/-- The concrete hole family: two singleton holes. -/
def witnessHoles : HoleFamily 2 8 :=
  ⟨{({c0} : Finset (Cube 2 8)), ({c4} : Finset (Cube 2 8))}⟩

lemma c0_ne_c4 : c0 ≠ c4 := by decide

lemma not_adj_c0_c4 : ¬ (cubeAdj 2 8).Adj c0 c4 := by decide

lemma mem_witnessHoles {H : Finset (Cube 2 8)}
    (h : H ∈ witnessHoles.holes) :
    H = ({c0} : Finset (Cube 2 8)) ∨ H = ({c4} : Finset (Cube 2 8)) := by
  simpa [witnessHoles] using h

lemma witness_disj :
    ∀ H₁ ∈ witnessHoles.holes, ∀ H₂ ∈ witnessHoles.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂ := by
  have hd : Disjoint ({c0} : Finset (Cube 2 8)) {c4} :=
    Finset.disjoint_singleton_left.mpr
      (fun h => c0_ne_c4 (Finset.mem_singleton.mp h))
  intro H₁ h₁ H₂ h₂ hne
  rcases mem_witnessHoles h₁ with rfl | rfl <;>
    rcases mem_witnessHoles h₂ with rfl | rfl
  · exact absurd rfl hne
  · exact hd
  · exact hd.symm
  · exact absurd rfl hne

lemma witness_noedges :
    noEdgesBetweenHoles (cubeAdj 2 8) witnessHoles.holes := by
  intro H₁ h₁ H₂ h₂ hne x hx y hy
  rcases mem_witnessHoles h₁ with rfl | rfl <;>
    rcases mem_witnessHoles h₂ with rfl | rfl
  · exact absurd rfl hne
  · rw [Finset.mem_singleton] at hx hy; subst hx; subst hy
    exact not_adj_c0_c4
  · rw [Finset.mem_singleton] at hx hy; subst hx; subst hy
    exact fun h => not_adj_c0_c4 h.symm
  · exact absurd rfl hne

lemma witness_holes_nonempty :
    ∀ H₀ ∈ witnessHoles.holes, H₀.Nonempty := by
  intro H₀ h₀
  rcases mem_witnessHoles h₀ with rfl | rfl
  · exact ⟨c0, Finset.mem_singleton_self c0⟩
  · exact ⟨c4, Finset.mem_singleton_self c4⟩

/-- The smallness gate at `d = 2`, `κ₀ = 16` — the Lean-exact form of the
certified companion row (gate value `≈ 0.00933 < 1`).  Proof: the gate
equals `82944 / e^{16}` and `e^{16} > 2.7^{16} > 82944`. -/
lemma witness_hCq :
    ((3 ^ 2 : ℕ) : ℝ) ^ 2 *
        (Real.exp (-(16 : ℝ)) * 2 ^ (3 ^ 2 + 1)) < 1 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ (16 : ℕ) < Real.exp 1 ^ (16 : ℕ) := by
    gcongr
  have h16 : Real.exp (16 : ℝ) = Real.exp 1 ^ (16 : ℕ) := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) * 1 by norm_num,
      Real.exp_nat_mul]
  have h3 : (82944 : ℝ) < Real.exp (16 : ℝ) := by
    have hnum : (82944 : ℝ) < (2.7 : ℝ) ^ (16 : ℕ) := by norm_num
    rw [h16]; linarith
  have hmul : Real.exp (-(16 : ℝ)) * Real.exp (16 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos : (0 : ℝ) < Real.exp (-(16 : ℝ)) := Real.exp_pos _
  push_cast
  nlinarith [h3, hmul, hpos]

/-- Arbitrary activity (the endpoints are activity-agnostic; the weight
hypotheses are what carry content). -/
def witnessActivity : Finset (Cube 2 8) → ℂ := fun _ => 0

/-- The genuine exponential weight at the doubled rate — strictly
positive on every polymer, so the instantiated bounds are non-vacuous. -/
noncomputable def witnessWeight
    (Q : OmegaPolymerType witnessHoles witnessActivity) : ℝ :=
  appendixFHoleExpWeight witnessHoles (2 * (16 : ℝ)) Q.val

/-- **E2 instantiated** at the witness: marked-root leaf summation with the
strictly positive exponential weight, root `c0`, at the certified table
point `κ₀ = 16`. -/
theorem nonvacuous_markedRootLeafGeometricBound (n : ℕ) :
    ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum
          witnessHoles witnessActivity witnessWeight c0 n
      ≤
    appendixFSecondUrsellMomentConstant 2 16 *
      appendixFSecondUrsellLeafConstant 2 16 ^ n :=
  markedRootLeafGeometricBound witnessHoles witnessActivity witnessWeight
    c0 n 16 (by norm_num)
    (fun Q => appendixFHoleExpWeight_nonneg _ _ _)
    (fun _Q => le_rfl)
    witness_disj witness_noedges witness_holes_nonempty witness_hCq

lemma witness_skeleton_mem :
    c2 ∈ skeleton witnessHoles ({c2} : Finset (Cube 2 8)) := by decide

/-- **E3 instantiated** at the witness: target-preserving orderwise bound
with `w = u =` the exponential weight and zero extraction rate (the
rate-`0` hole weight is identically `1`). -/
theorem nonvacuous_targetPreservingWeightedTreeBound (n : ℕ) :
    appendixFHoleHsharpWeightedTreeTerm
        witnessHoles witnessActivity witnessWeight
        ({c2} : Finset (Cube 2 8)) n ≤
      appendixFSecondUrsellMomentConstant 2 16 *
        appendixFHoleExpWeight witnessHoles 0
          ({c2} : Finset (Cube 2 8)) *
        appendixFSecondUrsellLeafConstant 2 16 ^ n :=
  targetPreservingWeightedTreeBound witnessHoles witnessActivity
    witnessWeight witnessWeight ({c2} : Finset (Cube 2 8)) c2 n 0 16
    le_rfl
    (fun Q => appendixFHoleExpWeight_nonneg _ _ _)
    (fun Q => appendixFHoleExpWeight_nonneg _ _ _)
    (fun Q => by
      simp [appendixFHoleExpWeight])
    (fun _Q => le_rfl)
    witness_skeleton_mem (by norm_num)
    witness_disj witness_noedges witness_holes_nonempty witness_hCq

end NonVacuity
end MarkedRootedClosure
