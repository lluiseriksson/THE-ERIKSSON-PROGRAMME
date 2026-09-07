import YangMills.RG.NeumannRectangleDirectionalMasks

/-!
PRE-VALIDATION: source present; production .olean not yet materialized;
production compiler result not verified. Exact proof body passed a HOT draft
check; the promoted module still requires its independent cold gate. The FULL flag is computed from the ACTUAL directional masks,
not supplied independently. Fine/block units are related by positive B.
This does not identify a Green kernel or prove a physical inverse.
-/

namespace YangMills.RG

open YangMills

/-- The same full-side test used by both actual torus bond masks. -/
def neumannPhysicalFullFlag (N : ℕ) (m : Fin 4 → ℤ) (i : Fin 4) : Bool :=
  decide (Int.toNat (m i) = N)

theorem neumannPhysicalFullFlag_iff (N : ℕ) (m : Fin 4 → ℤ) (i : Fin 4) :
    neumannPhysicalFullFlag N m i = true ↔ Int.toNat (m i) = N := by
  simp only [neumannPhysicalFullFlag, decide_eq_true_eq]

/-- B is a positive fine-site block side; N and m are in block units.
The ambient fine period is B*N and the fine rectangular side is B*m. -/
theorem neumannPhysicalFullFlag_scale_test
    (B N : ℕ) (m : ℤ) (hB : 0 < B) (hm : 0 ≤ m) :
    Int.toNat ((B : ℤ) * m) = B * N ↔ Int.toNat m = N := by
  have hc : ((B * Int.toNat m : ℕ) : ℤ) = (B : ℤ) * m := by
    simp only [Int.natCast_mul, Int.toNat_of_nonneg hm]
  have hmul : Int.toNat ((B : ℤ) * m) = B * Int.toNat m := by
    rw [← hc]
    exact Int.toNat_natCast _
  rw [hmul]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hB h
  · intro h
    exact congrArg (fun n : ℕ => B * n) h

theorem neumannPhysicalFullFlag_scale
    (B N : ℕ) (m : Fin 4 → ℤ) (hB : 0 < B) (hm : ∀ i, 0 ≤ m i) :
    neumannPhysicalFullFlag (B * N) (fun i => (B : ℤ) * m i) =
      neumannPhysicalFullFlag N m := by
  funext i
  simp only [neumannPhysicalFullFlag,
    neumannPhysicalFullFlag_scale_test B N (m i) hB (hm i)]

/-- Non-strict fit is preserved: FULL directions keep actual wrap bonds. -/
theorem neumannPhysicalFullFlag_outgoing
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ i, 0 < m i) (hfit : ∀ i, m i ≤ (N : ℤ))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m)) (i : Fin 4) :
    (x.1, i) ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
      neumannPhysicalFullFlag N m i = true ∨
        (x.1 i).val + 1 < Int.toNat (m i) := by
  rw [neumannPhysicalFullFlag_iff]
  exact neumannRectangle_outgoingBond_iff hm hfit x i

theorem neumannPhysicalFullFlag_incoming
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ i, 0 < m i) (hfit : ∀ i, m i ≤ (N : ℤ))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m)) (i : Fin 4) :
    (x.1.shiftBack i, i) ∈
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
      neumannPhysicalFullFlag N m i = true ∨ 0 < (x.1 i).val := by
  rw [neumannPhysicalFullFlag_iff]
  exact neumannRectangle_incomingBond_iff hm hfit x i

end YangMills.RG

