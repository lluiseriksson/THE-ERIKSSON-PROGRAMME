import YangMills.RG.BalabanCMP89NeumannRectangularRegionalOwnerTransport
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
# CMP89 rectangular points in the physical CMP99 owner geometry

The source rectangle starts at the origin in the coordinates used by the
multiple-reflection certificate.  The embedding into the actual finite fine
carrier and the CMP99 `blockSite` owner are constructed internally.  There is
no free owner map.
-/

namespace YangMills.RG

noncomputable section

/-- Canonical embedding of a nonnegative half-open CMP89 rectangle into a
finite fine carrier.  The fit condition is the source-facing upper-side
dictionary and remains visible. -/
def cmp89SourceNeumannRectanglePointToFinBox_draft
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x : CMP89SourceNeumannIntegerRectanglePoint m) : FinBox 4 N :=
  fun mu =>
    ⟨Int.toNat (x.1 mu), by
      have hx0 := (x.2 mu).1
      have hxlt := lt_of_lt_of_le (x.2 mu).2 (hfit mu)
      have hxcast : (Int.toNat (x.1 mu) : ℤ) = x.1 mu :=
        Int.toNat_of_nonneg hx0
      exact_mod_cast (show (Int.toNat (x.1 mu) : ℤ) < (N : ℤ) by
        simpa [hxcast] using hxlt)⟩

@[simp]
theorem cmp89SourceNeumannRectanglePointToFinBox_val_draft
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x : CMP89SourceNeumannIntegerRectanglePoint m) (mu : Fin 4) :
    (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x mu).val =
      Int.toNat (x.1 mu) := rfl

/-- Periodic coordinate distance of the canonical embeddings is dominated by
the literal integer displacement already paid by the CMP89 image bound. -/
theorem finTorusDist_cmp89RectangleEmbedding_le_natAbs_sub_draft
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) (mu : Fin 4) :
    finTorusDist
        (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x mu)
        (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n mu) ≤
      (x.1 mu - n.1 mu).natAbs := by
  have hx0 := (x.2 mu).1
  have hn0 := (n.2 mu).1
  have hxcast : (Int.toNat (x.1 mu) : ℤ) = x.1 mu :=
    Int.toNat_of_nonneg hx0
  have hncast : (Int.toNat (n.1 mu) : ℤ) = n.1 mu :=
    Int.toNat_of_nonneg hn0
  by_cases hnx : Int.toNat (n.1 mu) ≤ Int.toNat (x.1 mu)
  · calc
      finTorusDist
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x mu)
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n mu) ≤
          Int.toNat (x.1 mu) - Int.toNat (n.1 mu) :=
        finTorusDist_le_val_sub _ _ hnx
      _ = (x.1 mu - n.1 mu).natAbs := by
        have hsub : 0 ≤ x.1 mu - n.1 mu := by omega
        have habs : ((x.1 mu - n.1 mu).natAbs : ℤ) =
            x.1 mu - n.1 mu := Int.natAbs_of_nonneg hsub
        omega
  · have hxn : Int.toNat (x.1 mu) ≤ Int.toNat (n.1 mu) := by omega
    calc
      finTorusDist
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x mu)
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n mu) =
          finTorusDist
            (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n mu)
            (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x mu) :=
        finTorusDist_comm _ _
      _ ≤ Int.toNat (n.1 mu) - Int.toNat (x.1 mu) :=
        finTorusDist_le_val_sub _ _ hxn
      _ = (x.1 mu - n.1 mu).natAbs := by
        have hsub : x.1 mu - n.1 mu ≤ 0 := by omega
        have habs : ((x.1 mu - n.1 mu).natAbs : ℤ) =
            -(x.1 mu - n.1 mu) := Int.ofNat_natAbs_of_nonpos hsub
        omega

/-- Fine periodic distance is bounded by the literal CMP89 signed-`l1`
distance, with no volume or side-cardinality factor. -/
theorem finBoxDist_cmp89RectangleEmbedding_le_l1_draft
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    (finBoxDist
        (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x)
        (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n) : ℝ) ≤
      cmp89Eq251LatticeL1Length (x.1 - n.1) := by
  have hbox := finBoxDist_le_sum_finTorusDist
    (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x)
    (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n)
  have hsum :
      ∑ mu, finTorusDist
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x mu)
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n mu) ≤
        ∑ mu, (x.1 mu - n.1 mu).natAbs := by
    exact Finset.sum_le_sum fun mu _ =>
      finTorusDist_cmp89RectangleEmbedding_le_natAbs_sub_draft
        hfit x n mu
  have hnat := hbox.trans hsum
  have hnatReal :
      (finBoxDist
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x)
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n) : ℝ) ≤
        ∑ mu, ((x.1 mu - n.1 mu).natAbs : ℝ) := by
    exact_mod_cast hnat
  simpa [cmp89Eq251LatticeL1Length] using hnatReal

/-- The canonical CMP99 localization owners of the embedded rectangle points
satisfy the exact inverse-scale bridge consumed by the owner-rate theorem. -/
theorem cmp89RectanglePhysicalOwner_mul_dist_le_l1_add_boundary_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {m : Fin 4 → ℤ}
    (hfit : ∀ mu, m mu ≤
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) : ℕ))
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    (L ^ (depth + 1) : ℝ) *
        (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth
            (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x))
          (cmp99Eq389SourceLocalizationOwner L K Q depth
            (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n)) : ℝ) ≤
      cmp89Eq251LatticeL1Length (x.1 - n.1) +
        (2 * (L ^ (depth + 1) - 1) : ℕ) := by
  have howner :=
    cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
      depth
      (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x)
      (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n)
  have hownerReal :
      (L ^ (depth + 1) : ℝ) *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x))
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n)) : ℝ) ≤
        (finBoxDist
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit x)
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit n) : ℝ) +
            (2 * (L ^ (depth + 1) - 1) : ℕ) := by
    exact_mod_cast howner
  exact hownerReal.trans (add_le_add
    (finBoxDist_cmp89RectangleEmbedding_le_l1_draft hfit x n)
    (le_refl _))

end

end YangMills.RG
