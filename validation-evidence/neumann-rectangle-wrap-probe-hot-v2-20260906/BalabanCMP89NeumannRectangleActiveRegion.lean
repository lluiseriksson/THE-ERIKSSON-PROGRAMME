import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalOwnerGeometry

/-!
# Canonical active region for the CMP89 half-open Neumann rectangle

The source rectangle is embedded in the finite carrier by the already audited
nonnegative-coordinate map.  This module defines the active region to be
exactly its half-open coordinate image and constructs the site equivalence
internally.  It does not identify this region with the terminal region of a
generated CMP99 tower; that remaining block-alignment dictionary stays
visible to the next specialization.
-/

namespace YangMills.RG

noncomputable section

/-- The literal half-open source rectangle as an active region of the finite
fine carrier. -/
def cmp89SourceNeumannRectangleActiveRegion
    {N : ℕ} [NeZero N] (m : Fin 4 → ℤ) : ActiveGaugeRegion 4 N :=
  ⟨Finset.univ.filter fun y =>
    ∀ mu, (y mu).val < Int.toNat (m mu)⟩

@[simp]
theorem mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ} (y : FinBox 4 N) :
    y ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).sites ↔
      ∀ mu, (y mu).val < Int.toNat (m mu) := by
  simp [cmp89SourceNeumannRectangleActiveRegion]

/-- The canonical embedding lands in the literal rectangular active region.
No free site map is supplied. -/
def cmp89SourceNeumannRectangleSite
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x : CMP89SourceNeumannIntegerRectanglePoint m) :
    ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m) :=
  ⟨cmp89SourceNeumannRectanglePointToFinBox_draft hfit x, by
    rw [mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff]
    intro mu
    have hx0 : 0 ≤ x.1 mu := (x.2 mu).1
    have hm0 : 0 ≤ m mu := le_trans (x.2 mu).1 (x.2 mu).2.le
    have hxcast : (Int.toNat (x.1 mu) : ℤ) = x.1 mu :=
      Int.toNat_of_nonneg hx0
    have hmcast : (Int.toNat (m mu) : ℤ) = m mu :=
      Int.toNat_of_nonneg hm0
    have hcast : (Int.toNat (x.1 mu) : ℤ) < (Int.toNat (m mu) : ℤ) := by
      simpa only [hxcast, hmcast] using (x.2 mu).2
    rw [cmp89SourceNeumannRectanglePointToFinBox_val_draft]
    exact_mod_cast hcast⟩

/-- Every site of the canonical rectangular region has a unique literal
integer representative in the source half-open rectangle. -/
def cmp89SourceNeumannRectangleSiteEquiv
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ)) :
    CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m) where
  toFun := cmp89SourceNeumannRectangleSite (N := N) hfit
  invFun y :=
    ⟨fun mu => ((y.1 mu).val : ℤ), by
      intro mu
      constructor
      · exact Int.natCast_nonneg _
      · have hy :=
          (mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff y.1).mp y.2 mu
        have hm0 : 0 ≤ m mu := (hm mu).le
        have hmcast : (Int.toNat (m mu) : ℤ) = m mu :=
          Int.toNat_of_nonneg hm0
        calc
          ((y.1 mu).val : ℤ) < (Int.toNat (m mu) : ℤ) := by
            exact_mod_cast hy
          _ = m mu := hmcast⟩
  left_inv x := by
    apply Subtype.ext
    funext mu
    exact Int.toNat_of_nonneg (x.2 mu).1
  right_inv y := by
    apply Subtype.ext
    funext mu
    rfl

@[simp]
theorem cmp89SourceNeumannRectangleSiteEquiv_apply
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (x : CMP89SourceNeumannIntegerRectanglePoint m) :
    (cmp89SourceNeumannRectangleSiteEquiv (N := N) hm hfit x).1 =
      cmp89SourceNeumannRectanglePointToFinBox_draft hfit x :=
  rfl

end

end YangMills.RG
