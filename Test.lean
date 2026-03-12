import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

open YangMills

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
  [MeasurableSpace G]

-- Subtype has MeasurableSpace automatically
example : MeasurableSpace
  {f : FiniteLatticeGeometry.E (d:=d) (N:=N) (G:=G) → G //
   ∀ e, f (FiniteLatticeGeometry.reverse e) = (f e)⁻¹} := inferInstance

-- So we just need to transfer it to GaugeConfig via the bijection
-- First add ext lemma
@[ext]
theorem GaugeConfig.ext {A B : GaugeConfig d N G} (h : ∀ e, A e = B e) : A = B := by
  cases A; cases B; simp [GaugeConfig.toFun] at h ⊢; funext e; exact h e

-- Now the equivalence
def GaugeConfig.equivSubtype :
    GaugeConfig d N G ≃
    {f : FiniteLatticeGeometry.E (d:=d) (N:=N) (G:=G) → G //
      ∀ e, f (FiniteLatticeGeometry.reverse e) = (f e)⁻¹} :=
  { toFun  := fun A => ⟨A.toFun, A.map_reverse⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, hf⟩
    left_inv  := fun A => by ext e; rfl
    right_inv := fun ⟨f, _⟩ => rfl }

-- Transfer MeasurableSpace
instance : MeasurableSpace (GaugeConfig d N G) :=
  MeasurableSpace.comap GaugeConfig.equivSubtype.toFun inferInstance
