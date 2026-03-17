import Mathlib
import YangMills.P8_PhysicalGap.SpatialLocalityFramework

/-!
# LatticeLocalObservables — v0.8.28

Concrete scalar spin skeleton on ℤᵈ.
-/

namespace YangMills

open MeasureTheory

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def IsCylindricalObservable (A : Finset (Site d)) (F : Ω → ℝ) : Prop :=
  Measurable F

example : siteDist (d := 2) (fun _ => 0) (fun _ => 0) = 0 := by
  simp [siteDist]

example : siteDist (d := 1) (fun _ => (0 : ℤ)) (fun _ => 3) = 3 := by
  decide

end YangMills
