import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Pi
import Mathlib.MeasureTheory.MeasureSpaceDef

namespace YangMills

/-!
# L0 — Finite lattice foundations
Layer L0.1: Finite lattice box Λ_L
-/

/-- L0.1.a: The d-dimensional finite lattice of side length N.
    Abstracted as `Fin d → Fin N` (vertices). This is the minimal combinatorial
    structure needed for gauge theory. -/
def FinBox (d N : ℕ) := Fin d → Fin N

instance (d N : ℕ) : Fintype (FinBox d N) := Pi.fintype

theorem card_finBox (d N : ℕ) : Fintype.card (FinBox d N) = N ^ d := by
  simp [FinBox]

instance (d N : ℕ) [NeZero N] : Inhabited (FinBox d N) :=
  ⟨fun _ => ⟨0, NeZero.pos N⟩⟩

/-- L0.2: Oriented edges. Each edge is a pair (vertex, direction). -/
def OrientedEdge (d N : ℕ) := FinBox d N × Fin d

instance (d N : ℕ) : Fintype (OrientedEdge d N) := Prod.fintype

/-- L0.3: Plaquette (elementary square) for d=4. -/
def Plaquette (d N : ℕ) := FinBox d N × Fin d × Fin d   -- base vertex + two directions

instance (d N : ℕ) : Fintype (Plaquette d N) := Prod.fintype

/-!
# L0.7: Gauge measure on the configuration space
Now that M01 is closed in Mathlib, we can define the product Haar measure directly.
-/

variable {d N : ℕ} {G : Type*} [TopologicalGroup G] [CompactSpace G] [MeasureSpace G]
  [IsHaarMeasure (haarMeasure (1 : G))]

/-- The full gauge configuration space: one copy of G per oriented edge. -/
def GaugeConfig := OrientedEdge d N → G

instance : Fintype (GaugeConfig) := Pi.fintype

/-- L0.7: The unique left-invariant probability measure on the gauge configurations.
     This is exactly the product of normalized Haar measures (M01 resolved). -/
def gaugeMeasure : Measure GaugeConfig :=
  Measure.pi (fun _ => haarMeasure (1 : G))

theorem gaugeMeasure_isProbability : gaugeMeasure.IsProbabilityMeasure := by
  simp [gaugeMeasure, Measure.pi, MeasureTheory.Measure.pi.isProbabilityMeasure]

theorem gaugeMeasure_isLeftInvariant : IsLeftInvariant gaugeMeasure := by
  simp [gaugeMeasure]
  exact MeasureTheory.Measure.pi.isLeftInvariant (fun _ => IsHaarMeasure.leftInvariant (haarMeasure (1 : G)))

end YangMills
