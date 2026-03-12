import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

open YangMills MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

abbrev PosEdge (d N : ℕ) := {e : ConcreteEdge d N // e.sign = true}

noncomputable def posToFun (f : PosEdge d N → G) : ConcreteEdge d N → G :=
  fun e => if h : e.sign = true then f ⟨e, h⟩
           else (f ⟨{ e with sign := true }, rfl⟩)⁻¹

omit [NeZero d] [NeZero N] [MeasurableSpace G] in
lemma posToFun_reverse (f : PosEdge d N → G) (e : ConcreteEdge d N) :
    posToFun f { e with sign := !e.sign } = (posToFun f e)⁻¹ := by
  obtain ⟨src, dir, sign⟩ := e; cases sign <;> simp [posToFun]

omit [MeasurableSpace G] in
lemma finBoxGeometry_reverse (e : ConcreteEdge d N) :
    @FiniteLatticeGeometry.reverse _ _ G _ (finBoxGeometry d N G) e =
    { e with sign := !e.sign } := rfl

omit [MeasurableSpace G] in
@[ext]
lemma GaugeConfig.ext' {A B : GaugeConfig d N G} (h : ∀ e, A e = B e) : A = B := by
  cases A; cases B; congr; funext e; exact h e

noncomputable def posToConfig (f : PosEdge d N → G) : GaugeConfig d N G where
  toFun := posToFun f
  map_reverse e := by rw [finBoxGeometry_reverse]; exact posToFun_reverse f e

def configToPos (A : GaugeConfig d N G) : PosEdge d N → G :=
  fun ⟨e, _⟩ => A e

noncomputable def gaugeConfigEquiv :
    (PosEdge d N → G) ≃ GaugeConfig d N G where
  toFun  := posToConfig
  invFun := configToPos
  left_inv f := by ext ⟨e, he⟩; simp [configToPos, posToConfig, posToFun, he]
  right_inv A := by
    ext e
    simp only [posToConfig, configToPos, posToFun]
    obtain ⟨src, dir, sign⟩ := e
    cases sign <;> simp
    · have := A.map_reverse ⟨src, dir, true⟩
      rw [finBoxGeometry_reverse] at this; simpa using this.symm

noncomputable instance : MeasurableSpace (GaugeConfig d N G) :=
  MeasurableSpace.comap gaugeConfigEquiv.symm inferInstance

noncomputable def gaugeMeasureFrom (μ : Measure G) : Measure (GaugeConfig d N G) :=
  Measure.map gaugeConfigEquiv (Measure.pi (fun _ : PosEdge d N => μ))

#check @gaugeMeasureFrom
