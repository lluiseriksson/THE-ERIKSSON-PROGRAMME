import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-! ## Positive edges and gauge config equivalence -/

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

/-! ## Measurable space and gauge measure -/

noncomputable instance instMeasurableSpaceGaugeConfig :
    MeasurableSpace (GaugeConfig d N G) :=
  MeasurableSpace.comap gaugeConfigEquiv.symm inferInstance

lemma measurable_gaugeConfigEquiv :
    Measurable (gaugeConfigEquiv (d:=d) (N:=N) (G:=G)) := by
  rw [measurable_iff_comap_le]
  simp only [instMeasurableSpaceGaugeConfig]
  rw [MeasurableSpace.comap_comp]
  simp [MeasurableSpace.comap_id]

/-- Product Haar measure on gauge configurations via positive-edge coordinates. -/
noncomputable def gaugeMeasureFrom (μ : Measure G) : Measure (GaugeConfig d N G) :=
  Measure.map gaugeConfigEquiv (Measure.pi (fun _ : PosEdge d N => μ))

instance gaugeMeasureFrom_isProbability (μ : Measure G) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaugeMeasureFrom (d:=d) (N:=N) μ) := by
  unfold gaugeMeasureFrom
  apply Measure.isProbabilityMeasure_map
  exact measurable_gaugeConfigEquiv.aemeasurable

/-! ## L1.1: Partition function -/

/-- Partition function: integral of Boltzmann weight over gauge measure. -/
noncomputable def partitionFunction (μ : Measure G)
    (plaquetteEnergy : G → ℝ) (β : ℝ) : ℝ :=
  ∫ U : GaugeConfig d N G, Real.exp (-β * wilsonAction plaquetteEnergy U)
    ∂(gaugeMeasureFrom (d:=d) (N:=N) μ)

/-- The partition function is strictly positive. -/
theorem partitionFunction_pos (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h_int : Integrable
      (fun U : GaugeConfig d N G => Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    0 < partitionFunction (d:=d) (N:=N) μ plaquetteEnergy β := by
  unfold partitionFunction
  haveI : NeZero (gaugeMeasureFrom (d:=d) (N:=N) μ) :=
    IsProbabilityMeasure.neZero _
  exact integral_exp_pos (μ := gaugeMeasureFrom (d:=d) (N:=N) μ) h_int

/-! ## L1.2: Gibbs measure -/

/-- Gibbs measure: exponential tilt of gauge measure by Boltzmann weight. -/
noncomputable def gibbsMeasure (μ : Measure G)
    (plaquetteEnergy : G → ℝ) (β : ℝ) : Measure (GaugeConfig d N G) :=
  (gaugeMeasureFrom (d:=d) (N:=N) μ).tilted
    (fun U => -β * wilsonAction plaquetteEnergy U)

/-- Gibbs measure is a probability measure given integrability. -/
instance gibbsMeasure_isProbability (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ)
    (h_int : Integrable
      (fun U : GaugeConfig d N G => Real.exp (-β * wilsonAction plaquetteEnergy U))
      (gaugeMeasureFrom (d:=d) (N:=N) μ)) :
    IsProbabilityMeasure (gibbsMeasure (d:=d) (N:=N) μ plaquetteEnergy β) := by
  unfold gibbsMeasure
  haveI : NeZero (gaugeMeasureFrom (d:=d) (N:=N) μ) :=
    IsProbabilityMeasure.neZero _
  exact isProbabilityMeasure_tilted h_int

end YangMills
