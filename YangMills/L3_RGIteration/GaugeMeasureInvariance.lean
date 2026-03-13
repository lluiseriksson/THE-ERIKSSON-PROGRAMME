import Mathlib
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance
import YangMills.L1_GibbsMeasure.GibbsMeasure

namespace YangMills

open MeasureTheory Set

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G] [MeasurableSpace G]

/-! ## L3.3: Gauge invariance of the base gauge measure -/

private lemma map_mul_conj_eq_self (μ : Measure G) [MeasurableMul₂ G]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (a b : G) :
    Measure.map (fun g => a * g * b⁻¹) μ = μ := by
  have : (fun g : G => a * g * b⁻¹) = (fun g => g * b⁻¹) ∘ (fun g => a * g) := rfl
  rw [this, ← Measure.map_map (measurable_mul_const b⁻¹) (measurable_const_mul a),
      map_mul_left_eq_self, map_mul_right_eq_self]

private lemma pi_map_mul_conj [MeasurableMul₂ G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [SigmaFinite μ]
    (a b : PosEdge d N → G)
    (hm : Measurable (fun f : PosEdge d N → G => fun i => a i * f i * (b i)⁻¹)) :
    Measure.map (fun f : PosEdge d N → G => fun i => a i * f i * (b i)⁻¹)
      (Measure.pi (fun _ : PosEdge d N => μ)) = Measure.pi (fun _ : PosEdge d N => μ) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun f : PosEdge d N → G => fun i => a i * f i * (b i)⁻¹) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => (fun g => a i * g * (b i)⁻¹) ⁻¹' s i) := by
    ext f; simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  congr 1; ext i
  rw [← map_mul_conj_eq_self μ (a i) (b i),
      Measure.map_apply (by fun_prop) (hs i),
      map_mul_conj_eq_self μ (a i) (b i)]

private lemma gaugeAct_comm_equiv [MeasurableMul₂ G] (u : GaugeTransform d N G) :
    (fun f : PosEdge d N → G => GaugeConfig.gaugeAct u (gaugeConfigEquiv f)) =
    (fun f : PosEdge d N → G => gaugeConfigEquiv (fun i =>
        u (i.val.srcV) * f i * (u (i.val.dstV))⁻¹)) := by
  ext f ⟨src, dir, sign⟩
  cases sign
  · simp only [GaugeConfig.gaugeAct, gaugeConfigEquiv, Equiv.coe_fn_mk, posToConfig, posToFun,
               dif_neg Bool.false_ne_true, ConcreteEdge.srcV, ConcreteEdge.dstV,
               FiniteLatticeGeometry.src, FiniteLatticeGeometry.dst, finBoxGeometry, if_true]
    simp only [Bool.false_eq_true, if_false]
    group
  · simp only [GaugeConfig.gaugeAct, gaugeConfigEquiv, Equiv.coe_fn_mk, posToConfig, posToFun,
               ConcreteEdge.srcV, ConcreteEdge.dstV,
               FiniteLatticeGeometry.src, FiniteLatticeGeometry.dst, finBoxGeometry,
               dite_true, if_true]

theorem gaugeMeasureFrom_gauge_invariant [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [SigmaFinite μ]
    (u : GaugeTransform d N G)
    (hm : Measurable (GaugeConfig.gaugeAct u)) :
    Measure.map (GaugeConfig.gaugeAct u) (gaugeMeasureFrom (d := d) (N := N) μ) =
    gaugeMeasureFrom (d := d) (N := N) μ := by
  unfold gaugeMeasureFrom
  set a := fun i : PosEdge d N => u (i.val.srcV)
  set b := fun i : PosEdge d N => u (i.val.dstV)
  set C := fun f : PosEdge d N → G => fun i => a i * f i * (b i)⁻¹
  have hC : Measurable C := by fun_prop
  have hcomm : GaugeConfig.gaugeAct u ∘ gaugeConfigEquiv = gaugeConfigEquiv ∘ C := by
    ext f; exact congr_fun (gaugeAct_comm_equiv u) f
  calc Measure.map (GaugeConfig.gaugeAct u)
          (Measure.map gaugeConfigEquiv (Measure.pi (fun _ => μ)))
      = Measure.map (GaugeConfig.gaugeAct u ∘ gaugeConfigEquiv)
          (Measure.pi (fun _ => μ)) :=
        Measure.map_map hm measurable_gaugeConfigEquiv
    _ = Measure.map (gaugeConfigEquiv ∘ C)
          (Measure.pi (fun _ => μ)) := by rw [hcomm]
    _ = Measure.map gaugeConfigEquiv
          (Measure.map C (Measure.pi (fun _ => μ))) :=
        (Measure.map_map measurable_gaugeConfigEquiv hC).symm
    _ = Measure.map gaugeConfigEquiv (Measure.pi (fun _ => μ)) := by
        congr 1; exact pi_map_mul_conj μ a b hC

end YangMills
