import YangMills.RG.BalabanCMP116WilsonPlaquetteEnergy
import YangMills.RG.BalabanCMP116WilsonHessianLocality
import YangMills.RG.BalabanCMP116WilsonHessianPlaquetteOperator

/-!
# Finite-overlap bound for the interacting Wilson Hessian defect

The local plaquette estimate is summed without a volume factor.  Each of the
four plaquette slots contains any fixed physical bond at most `d` times, so
the total local energy is bounded by `4 d` times the global cochain energy.
Finite-dimensional Cauchy--Schwarz then gives a global bilinear defect bound.

The constant is deliberately conservative.  Its purpose is to close the
uniform finite-overlap step before the weighted Schur estimate.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- For one fixed plaquette slot, the summed coordinate energy is at most
`d` times the global cochain energy. -/
theorem sum_plaquetteSlot_coordinate_norm_sq_le
    (A : PhysicalGaugeOneCochain d N Nc) (k : Fin 4) :
    (∑ p : ConcretePlaquette d N,
        ‖A (physicalBondOfEdge (p.edges k))‖ ^ 2) ≤
      (d : ℝ) * ‖A‖ ^ 2 := by
  classical
  simp_rw [physicalBondOfEdge_edges_eq_plaquetteBondSlots]
  calc
    (∑ p : ConcretePlaquette d N,
        ‖A (plaquetteBondSlots p k)‖ ^ 2) =
        ∑ p : ConcretePlaquette d N,
          ∑ b : PhysicalBond d N,
            if plaquetteBondSlots p k = b then ‖A b‖ ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              simp
    _ = ∑ b : PhysicalBond d N,
          ∑ p : ConcretePlaquette d N,
            if plaquetteBondSlots p k = b then ‖A b‖ ^ 2 else 0 :=
      Finset.sum_comm
    _ = ∑ b : PhysicalBond d N,
          ((Finset.univ.filter
            (fun p : ConcretePlaquette d N =>
              plaquetteBondSlots p k = b)).card : ℝ) * ‖A b‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro b hb
          calc
            (∑ p : ConcretePlaquette d N,
                if plaquetteBondSlots p k = b then ‖A b‖ ^ 2 else 0) =
                ∑ p ∈ Finset.univ.filter
                  (fun p : ConcretePlaquette d N =>
                    plaquetteBondSlots p k = b), ‖A b‖ ^ 2 :=
              (Finset.sum_filter _ _).symm
            _ = ((Finset.univ.filter
                  (fun p : ConcretePlaquette d N =>
                    plaquetteBondSlots p k = b)).card : ℝ) * ‖A b‖ ^ 2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b : PhysicalBond d N, (d : ℝ) * ‖A b‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro b hb
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_plaquettes_slot_eq_le b k
          · positivity
    _ = (d : ℝ) * ∑ b : PhysicalBond d N, ‖A b‖ ^ 2 := by
          rw [Finset.mul_sum]
    _ = (d : ℝ) * ‖A‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]

/-- The four-slot plaquette energies have total square at most `4 d` times
the global cochain energy. -/
theorem sum_physicalPlaquetteCochainEnergySq_le
    (A : PhysicalGaugeOneCochain d N Nc) :
    (∑ p : ConcretePlaquette d N,
        physicalPlaquetteCochainEnergySq A p) ≤
      ((4 * d : ℕ) : ℝ) * ‖A‖ ^ 2 := by
  classical
  calc
    (∑ p : ConcretePlaquette d N,
        physicalPlaquetteCochainEnergySq A p) =
        ∑ k : Fin 4, ∑ p : ConcretePlaquette d N,
          ‖A (physicalBondOfEdge (p.edges k))‖ ^ 2 := by
            simp only [physicalPlaquetteCochainEnergySq]
            rw [Finset.sum_comm]
    _ ≤ ∑ _k : Fin 4, (d : ℝ) * ‖A‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ =>
        sum_plaquetteSlot_coordinate_norm_sq_le A k)
    _ = ((4 * d : ℕ) : ℝ) * ‖A‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring

/-- Squaring the local energy recovers its defining sum. -/
theorem physicalPlaquetteCochainEnergy_sq
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    physicalPlaquetteCochainEnergy A p ^ 2 =
      physicalPlaquetteCochainEnergySq A p := by
  unfold physicalPlaquetteCochainEnergy
  rw [Real.sq_sqrt]
  unfold physicalPlaquetteCochainEnergySq
  positivity

/-- Finite-overlap Cauchy--Schwarz for the two local cochain energies. -/
theorem sum_physicalPlaquetteCochainEnergy_mul_le
    (A B : PhysicalGaugeOneCochain d N Nc) :
    (∑ p : ConcretePlaquette d N,
        physicalPlaquetteCochainEnergy A p *
          physicalPlaquetteCochainEnergy B p) ≤
      ((4 * d : ℕ) : ℝ) * ‖A‖ * ‖B‖ := by
  classical
  calc
    (∑ p : ConcretePlaquette d N,
        physicalPlaquetteCochainEnergy A p *
          physicalPlaquetteCochainEnergy B p) ≤
        Real.sqrt
            (∑ p : ConcretePlaquette d N,
              physicalPlaquetteCochainEnergy A p ^ 2) *
          Real.sqrt
            (∑ p : ConcretePlaquette d N,
              physicalPlaquetteCochainEnergy B p ^ 2) := by
              simpa only [Finset.sum_attach, Finset.mem_univ, true_and] using
                (Real.sum_mul_le_sqrt_mul_sqrt
                  (Finset.univ : Finset (ConcretePlaquette d N))
                  (physicalPlaquetteCochainEnergy A)
                  (physicalPlaquetteCochainEnergy B))
    _ = Real.sqrt
            (∑ p : ConcretePlaquette d N,
              physicalPlaquetteCochainEnergySq A p) *
          Real.sqrt
            (∑ p : ConcretePlaquette d N,
              physicalPlaquetteCochainEnergySq B p) := by
              simp_rw [physicalPlaquetteCochainEnergy_sq]
    _ ≤ Real.sqrt (((4 * d : ℕ) : ℝ) * ‖A‖ ^ 2) *
          Real.sqrt (((4 * d : ℕ) : ℝ) * ‖B‖ ^ 2) := by
            gcongr
            · exact sum_physicalPlaquetteCochainEnergySq_le A
            · exact sum_physicalPlaquetteCochainEnergySq_le B
    _ = ((4 * d : ℕ) : ℝ) * ‖A‖ * ‖B‖ := by
          have hd : 0 ≤ ((4 * d : ℕ) : ℝ) := by positivity
          have hA :
              Real.sqrt (((4 * d : ℕ) : ℝ) * ‖A‖ ^ 2) =
                Real.sqrt (((4 * d : ℕ) : ℝ)) * ‖A‖ := by
            rw [Real.sqrt_mul hd, Real.sqrt_sq_eq_abs,
              abs_of_nonneg (norm_nonneg A)]
          have hB :
              Real.sqrt (((4 * d : ℕ) : ℝ) * ‖B‖ ^ 2) =
                Real.sqrt (((4 * d : ℕ) : ℝ)) * ‖B‖ := by
            rw [Real.sqrt_mul hd, Real.sqrt_sq_eq_abs,
              abs_of_nonneg (norm_nonneg B)]
          have hsqrt :
              Real.sqrt (((4 * d : ℕ) : ℝ)) *
                Real.sqrt (((4 * d : ℕ) : ℝ)) =
                ((4 * d : ℕ) : ℝ) := by
            exact Real.mul_self_sqrt hd
          rw [hA, hB]
          calc
            (Real.sqrt (((4 * d : ℕ) : ℝ)) * ‖A‖) *
                (Real.sqrt (((4 * d : ℕ) : ℝ)) * ‖B‖) =
                (Real.sqrt (((4 * d : ℕ) : ℝ)) *
                  Real.sqrt (((4 * d : ℕ) : ℝ))) * ‖A‖ * ‖B‖ := by
                    ring
            _ = ((4 * d : ℕ) : ℝ) * ‖A‖ * ‖B‖ := by
                  rw [hsqrt]

/-- Global Wilson Hessian defect: conservative volume-uniform bilinear
bound obtained by summing the physical plaquette energies. -/
theorem abs_inner_physicalWilsonHessianDefectCLM_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    |inner ℝ (physicalWilsonHessianDefectCLM U A) B| ≤
      ((256 * Nc * d : ℕ) : ℝ) * ε * ‖A‖ * ‖B‖ := by
  rw [physicalWilsonHessianDefectCLM_eq_sum_plaquette]
  simp_rw [ContinuousLinearMap.sum_apply, sum_inner]
  calc
    |∑ p : ConcretePlaquette d N,
        inner ℝ (physicalWilsonPlaquetteHessianDefectCLM U p A) B| ≤
        ∑ p : ConcretePlaquette d N,
          |inner ℝ (physicalWilsonPlaquetteHessianDefectCLM U p A) B| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : ConcretePlaquette d N,
          (Nc : ℝ) * (64 * ε *
            physicalPlaquetteCochainEnergy A p *
            physicalPlaquetteCochainEnergy B p) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [inner_physicalWilsonPlaquetteHessianDefectCLM]
        exact abs_ambientWilsonPlaquetteHessian_sub_trivial_le_energy
          U ε hε hsmall A B p
    _ = ((Nc : ℝ) * 64 * ε) *
          ∑ p : ConcretePlaquette d N,
            physicalPlaquetteCochainEnergy A p *
              physicalPlaquetteCochainEnergy B p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ ≤ ((Nc : ℝ) * 64 * ε) *
          (((4 * d : ℕ) : ℝ) * ‖A‖ * ‖B‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact sum_physicalPlaquetteCochainEnergy_mul_le A B
        · positivity
    _ = ((256 * Nc * d : ℕ) : ℝ) * ε * ‖A‖ * ‖B‖ := by
        push_cast
        ring

end

end YangMills.RG
