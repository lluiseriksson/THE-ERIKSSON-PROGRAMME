import YangMills.RG.NormalizedPacketWeightedEnergy
import YangMills.RG.PositiveCompressedTrace

/-! Actual packet image basis and genuine compression trace. No supplied
orthonormality, span or trace identity, and no invariance premise. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000

variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def actualPacketSubspace (hNc : 2 ≤ Nc) (R : ℕ) :
    Submodule ℝ (PhysicalGaugeOneCochain (d + 2) n Nc) := by
  classical
  exact Submodule.span ℝ
    (↑(Finset.univ.image (normalizedCoexactRealPacket (n := n) (d := d) hNc R)) :
      Set (PhysicalGaugeOneCochain (d + 2) n Nc))

theorem actualPacketSubspace_eq_range (hNc : 2 ≤ Nc) (R : ℕ) :
    actualPacketSubspace (n := n) (d := d) (d := d) hNc R =
      LinearMap.range (normalizedCoexactRealLinear (n := n) (d := d) hNc R) := by
  classical
  rw [normalizedCoexactRealPacket_span]
  simp [actualPacketSubspace]

noncomputable def actualPacketBasis (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n) :
    OrthonormalBasis (↑(Finset.univ : Finset (CoexactPositiveIndex d R × Bool))) ℝ
      (actualPacketSubspace (n := n) (d := d) hNc R) := by
  classical
  exact OrthonormalBasis.span (normalizedCoexactRealPacket_orthonormal (n := n) (d := d) hNc R hR)
    Finset.univ

theorem actualPacketBasis_coe (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (p : ↑(Finset.univ : Finset (CoexactPositiveIndex d R × Bool))) :
    ((actualPacketBasis (n := n) (d := d) hNc R hR p : actualPacketSubspace (n := n) (d := d) hNc R) :
      PhysicalGaugeOneCochain (d + 2) n Nc) =
        normalizedCoexactRealPacket (n := n) (d := d) hNc R p := by
  classical
  exact OrthonormalBasis.span_apply _ _ p

theorem actualPacket_compression_trace (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (T : PhysicalGaugeOneCochain (d + 2) n Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain (d + 2) n Nc) :
    LinearMap.trace ℝ (actualPacketSubspace (n := n) (d := d) hNc R)
      (finiteSubspaceCompression (actualPacketSubspace (n := n) (d := d) hNc R) T) =
        ∑ p : CoexactPositiveIndex d R × Bool,
          inner ℝ (normalizedCoexactRealPacket (n := n) (d := d) hNc R p)
            (T (normalizedCoexactRealPacket (n := n) (d := d) hNc R p)) := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (actualPacketBasis (n := n) (d := d) hNc R hR)]
  simp_rw [finiteSubspaceCompression_inner, actualPacketBasis_coe]
  exact Finset.sum_coe_sort Finset.univ _

theorem actualPacket_weightedRepair_trace (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (w : PhysicalGradientIndex (d + 2) n → ℝ) :
    LinearMap.trace ℝ (actualPacketSubspace (n := n) (d := d) hNc R)
      (finiteSubspaceCompression (actualPacketSubspace (n := n) (d := d) hNc R)
        (componentwiseWeightedRepairCLM w).toLinearMap) =
      ∑ p : CoexactPositiveIndex d R × Bool, ∑ i : Fin (d + 2), ∑ l : Fin (d + 2),
        (‖normalizedPacketAmplitude (n := n) (d := d) R p l‖ ^ 2 *
          ‖positiveCoexactCharacter (n := n) (d := d) R p.1 (Pi.single i (1 : ZMod n)) - 1‖ ^ 2) *
            ∑ x : FinBox (d + 2) n, w (i, (x, l)) := by
  rw [actualPacket_compression_trace hNc R hR]
  apply Finset.sum_congr rfl
  intro p _
  exact normalizedRealPacket_weighted_energy hNc R p w

end YangMills.RG
