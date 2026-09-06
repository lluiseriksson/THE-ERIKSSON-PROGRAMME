import YangMills.RG.NeumannRectangleDirectionalMasks
import YangMills.RG.NeumannFlatInternalBondAction

/-!
# PRE-VALIDATION: actual flat rectangular Laplacian with directional masks

Source present; .olean not materialized; result not compiler-verified.
This is a composition of the actual internal-bond action and the directionwise
full-period/proper-side masks. It does not choose the eventual physical carrier,
identify an integer boundary operator or produce a regional Green inverse.
Both inverse-spacing factors and the original non-strict side fit are retained.
The directional-mask production cold gate must be preserved before HOT testing.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

/-- Each direction independently keeps its periodic wrap when its side fills
the torus. Proper sides instead have the two distinct Neumann endpoint masks.
No global strict-fit assumption is introduced. -/
theorem neumannRectangleFlat_laplacian_directionalMasks
    {N Nc : ℕ} [NeZero N] [NeZero Nc] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu) (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (rho : SUNAdjointModel Nc) (spacing : ℝ)
    (f : GaugeZeroCochain 4 N (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m)) :
    cmp89SourceNeumannRegionalLaplacian
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m) rho
        (cmp99SourceFlatGaugeConfig 4 N Nc) spacing
        (restrictZeroCLM
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m) f) x =
      spacing⁻¹ • ∑ i : Fin 4,
        ((if Int.toNat (m i) = N ∨ (x.1 i).val + 1 < Int.toNat (m i) then
            spacing⁻¹ • (f x.1 - f (x.1.shift i)) else 0) -
          (if Int.toNat (m i) = N ∨ 0 < (x.1 i).val then
            spacing⁻¹ • (f (x.1.shiftBack i) - f x.1) else 0)) := by
  classical
  rw [neumannFlatInternalBond_laplacian_apply]
  simp_rw [neumannRectangle_outgoingBond_iff hm hfit x,
    neumannRectangle_incomingBond_iff hm hfit x]

#print axioms neumannRectangleFlat_laplacian_directionalMasks

end
end YangMills.RG
