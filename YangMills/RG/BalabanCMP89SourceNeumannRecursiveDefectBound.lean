import YangMills.RG.BalabanCMP89SourceNeumannParallelDefect
import YangMills.RG.BalabanCMP99CoarseDerivativeRemainder
import YangMills.RG.BalabanCMP99OneScaleRegionalPoincare

/-!
# Quantitative CMP89 Neumann recursion defect

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The exact straight component of the CMP99 coarse derivative vanishes on the
CMP89 regional Neumann kernel.  This leaf packages the remaining `Ubar`
transport mismatch as a literal one-cochain and bounds its restriction to
the active coarse bonds by the already proved no-volume-loss global sum.

The result is deliberately a defect estimate, not exact recursive kernel
propagation.  The next step must combine it with a quantitative lower bound
for the coarse Neumann joint-kernel complement; no such absorption is hidden
here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The explicit coarse-transport mismatch as a full positive-bond
one-cochain. -/
noncomputable def cmp99SourceCoarseTransportRemainderCochain
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    GaugeOneCochain d N' (SUNLieCoord Nc) :=
  WithLp.toLp 2 fun b =>
    cmp99SourceCoarseTransportRemainder rho U V phi b.1 b.2

@[simp] theorem cmp99SourceCoarseTransportRemainderCochain_apply
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (b : PositiveBond d N') :
    cmp99SourceCoarseTransportRemainderCochain rho U V phi b =
      cmp99SourceCoarseTransportRemainder rho U V phi b.1 b.2 := rfl

/-- On the fine regional Neumann kernel, restriction of the literal coarse
derivative to active coarse bonds equals restriction of the explicit `Ubar`
transport remainder. -/
theorem restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    {spacing : ℝ} (hspacing : spacing ≠ 0)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega rho U spacing phi = 0) :
    let coarseOmega := cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
    restrictOneCLM coarseOmega
        (covariantD0CLM rho V
          (cmp99FullSourceBlockAverage rho U (extendZeroZeroCLM Omega phi))) =
      restrictOneCLM coarseOmega
        (cmp99SourceCoarseTransportRemainderCochain
          rho U V (extendZeroZeroCLM Omega phi)) := by
  dsimp only
  apply PiLp.ext
  intro b
  rcases b with ⟨⟨y, mu⟩, hb⟩
  have hb' : y ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites ∧
      y.shift mu ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites := by
    simpa [ActiveGaugeRegion.bonds] using hb
  change covariantD0CLM rho V
      (cmp99FullSourceBlockAverage rho U (extendZeroZeroCLM Omega phi))
        (y, mu) =
    cmp99SourceCoarseTransportRemainder rho U V
      (extendZeroZeroCLM Omega phi) y mu
  exact covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel
    Omega rho U V hspacing phi hD y mu hb'.1 hb'.2

/-- Volume-free active-coarse-bond estimate for the recursive Neumann
defect.  The only multiplicity is the physical number of directions; no
cardinality of the active region appears. -/
theorem norm_restrictOne_cmp99SourceCoarseTransportRemainderCochain_sq_le
    (Omega : ActiveGaugeRegion d (M * N'))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (V : PhysicalGaugeBackground d N' Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (epsilonFine epsilonCoarse : ℝ)
    (epsilonFine_nonneg : 0 ≤ epsilonFine)
    (epsilonCoarse_nonneg : 0 ≤ epsilonCoarse)
    (fine_small : ∀ e : ConcreteEdge d (M * N'),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonFine)
    (coarse_small : ∀ b : PhysicalBond d N',
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonCoarse) :
    let coarseOmega := cmp99ActiveCoarseRegion (M := M) (N' := N') Omega
    ‖restrictOneCLM coarseOmega
        (cmp99SourceCoarseTransportRemainderCochain
          rho U V (extendZeroZeroCLM Omega phi))‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) * ‖phi‖ ^ 2 := by
  dsimp only
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ b : ActiveGaugeRegion.Bond
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        ‖restrictOneCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
          (cmp99SourceCoarseTransportRemainderCochain
            rho U V (extendZeroZeroCLM Omega phi)) b‖ ^ 2) =
      ∑ b ∈ (cmp99ActiveCoarseRegion
          (M := M) (N' := N') Omega).bonds,
        ‖cmp99SourceCoarseTransportRemainderCochain
          rho U V (extendZeroZeroCLM Omega phi) b‖ ^ 2 := by
      exact Finset.sum_subtype _ (fun b => Iff.rfl) _
    _ ≤ ∑ b : PositiveBond d N',
        ‖cmp99SourceCoarseTransportRemainderCochain
          rho U V (extendZeroZeroCLM Omega phi) b‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b _ _ => sq_nonneg _)
    _ = ∑ y : FinBox d N', ∑ mu : Fin d,
        ‖cmp99SourceCoarseTransportRemainder rho U V
          (extendZeroZeroCLM Omega phi) y mu‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      rfl
    _ ≤ cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) *
          ‖extendZeroZeroCLM Omega phi‖ ^ 2 :=
      sum_norm_cmp99SourceCoarseTransportRemainder_sq_le
        U V (extendZeroZeroCLM Omega phi) epsilonFine epsilonCoarse
        epsilonFine_nonneg epsilonCoarse_nonneg fine_small coarse_small
    _ = _ := by rw [norm_extendZeroZeroCLM_eq]

end

end YangMills.RG
