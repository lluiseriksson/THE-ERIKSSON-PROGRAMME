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
open scoped Matrix.Norms.L2Operator

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

/-- Restriction to an active positive-bond subtype does not increase the
counting `L²` norm.  This is stated with all physical indices pinned so later
source specializations do not ask typeclass inference to unfold the whole
regional tower. -/
theorem norm_restrictOneCLM_sq_le_sun
    (Omega : ActiveGaugeRegion d N')
    (A : GaugeOneCochain d N' (SUNLieCoord Nc)) :
    ‖restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ b : ActiveGaugeRegion.Bond Omega,
        ‖restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega A b‖ ^ 2) =
      ∑ b ∈ Omega.bonds, ‖A b‖ ^ 2 := by
      exact Finset.sum_subtype _ (fun b => Iff.rfl) _
    _ ≤ ∑ b : PositiveBond d N', ‖A b‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b _ _ => sq_nonneg _)

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
    restrictOneCLM (𝔤 := SUNLieCoord Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (covariantD0CLM rho V
          (cmp99FullSourceBlockAverage rho U
            (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi))) =
      restrictOneCLM (𝔤 := SUNLieCoord Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceCoarseTransportRemainderCochain
          rho U V (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)) := by
  apply PiLp.ext
  intro b
  rcases b with ⟨⟨y, mu⟩, hb⟩
  have hb' : y ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites ∧
      y.shift mu ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites := by
    simpa [ActiveGaugeRegion.bonds] using hb
  change covariantD0CLM rho V
      (cmp99FullSourceBlockAverage rho U
        (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi))
        (y, mu) =
    cmp99SourceCoarseTransportRemainder rho U V
      (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi) y mu
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
    ‖restrictOneCLM (𝔤 := SUNLieCoord Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceCoarseTransportRemainderCochain
          rho U V
            (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi))‖ ^ 2 ≤
      cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) * ‖phi‖ ^ 2 := by
  calc
    ‖restrictOneCLM (𝔤 := SUNLieCoord Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceCoarseTransportRemainderCochain
          rho U V
            (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi))‖ ^ 2 ≤
      ‖cmp99SourceCoarseTransportRemainderCochain
        rho U V
          (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)‖ ^ 2 :=
      norm_restrictOneCLM_sq_le_sun
        (d := d) (N' := N') (Nc := Nc)
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceCoarseTransportRemainderCochain
          rho U V
            (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi))
    _ = ∑ y : FinBox d N', ∑ mu : Fin d,
        ‖cmp99SourceCoarseTransportRemainder rho U V
          (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi) y mu‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
      rfl
    _ ≤ cmp99SourceBlockAverageWeight M d *
        (2 * (cmp99SourceTripleHolonomyRadius d M epsilonFine +
          epsilonCoarse)) ^ 2 * (d : ℝ) *
          ‖extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi‖ ^ 2 :=
      sum_norm_cmp99SourceCoarseTransportRemainder_sq_le
        (d := d) (M := M) (N' := N') (Nc := Nc)
        U V (extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega phi)
        epsilonFine epsilonCoarse
        epsilonFine_nonneg epsilonCoarse_nonneg fine_small coarse_small
    _ = _ := by rw [norm_extendZeroZeroCLM_eq]

end

end YangMills.RG
