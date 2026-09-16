import YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision
import YangMills.RG.BalabanCMP99ActiveRegionSourceCovariantAdjointStencil

/-!
# PRE-VALIDATION: Neumann internal-bond adjoint and finite divergence

Source present; .olean not materialized; not compiler-verified.
The counting adjoint of bond restriction is proved, not assumed. The actual
Neumann derivative factors through the ambient-bond-valued regional derivative,
but its adjoint receives a zero-extended INTERNAL bond field. This does not
identify Neumann with Dirichlet, assert a reflected Green boundary law, or
produce a regional inverse, uniform B0, or window15.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

omit [NeZero d] in
/-- Counting-Hilbert bond restriction/extension identity, valid also for
an empty internal-bond set. No geometric nonemptiness is assumed. -/
theorem neumannInternalBond_restrict_eq_extend_adjoint
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) :
    restrictOneCLM (𝔤 := g) Omega = (extendZeroOneCLM (𝔤 := g) Omega).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f phi
  let extPhi := extendZeroOneCLM Omega phi
  have hinter : inner ℝ phi (restrictOneCLM Omega f) =
      inner ℝ extPhi f := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    have hsupport :
        (∑ x ∈ Omega.bonds, inner ℝ (extPhi x) (f x)) =
          ∑ x : PositiveBond d N, inner ℝ (extPhi x) (f x) := by
      apply Finset.sum_subset (Finset.subset_univ Omega.bonds)
      intro x _hx hxOmega
      simp [extPhi, extendZeroOneCLM, hxOmega]
    calc
      (∑ x : ActiveGaugeRegion.Bond Omega,
          inner ℝ (phi x) ((restrictOneCLM Omega f) x)) =
          ∑ x : ActiveGaugeRegion.Bond Omega,
            inner ℝ (extPhi x.1) (f x.1) := by
        apply Finset.sum_congr rfl
        intro x _hx
        simp [restrictOneCLM, extPhi, extendZeroOneCLM, x.2]
      _ = ∑ x ∈ Omega.bonds, inner ℝ (extPhi x) (f x) := by
        exact (Finset.sum_subtype Omega.bonds (fun x => Iff.rfl)
          (fun x => inner ℝ (extPhi x) (f x))).symm
      _ = ∑ x : PositiveBond d N, inner ℝ (extPhi x) (f x) := hsupport
  calc
    inner ℝ (restrictOneCLM Omega f) phi =
        inner ℝ phi (restrictOneCLM Omega f) := real_inner_comm _ _
    _ = inner ℝ (extendZeroOneCLM Omega phi) f := hinter
    _ = inner ℝ f (extendZeroOneCLM Omega phi) := real_inner_comm _ _

/-- The actual Neumann derivative retains only internal bonds of the actual
regional derivative. The operators are not arbitrary chosen parameters. -/
theorem neumannInternalBond_derivative_eq_restrict
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ) :
    cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing =
      (restrictOneCLM (𝔤 := SUNLieCoord Nc) Omega).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing) := by
  ext phi x
  rfl

/-- Reversing the preceding factorization inserts zero extension of the
internal bond field, not an equality of the two Laplacians. -/
theorem neumannInternalBond_adjoint_eq_extended_divergence
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ) :
    (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing).adjoint =
      (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint.comp
        (extendZeroOneCLM (𝔤 := SUNLieCoord Nc) Omega) := by
  rw [neumannInternalBond_derivative_eq_restrict,
    ContinuousLinearMap.adjoint_comp,
    neumannInternalBond_restrict_eq_extend_adjoint,
    ContinuousLinearMap.adjoint_adjoint]

/-- Literal finite divergence of the Neumann internal-bond derivative.
The zero extension in both summands is essential at the boundary. -/
theorem neumannInternalBond_laplacian_apply
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site Omega) :
    cmp89SourceNeumannRegionalLaplacian Omega rho U spacing phi x =
      spacing⁻¹ • ∑ i : Fin d,
        (extendZeroOneCLM Omega
            (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing phi)
            (x.1, i) -
          rho.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((x.1.shiftBack i, i) : PhysicalBond d N)))⁻¹
            (extendZeroOneCLM Omega
              (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing phi)
              (x.1.shiftBack i, i))) := by
  rw [cmp89SourceNeumannRegionalLaplacian,
    ContinuousLinearMap.comp_apply,
    neumannInternalBond_adjoint_eq_extended_divergence,
    ContinuousLinearMap.comp_apply]
  exact cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply
    Omega rho U spacing
    (extendZeroOneCLM Omega
      (cmp89SourceNeumannRegionalCovariantD0CLM Omega rho U spacing phi)) x

#print axioms neumannInternalBond_restrict_eq_extend_adjoint
#print axioms neumannInternalBond_derivative_eq_restrict
#print axioms neumannInternalBond_adjoint_eq_extended_divergence
#print axioms neumannInternalBond_laplacian_apply

end
end YangMills.RG
