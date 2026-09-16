/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceAdjointTransport

/-!
# The regional CMP99 synthesis is the Hilbert adjoint

For a block-saturated fine region, active fine sites are exactly pairs formed
by an active coarse block and a fine site in that block.  Reindexing the
counting inner product through this equivalence identifies the explicit
synthesis map with the Hilbert adjoint of the transported block average.

The identity is one-scale and independent of the source construction of the
transport.  It does not construct the recursive CMP99 operator `Q'_j`.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']
variable {g : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- The fine-site decomposition into its unique active owner block and its
position inside that block. -/
noncomputable def cmp99ActiveFineBlockEquiv
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) :
    ActiveGaugeRegion.Site Omega ≃
      Σ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        {x : FinBox d (M * N') // x ∈ blockOf M N' y.1} where
  toFun x :=
    ⟨⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff
          (M := M) (N' := N') Omega (blockSite M N' x.1)).2
            (hOmega x.1 x.2)⟩,
      ⟨x.1, (mem_blockOf M N' (blockSite M N' x.1) x.1).2 rfl⟩⟩
  invFun p := cmp99ActiveFineSiteOfBlock Omega p.1 p.2
  left_inv x := Subtype.ext rfl
  right_inv p := by
    rcases p with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
    have howner : blockSite M N' x = y :=
      (mem_blockOf M N' y x).mp hx
    subst y
    rfl

omit [NeZero N'] in
/-- Reindex a fine-site sum as the iterated sum over active coarse blocks and
their complete fine blocks. -/
theorem sum_cmp99ActiveFineBlockEquiv
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (f : ActiveGaugeRegion.Site Omega → ℝ) :
    (∑ x : ActiveGaugeRegion.Site Omega, f x) =
      ∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          f (cmp99ActiveFineSiteOfBlock Omega y x) := by
  calc
    (∑ x : ActiveGaugeRegion.Site Omega, f x) =
        ∑ p : Σ y : ActiveGaugeRegion.Site
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
          {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          f ((cmp99ActiveFineBlockEquiv Omega hOmega).symm p) := by
      exact (Equiv.sum_comp
        (cmp99ActiveFineBlockEquiv Omega hOmega).symm f).symm
    _ = ∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          f (cmp99ActiveFineSiteOfBlock Omega y x) := by
      rw [Fintype.sum_sigma]
      rfl

/-- The explicit synthesis is exactly the Hilbert adjoint of the transported
regional block average in the unweighted counting-space convention. -/
theorem cmp99TransportedBlockSynthesisCLM_eq_adjoint
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    cmp99TransportedBlockSynthesisCLM Omega hOmega w transport =
      (cmp99TransportedBlockAverageCLM Omega w transport).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro eta phi
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [sum_cmp99ActiveFineBlockEquiv Omega hOmega]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [cmp99TransportedBlockAverageCLM_apply]
  simp_rw [cmp99TransportedBlockSynthesisCLM_apply_block]
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  congr 1
  have hinner := (transport y.1 x.1).inner_map_map
    ((transport y.1 x.1).symm (eta y))
    (phi (cmp99ActiveFineSiteOfBlock Omega y x))
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hinner.symm

/-- Exact squared norm of the regional synthesis.  The block-cardinality
factor belongs to `Q Q†`, not to the adjoint identity itself. -/
theorem norm_cmp99TransportedBlockSynthesisCLM_sq
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    ‖cmp99TransportedBlockSynthesisCLM Omega hOmega w transport eta‖ ^ 2 =
      (w ^ 2 * (M : ℝ) ^ d) * ‖eta‖ ^ 2 := by
  let Q := cmp99TransportedBlockAverageCLM Omega w transport
  let S := cmp99TransportedBlockSynthesisCLM Omega hOmega w transport
  have hS : S = Q.adjoint :=
    cmp99TransportedBlockSynthesisCLM_eq_adjoint Omega hOmega w transport
  calc
    ‖S eta‖ ^ 2 = inner ℝ (S eta) (S eta) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ eta (Q (S eta)) := by
      rw [hS, ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℝ eta ((Q.comp S) eta) := rfl
    _ = inner ℝ eta
        (((w ^ 2 * (M : ℝ) ^ d) •
          ContinuousLinearMap.id ℝ _) eta) := by
      rw [cmp99TransportedBlockAverage_comp_synthesis
        Omega hOmega w transport]
    _ = (w ^ 2 * (M : ℝ) ^ d) * ‖eta‖ ^ 2 := by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        inner_smul_right, real_inner_self_eq_norm_sq]

/-- Exact norm scaling, hence the explicit lower bound required by the
regional coarse-covariance argument. -/
theorem norm_cmp99TransportedBlockSynthesisCLM
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) g) :
    ‖cmp99TransportedBlockSynthesisCLM Omega hOmega w transport eta‖ =
      Real.sqrt (w ^ 2 * (M : ℝ) ^ d) * ‖eta‖ := by
  have hsq := norm_cmp99TransportedBlockSynthesisCLM_sq
    Omega hOmega w transport eta
  have hcoefficient : 0 ≤ w ^ 2 * (M : ℝ) ^ d := by positivity
  have hsqrt := Real.sq_sqrt hcoefficient
  have hleft := norm_nonneg
    (cmp99TransportedBlockSynthesisCLM Omega hOmega w transport eta)
  have hright : 0 ≤ Real.sqrt (w ^ 2 * (M : ℝ) ^ d) * ‖eta‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg eta)
  nlinarith

section AdjointTransport

variable {Nc : ℕ} [NeZero Nc]

/-- Physical adjoint-holonomy specialization of the Hilbert-adjoint
identity. -/
theorem cmp99AdjointBlockSynthesisCLM_eq_adjoint
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (rho : SUNAdjointModel Nc)
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc) :
    cmp99AdjointBlockSynthesisCLM Omega hOmega w rho holonomy =
      (cmp99AdjointBlockAverageCLM Omega w rho holonomy).adjoint :=
  cmp99TransportedBlockSynthesisCLM_eq_adjoint
    Omega hOmega w (cmp99AdjointBlockTransport rho holonomy)

/-- The exact lower bound for the adjoint of the physical one-scale regional
average. -/
theorem sqrt_blockWeight_mul_norm_le_adjoint_cmp99AdjointBlockAverageCLM
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (rho : SUNAdjointModel Nc)
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieCoord Nc)) :
    Real.sqrt (w ^ 2 * (M : ℝ) ^ d) * ‖eta‖ ≤
      ‖(cmp99AdjointBlockAverageCLM Omega w rho holonomy).adjoint eta‖ := by
  rw [← cmp99AdjointBlockSynthesisCLM_eq_adjoint
    Omega hOmega w rho holonomy]
  change Real.sqrt (w ^ 2 * (M : ℝ) ^ d) * ‖eta‖ ≤
    ‖cmp99TransportedBlockSynthesisCLM Omega hOmega w
      (cmp99AdjointBlockTransport rho holonomy) eta‖
  rw [norm_cmp99TransportedBlockSynthesisCLM]

/-- Coercivity of the regional middle operator with the lower bound for
`Q†` generated internally by the physical block average. -/
theorem isCoerciveCLM_cmp99SourceCoarseCovarianceMiddle_adjointBlockAverage
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (w : ℝ)
    (rho : SUNAdjointModel Nc)
    (holonomy : FinBox d N' → FinBox d (M * N') → SUN Nc)
    (A : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {c Lambda : ℝ} (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda) :
    IsCoerciveCLM
      (cmp99SourceCoarseCovarianceMiddle
        (cmp99AdjointBlockAverageCLM Omega w rho holonomy)
        (covarianceOfIsCoerciveCLM A hc hA))
      ((Real.sqrt (w ^ 2 * (M : ℝ) ^ d) / Lambda) ^ 2) := by
  apply isCoerciveCLM_cmp99SourceCoarseCovarianceMiddle
    A (cmp99AdjointBlockAverageCLM Omega w rho holonomy)
    hc hLambdaPos (Real.sqrt_nonneg _) hA hSymm hLambda
  intro eta
  exact sqrt_blockWeight_mul_norm_le_adjoint_cmp99AdjointBlockAverageCLM
    Omega hOmega w rho holonomy eta

end AdjointTransport

end

end YangMills.RG
