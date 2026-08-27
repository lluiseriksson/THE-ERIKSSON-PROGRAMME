import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityLaplacianLocality

/-!
# CMP99 (3.35): minimal internal-bond carrier of the Dirichlet Laplacian

The covariant derivative reads a one-bond collar, but after forming `D^*D`
the background on a boundary edge cancels from the quadratic form because the
adjoint representation is isometric.  Consequently the Laplacian itself only
requires equality on bonds whose two endpoints lie in the active region.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- The norm of the zero-extended covariant derivative is independent of the
background on boundary-crossing edges. -/
theorem norm_covariantD0CLM_extendZero_eq_of_eqOn_internalBonds
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc)
    (hUV : ∀ b ∈ Omega.bonds,
      U (ConcreteEdge.mk b.1 b.2 true) =
        V (ConcreteEdge.mk b.1 b.2 true))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖covariantD0CLM rho U (extendZeroZeroCLM Omega phi)‖ =
      ‖covariantD0CLM rho V (extendZeroZeroCLM Omega phi)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro b _hb
  rcases b with ⟨x, mu⟩
  by_cases hx : x ∈ Omega.sites
  · by_cases hy : x.shift mu ∈ Omega.sites
    · have hbOmega : (x, mu) ∈ Omega.bonds := by
        simp [ActiveGaugeRegion.bonds, hx, hy]
      simp only [covariantD0CLM_apply,
        extendZeroZeroCLM_apply_of_mem Omega phi x hx,
        extendZeroZeroCLM_apply_of_mem Omega phi (x.shift mu) hy]
      rw [show U (ConcreteEdge.mk x mu true) =
          V (ConcreteEdge.mk x mu true) from hUV (x, mu) hbOmega]
    · simp [covariantD0CLM_apply,
        extendZeroZeroCLM_apply_of_mem Omega phi x hx,
        extendZeroZeroCLM_apply_of_not_mem Omega phi (x.shift mu) hy]
  · by_cases hy : x.shift mu ∈ Omega.sites
    · simp [covariantD0CLM_apply,
        extendZeroZeroCLM_apply_of_not_mem Omega phi x hx,
        extendZeroZeroCLM_apply_of_mem Omega phi (x.shift mu) hy,
        rho.norm_ad]
    · simp [covariantD0CLM_apply,
        extendZeroZeroCLM_apply_of_not_mem Omega phi x hx,
        extendZeroZeroCLM_apply_of_not_mem Omega phi (x.shift mu) hy]

/-- The scaled regional derivative inherits the same boundary cancellation. -/
theorem norm_cmp99ActiveRegionSourceCovariantD0CLM_eq_of_eqOn_internalBonds
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (hUV : ∀ b ∈ Omega.bonds,
      U (ConcreteEdge.mk b.1 b.2 true) =
        V (ConcreteEdge.mk b.1 b.2 true))
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing phi‖ =
      ‖cmp99ActiveRegionSourceCovariantD0CLM Omega rho V spacing phi‖ := by
  unfold cmp99ActiveRegionSourceCovariantD0CLM
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    norm_smul]
  rw [norm_covariantD0CLM_extendZero_eq_of_eqOn_internalBonds
    Omega rho U V hUV phi]

/-- Exact minimal-carrier locality of the regional Dirichlet Laplacian. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_internalBonds
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (hUV : ∀ b ∈ Omega.bonds,
      U (ConcreteEdge.mk b.1 b.2 true) =
        V (ConcreteEdge.mk b.1 b.2 true)) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing =
      cmp99ActiveRegionSourceCovariantLaplacian Omega rho V spacing := by
  let KU := cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing
  let KV := cmp99ActiveRegionSourceCovariantLaplacian Omega rho V spacing
  have hKU : KU.IsSymmetric :=
    cmp99ActiveRegionSourceCovariantLaplacian_isSymmetric
      Omega rho U spacing
  have hKV : KV.IsSymmetric :=
    cmp99ActiveRegionSourceCovariantLaplacian_isSymmetric
      Omega rho V spacing
  have hquad : ∀ phi, inner ℝ phi (KU phi) = inner ℝ phi (KV phi) := by
    intro phi
    dsimp only [KU, KV]
    rw [inner_cmp99ActiveRegionSourceCovariantLaplacian,
      inner_cmp99ActiveRegionSourceCovariantLaplacian,
      norm_cmp99ActiveRegionSourceCovariantD0CLM_eq_of_eqOn_internalBonds
        Omega rho U V spacing hUV phi]
  have hzero : (KU - KV).toLinearMap = 0 := by
    apply ((hKU.sub hKV).inner_map_self_eq_zero).mp
    intro phi
    change inner ℝ (KU phi - KV phi) phi = 0
    rw [inner_sub_left]
    rw [hKU.apply_clm phi phi, hKV.apply_clm phi phi, hquad phi]
    exact sub_self _
  rw [← sub_eq_zero]
  apply ContinuousLinearMap.ext
  intro phi
  simpa using congrArg (fun T => T phi) hzero

end

end YangMills.RG
