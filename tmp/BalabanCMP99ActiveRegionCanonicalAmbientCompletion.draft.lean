import YangMills.RG.BalabanCMP99LocalizedParametrix
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann
import YangMills.RG.BalabanCMP99SourceEq395LocalInverse

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Canonical ambient completion of a regional zero-cochain precision

The physical Eq. (3.35)/(3.60) precision lives on one selected active region,
whereas the reusable CMP99 regional-Neumann and Eq. (3.42) interfaces start
from an ambient precision and compress it to that region.  This file bridges
that carrier mismatch without identifying two independently chosen physical
operators.

For restriction `R`, zero extension `E`, and a regional precision `K`, define

`K_ambient = E K R + (I - E R)`.

The identity on the exterior is only a canonical technical completion.  The
file proves that its Dirichlet compression is exactly `K`, and therefore that
the generated regional Green is exactly the canonical covariance of `K` by
inverse uniqueness.  No ambient precision, regional Green, inverse equality,
or exterior mass is accepted from the caller.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N : ℕ} [NeZero N]
variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

private abbrev CMP99AmbientZeroEndomorphism (d N : ℕ) [NeZero N]
    (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℝ g] :=
  GaugeZeroCochain d N g →L[ℝ] GaugeZeroCochain d N g

private abbrev CMP99RegionalZeroEndomorphism
    (Omega : ActiveGaugeRegion d N)
    (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℝ g] :=
  ActiveGaugeZeroCochain Omega g →L[ℝ] ActiveGaugeZeroCochain Omega g

/-- Orthogonal characteristic projection onto one active zero-cochain
carrier, written through the repository's literal restriction/extension
maps. -/
noncomputable def cmp99ActiveRegionZeroProjection
    (Omega : ActiveGaugeRegion d N) :
    CMP99AmbientZeroEndomorphism d N g :=
  (extendZeroZeroCLM (𝔤 := g) Omega).comp
    (restrictZeroCLM (𝔤 := g) Omega)

/-- Orthogonal complement of the active-region characteristic projection. -/
noncomputable def cmp99ActiveRegionZeroComplementProjection
    (Omega : ActiveGaugeRegion d N) :
    CMP99AmbientZeroEndomorphism d N g :=
  ContinuousLinearMap.id ℝ _ - cmp99ActiveRegionZeroProjection Omega

/-- Exact Pythagorean splitting into the selected zero-cochain coordinates
and their complement. -/
theorem norm_sq_cmp99ActiveRegionZeroProjection_add_complement
    (Omega : ActiveGaugeRegion d N) (x : GaugeZeroCochain d N g) :
    ‖cmp99ActiveRegionZeroProjection Omega x‖ ^ 2 +
        ‖cmp99ActiveRegionZeroComplementProjection Omega x‖ ^ 2 =
      ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hy : y ∈ Omega.sites
  · simp [cmp99ActiveRegionZeroProjection,
      cmp99ActiveRegionZeroComplementProjection,
      ContinuousLinearMap.comp_apply, restrictZeroCLM, extendZeroZeroCLM, hy]
  · simp [cmp99ActiveRegionZeroProjection,
      cmp99ActiveRegionZeroComplementProjection,
      ContinuousLinearMap.comp_apply, restrictZeroCLM, extendZeroZeroCLM, hy]

/-- The complementary active-region coordinate projection has quadratic form
equal to its squared norm. -/
theorem inner_cmp99ActiveRegionZeroComplementProjection_self
    (Omega : ActiveGaugeRegion d N) (x : GaugeZeroCochain d N g) :
    inner ℝ x (cmp99ActiveRegionZeroComplementProjection Omega x) =
      ‖cmp99ActiveRegionZeroComplementProjection Omega x‖ ^ 2 := by
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hy : y ∈ Omega.sites
  · simp [cmp99ActiveRegionZeroProjection,
      cmp99ActiveRegionZeroComplementProjection,
      ContinuousLinearMap.comp_apply, restrictZeroCLM, extendZeroZeroCLM, hy]
  · simp [cmp99ActiveRegionZeroProjection,
      cmp99ActiveRegionZeroComplementProjection,
      ContinuousLinearMap.comp_apply, restrictZeroCLM, extendZeroZeroCLM, hy]

/-- Canonical ambient completion of a regional precision.  The exterior
coefficient is fixed to one rather than exposed as another source scalar. -/
noncomputable def cmp99ActiveRegionCanonicalAmbientCompletion
    (Omega : ActiveGaugeRegion d N)
    (K : CMP99RegionalZeroEndomorphism Omega g) :
    CMP99AmbientZeroEndomorphism d N g :=
  (extendZeroZeroCLM (𝔤 := g) Omega).comp
      (K.comp (restrictZeroCLM (𝔤 := g) Omega)) +
    cmp99ActiveRegionZeroComplementProjection Omega

/-- The canonical ambient completion is coercive with constant `min c 1`.
The proof is the exact zero-cochain analogue of the already sealed physical
bond compression theorem. -/
theorem isCoerciveCLM_cmp99ActiveRegionCanonicalAmbientCompletion
    (Omega : ActiveGaugeRegion d N)
    (K : CMP99RegionalZeroEndomorphism Omega g)
    {c : ℝ} (hK : IsCoerciveCLM K c) :
    IsCoerciveCLM
      (cmp99ActiveRegionCanonicalAmbientCompletion Omega K) (min c 1) := by
  intro x
  let E := extendZeroZeroCLM (𝔤 := g) Omega
  let R := restrictZeroCLM (𝔤 := g) Omega
  let P := cmp99ActiveRegionZeroProjection (g := g) Omega
  let Q := cmp99ActiveRegionZeroComplementProjection (g := g) Omega
  have hPyth : ‖P x‖ ^ 2 + ‖Q x‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_sq_cmp99ActiveRegionZeroProjection_add_complement Omega x
  have hR : R = E.adjoint :=
    cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint Omega
  have hKRx : c * ‖R x‖ ^ 2 ≤ inner ℝ (R x) (K (R x)) := hK (R x)
  have hminc : min c 1 ≤ c := min_le_left _ _
  have hmin1 : min c 1 ≤ 1 := min_le_right _ _
  have hPc : min c 1 * ‖P x‖ ^ 2 ≤ c * ‖R x‖ ^ 2 := by
    have hnorm : ‖P x‖ = ‖R x‖ := by
      change ‖E (R x)‖ = ‖R x‖
      exact norm_extendZeroZeroCLM_eq Omega (R x)
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right hminc (sq_nonneg ‖R x‖)
  have hQ1 : min c 1 * ‖Q x‖ ^ 2 ≤ 1 * ‖Q x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hmin1 (sq_nonneg ‖Q x‖)
  have hEKR : inner ℝ x (E (K (R x))) = inner ℝ (R x) (K (R x)) := by
    simpa [← hR] using (E.adjoint_inner_left (K (R x)) x).symm
  have hquad :
      inner ℝ x (cmp99ActiveRegionCanonicalAmbientCompletion Omega K x) =
        inner ℝ (R x) (K (R x)) + ‖Q x‖ ^ 2 := by
    rw [cmp99ActiveRegionCanonicalAmbientCompletion,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, inner_add_right, hEKR]
    exact congrArg (inner ℝ (R x) (K (R x)) + ·)
      (inner_cmp99ActiveRegionZeroComplementProjection_self Omega x)
  calc
    min c 1 * ‖x‖ ^ 2 =
        min c 1 * (‖P x‖ ^ 2 + ‖Q x‖ ^ 2) := by rw [hPyth]
    _ = min c 1 * ‖P x‖ ^ 2 + min c 1 * ‖Q x‖ ^ 2 := by ring
    _ ≤ c * ‖R x‖ ^ 2 + 1 * ‖Q x‖ ^ 2 := add_le_add hPc hQ1
    _ ≤ inner ℝ (R x) (K (R x)) + ‖Q x‖ ^ 2 := by
      simpa using add_le_add hKRx le_rfl
    _ = inner ℝ x
        (cmp99ActiveRegionCanonicalAmbientCompletion Omega K x) := hquad.symm

/-- Recompressing the canonical ambient completion recovers the original
regional precision exactly. -/
theorem cmp99RegionalDirichletPrecision_canonicalAmbientCompletion_eq
    (Omega : ActiveGaugeRegion d N)
    (K : CMP99RegionalZeroEndomorphism Omega g) :
    cmp99RegionalDirichletPrecision Omega
        (cmp99ActiveRegionCanonicalAmbientCompletion Omega K) = K := by
  let E := extendZeroZeroCLM (𝔤 := g) Omega
  let R := restrictZeroCLM (𝔤 := g) Omega
  have hRE : R.comp E = ContinuousLinearMap.id ℝ _ :=
    activeGaugeRegion_restrictZero_comp_extendZero Omega
  apply ContinuousLinearMap.ext
  intro phi
  have hREphi := DFunLike.congr_fun hRE phi
  have hREKphi := DFunLike.congr_fun hRE (K phi)
  change R (E (K (R (E phi))) + (E phi - E (R (E phi)))) = K phi
  rw [map_add, map_sub, hREphi, hREKphi, hREphi, sub_self, add_zero]

/-- The regional Green generated from the canonical ambient completion is
the canonical covariance of the original regional precision.  The exterior
identity is therefore proved irrelevant to every downstream regional action.
-/
theorem cmp99RegionalDirichletGreen_canonicalAmbientCompletion_eq
    (Omega : ActiveGaugeRegion d N)
    (K : CMP99RegionalZeroEndomorphism Omega g)
    {c : ℝ} (hc : 0 < c) (hK : IsCoerciveCLM K c) :
    cmp99RegionalDirichletGreen Omega
        (cmp99ActiveRegionCanonicalAmbientCompletion Omega K)
        (lt_min hc zero_lt_one)
        (isCoerciveCLM_cmp99ActiveRegionCanonicalAmbientCompletion Omega K hK) =
      covarianceOfIsCoerciveCLM K hc hK := by
  let A := cmp99ActiveRegionCanonicalAmbientCompletion Omega K
  let hA : IsCoerciveCLM A (min c 1) :=
    isCoerciveCLM_cmp99ActiveRegionCanonicalAmbientCompletion Omega K hK
  let Gext := cmp99RegionalDirichletGreen Omega A (lt_min hc zero_lt_one) hA
  let Gcan := covarianceOfIsCoerciveCLM K hc hK
  have hcompressed : cmp99RegionalDirichletPrecision Omega A = K :=
    cmp99RegionalDirichletPrecision_canonicalAmbientCompletion_eq Omega K
  have hGcanK : Gcan.comp K = ContinuousLinearMap.id ℝ _ :=
    covarianceOfIsCoerciveCLM_comp_precision K hc hK
  have hKGext : K.comp Gext = ContinuousLinearMap.id ℝ _ := by
    rw [← hcompressed]
    exact cmp99RegionalDirichletPrecision_comp_green Omega A
      (lt_min hc zero_lt_one) hA
  change Gext = Gcan
  calc
    Gext = (ContinuousLinearMap.id ℝ _).comp Gext := by simp
    _ = (Gcan.comp K).comp Gext := by rw [hGcanK]
    _ = Gcan.comp (K.comp Gext) := ContinuousLinearMap.comp_assoc _ _ _
    _ = Gcan.comp (ContinuousLinearMap.id ℝ _) := by rw [hKGext]
    _ = Gcan := by simp

end

end YangMills.RG
