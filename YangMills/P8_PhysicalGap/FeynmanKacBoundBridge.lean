/-
  C84: FeynmanKacBound -- strictly weaker than FeynmanKacFormula.
  FeynmanKacFormula requires EQUALITY of wilsonConnectedCorr with the
  transfer-matrix inner product.  FeynmanKacBound only requires the
  ABSOLUTE VALUE of wilsonConnectedCorr to be bounded above by the
  inner-product norm.  Strictly weaker: equality implies bound, but not vice versa.

  Main results:
  1. def FeynmanKacBound: one-sided version of FeynmanKacFormula
  2. feynmanKacFormula_implies_bound: FeynmanKacFormula -> FeynmanKacBound
  3. connectedCorrDecay_of_feynmanKacBound: same conclusion as C77 but weaker hyp
  4. feynmanKacBound_to_physicalStrong: end-to-end corollary
  Oracle: [propext, Classical.choice, Quot.sound].  No sorry.
-/
import Mathlib
import YangMills.L8_Terminal.ClayPhysical
import YangMills.P8_PhysicalGap.FeynmanKacBridge

namespace YangMills

open MeasureTheory Real
open scoped InnerProductSpace

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- FeynmanKacBound: one-sided weakening of FeynmanKacFormula.
    Instead of requiring equality, we only require |wCC| ≤ |inner product|. -/
def FeynmanKacBound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
    ∃ n : ℕ, distP N p q = ↑n ∧
    |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))|

/-- FeynmanKacFormula implies FeynmanKacBound (equality implies one-sided bound). -/
theorem feynmanKacFormula_implies_bound
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    FeynmanKacBound μ plaquetteEnergy β F distP T P₀ ψ_obs := by
  intro N _ p q
  obtain ⟨n, hn_eq, hcorr⟩ := hFK N p q
  exact ⟨n, hn_eq, hcorr ▸ le_refl _⟩

/-- With FeynmanKacBound + HasSpectralGap + StateNormBound, derive ConnectedCorrDecay.
    Key result: weakens C77's FeynmanKacFormula hypothesis to FeynmanKacBound. -/
noncomputable def connectedCorrDecay_of_feynmanKacBound
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {γ C C_ψ : ℝ}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (hFK : FeynmanKacBound μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hgap : HasSpectralGap T P₀ γ C)
    (hψ : StateNormBound ψ_obs C_ψ) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP where
  C     := C_ψ ^ 2 * C
  m     := γ
  hC    := mul_nonneg (sq_nonneg C_ψ) (le_of_lt hgap.2.1)
  hm    := hgap.1
  bound := fun N hN p q => by
    letI : NeZero N := hN
    obtain ⟨n, hn_dist, hn_bound⟩ := hFK N p q
    rw [hn_dist]
    have hC_ψ := hψ.1; have hp := hψ.2 N p; have hq := hψ.2 N q
    have hTS := hgap.2.2 n
    have hCS : |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))| ≤
        ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ := abs_real_inner_le_norm _ _
    have hopnorm : ‖(T ^ n - P₀) (ψ_obs N q)‖ ≤ ‖T ^ n - P₀‖ * ‖ψ_obs N q‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hbound : ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ ≤
        C_ψ ^ 2 * C * Real.exp (-γ * ↑n) :=
      calc ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖
          ≤ ‖ψ_obs N p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N q‖) :=
              mul_le_mul_of_nonneg_left hopnorm (norm_nonneg _)
        _ ≤ C_ψ * (‖T ^ n - P₀‖ * C_ψ) :=
              mul_le_mul hp (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
                (by positivity) hC_ψ
        _ ≤ C_ψ * (C * Real.exp (-γ * ↑n) * C_ψ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTS hC_ψ) hC_ψ
        _ = C_ψ ^ 2 * C * Real.exp (-γ * ↑n) := by ring
    linarith [hn_bound, hCS.trans hbound]

/-- End-to-end: FeynmanKacBound + HasSpectralGap + StateNormBound → ClayYangMillsPhysicalStrong -/
theorem feynmanKacBound_to_physicalStrong
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {γ C C_ψ : ℝ}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (hFK : FeynmanKacBound μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hgap : HasSpectralGap T P₀ γ C)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong μ plaquetteEnergy β F distP
    (connectedCorrDecay_of_feynmanKacBound hFK hgap hψ) hdistP

end YangMills
