import Mathlib
import YangMills.L8_Terminal.ClayPhysical
import YangMills.P8_PhysicalGap.FeynmanKacBridge

namespace YangMills

open MeasureTheory Real
open scoped InnerProductSpace

/-! ## L8.3: FeynmanKac → ClayYangMillsPhysicalStrong (C77 bridge)

### Background

After C76, the live path to `ClayYangMillsPhysicalStrong` required:
  1. `HasSpectralGap` for an N-dependent transfer matrix family, AND
  2. A `hdist` hypothesis connecting `distP N p q` to a matrix element bound on
     `wilsonConnectedCorr`, AND
  3. `HasContinuumMassGap` for the lattice mass profile.

The `FeynmanKacBridge.lean` file already defined `FeynmanKacFormula` and
`StateNormBound`, but only proved `feynmanKac_to_clay` (vacuous target).
There was no theorem connecting these hypotheses to `ClayYangMillsPhysicalStrong`.

### C77 contribution

`feynmanKac_to_physicalStrong` closes this gap.  Given:
- `FeynmanKacFormula` with real distance function distP (not zero),
- `StateNormBound ψ_obs C_ψ` (uniform observer norm bound),
- `HasSpectralGap T P0 γ C` (transfer matrix spectral gap),
- `hdistP` (distances are non-negative),

it builds `ConnectedCorrDecay` by Cauchy-Schwarz + state norm + spectral gap,
then applies `connectedCorrDecay_implies_physicalStrong`.

### Remaining live blockers

  1. Prove `HasSpectralGap` for the Yang-Mills transfer matrix,
  2. Prove `FeynmanKacFormula` for the lattice observable algebra,
  3. Prove `StateNormBound` for the physical observer family.

Oracle: `[propext, Classical.choice, Quot.sound]`. -/

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **C77 BRIDGE (sorry-free)**: FeynmanKacFormula + StateNormBound + HasSpectralGap
    → ConnectedCorrDecay via Cauchy-Schwarz + operator norm + spectral gap chain.
    Oracle: `[propext, Classical.choice, Quot.sound]`. -/
noncomputable def connectedCorrDecay_of_feynmanKac
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP where
  C     := C_ψ ^ 2 * C
  m     := γ
  hC    := mul_nonneg (sq_nonneg C_ψ) (le_of_lt hgap.2.1)
  hm    := hgap.1
  bound := fun N hN p q => by
    letI : NeZero N := hN
    obtain ⟨n, hn_eq, hcorr⟩ := hFK N p q
    have hC_ψ : (0 : ℝ) ≤ C_ψ := hψ.1
    have hp    : ‖ψ_obs N p‖ ≤ C_ψ := hψ.2 N p
    have hq    : ‖ψ_obs N q‖ ≤ C_ψ := hψ.2 N q
    have hTS   : ‖T ^ n - P₀‖ ≤ C * Real.exp (-γ * ↑n) :=
      transferMatrix_spectral_gap T P₀ γ C hgap n
    rw [hcorr, hn_eq]
    show |⟪ψ_obs N p, (T ^ n - P₀) (ψ_obs N q)⟫_ℝ| ≤
        C_ψ ^ 2 * C * Real.exp (-γ * ↑n)
    have hCS : |⟪ψ_obs N p, (T ^ n - P₀) (ψ_obs N q)⟫_ℝ| ≤
        ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ :=
      abs_real_inner_le_norm _ _
    have hopnorm : ‖(T ^ n - P₀) (ψ_obs N q)‖ ≤ ‖T ^ n - P₀‖ * ‖ψ_obs N q‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hbound : ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ ≤
        C_ψ ^ 2 * C * Real.exp (-γ * ↑n) :=
      calc ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖
          ≤ ‖ψ_obs N p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N q‖) :=
              mul_le_mul_of_nonneg_left hopnorm (norm_nonneg _)
        _ ≤ C_ψ * (‖T ^ n - P₀‖ * C_ψ) :=
              mul_le_mul hp
                (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
                (by positivity) hC_ψ
        _ ≤ C_ψ * (C * Real.exp (-γ * ↑n) * C_ψ) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hTS hC_ψ) hC_ψ
        _ = C_ψ ^ 2 * C * Real.exp (-γ * ↑n) := by ring
    linarith [hCS, hbound]

/-- **C77 MAIN (sorry-free)**: FeynmanKacFormula + StateNormBound + HasSpectralGap
    → ClayYangMillsPhysicalStrong (non-vacuous target).
    Oracle: `[propext, Classical.choice, Quot.sound]`. -/
theorem feynmanKac_to_physicalStrong
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong μ plaquetteEnergy β F distP
    (connectedCorrDecay_of_feynmanKac μ plaquetteEnergy β F distP
       T P₀ γ C C_ψ hgap ψ_obs hψ hFK)
    hdistP

/-- **C77-COR (sorry-free)**: FeynmanKacFormula + StateNormBound + HasSpectralGap
    → ClayYangMillsStrong (via PhysicalStrong → Strong hierarchy).
    Oracle: `[propext, Classical.choice, Quot.sound]`. -/
theorem feynmanKac_to_strong
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsStrong :=
  physicalStrong_implies_strong μ plaquetteEnergy β F distP
    (feynmanKac_to_physicalStrong μ plaquetteEnergy β F distP
       T P₀ γ C C_ψ hgap ψ_obs hψ hFK hdistP)

end YangMills
