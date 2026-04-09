/-
  C87: FeynmanKacOpNormBound — operator-norm correlator bound.

  ## Campaign Objective

  Introduce `FeynmanKacOpNormBound`, a strictly weaker (and more natural) hypothesis
  than `FeynmanKacBound + StateNormBound`:

    |wCC N p q| ≤ C_fk * ‖T^n − P₀‖

  This absorbs the Cauchy-Schwarz + state-norm steps into a single constant C_fk,
  so the main spectral-gap inference works in **plain Banach space** (no inner product).

  ## Improvements over C84 (FeynmanKacBound + StateNormBound)

  1. **No InnerProductSpace**: FeynmanKacOpNormBound only requires NormedSpace ℝ H.
     FeynmanKacBound uses @inner, so it needs InnerProductSpace ℝ H.
  2. **Single constant**: C_fk = C_ψ² in the Hilbert bridge, but any C_fk ≥ 0 works.
  3. **Shorter proof path**: connectedCorrDecay_of_opNormBound has a 3-line calc chain
     (no Cauchy-Schwarz detour).

  ## Four theorems

  1. def FeynmanKacOpNormBound     : |wCC| ≤ C_fk * ‖T^n-P₀‖ (Banach)
  2. connectedCorrDecay_of_opNormBound : OpNormBound + HasSpectralGap → ConnectedCorrDecay
  3. opNormBound_to_physicalStrong : OpNormBound + HasSpectralGap → ClayYangMillsPhysicalStrong
  4. feynmanKacBound_implies_opNormBound : FeynmanKacBound + StateNormBound → OpNormBound(C_ψ²)

  ## Bonus chain theorem (Section 3)

  5. normBound_opNormBound_to_physicalStrong: ‖T-P₀‖ ≤ lam + OpNormBound → Physical
     (chains C86 → C87, no sorry)

  ## Oracle

  Expected: [propext, Classical.choice, Quot.sound]

-/
import Mathlib
import YangMills.L8_Terminal.ClayPhysical
import YangMills.P8_PhysicalGap.FeynmanKacBoundBridge
import YangMills.P8_PhysicalGap.NormBoundToSpectralGap

namespace YangMills

open MeasureTheory Real ContinuousLinearMap
open scoped InnerProductSpace

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]

/-! ### Section 1: Banach-space theory (no inner product needed) -/

section BanachSpace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **C87-DEF (Banach)**: FeynmanKacOpNormBound — direct operator-norm correlator bound.

  Strictly weaker than `FeynmanKacBound + StateNormBound`: the Cauchy-Schwarz
  inequality and state-norm bound are absorbed into the single constant C_fk.
  Works in plain Banach space (no InnerProductSpace required).

    |wCC N p q| ≤ C_fk * ‖T ^ n − P₀‖

  In the Hilbert bridge (Section 2), C_fk = C_ψ² where C_ψ is the state-norm bound.
  Any C_fk ≥ 0 satisfying the inequality is accepted here. -/
def FeynmanKacOpNormBound
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (C_fk : ℝ) : Prop :=
  0 ≤ C_fk ∧
  ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
    ∃ n : ℕ, distP N p q = ↑n ∧
    |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      C_fk * ‖T ^ n - P₀‖

/-- **C87-1 (Banach)**: FeynmanKacOpNormBound + HasSpectralGap → ConnectedCorrDecay.

  Proof: pure Banach-space arithmetic.
  |wCC| ≤ C_fk * ‖T^n-P₀‖ ≤ C_fk * (C * exp(-γn)) = (C_fk*C) * exp(-γn).
  No Cauchy-Schwarz, no state-norm tracking.

  Oracle: [propext, Classical.choice, Quot.sound]. -/
noncomputable def connectedCorrDecay_of_opNormBound
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {γ C C_fk : ℝ}
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hgap : HasSpectralGap T P₀ γ C) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP where
  C   := C_fk * C
  m   := γ
  hC  := mul_nonneg hopnorm.1 (le_of_lt hgap.2.1)
  hm  := hgap.1
  bound := fun N hN p q => by
    letI : NeZero N := hN
    obtain ⟨n, hn_dist, hn_bound⟩ := hopnorm.2 N p q
    rw [hn_dist]
    have hTS := hgap.2.2 n
    have hC_fk := hopnorm.1
    calc |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
        ≤ C_fk * ‖T ^ n - P₀‖ := hn_bound
      _ ≤ C_fk * (C * Real.exp (-γ * ↑n)) :=
            mul_le_mul_of_nonneg_left hTS hC_fk
      _ = C_fk * C * Real.exp (-γ * ↑n) := by ring

/-- **C87-2 (Banach)**: End-to-end: OpNormBound + HasSpectralGap → ClayYangMillsPhysicalStrong.

  Chains C87-1 into `connectedCorrDecay_implies_physicalStrong`.
  Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem opNormBound_to_physicalStrong
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {γ C C_fk : ℝ}
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hgap : HasSpectralGap T P₀ γ C)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong μ plaquetteEnergy β F distP
    (connectedCorrDecay_of_opNormBound hopnorm hgap) hdistP

end BanachSpace

/-! ### Section 2: Hilbert bridge (InnerProductSpace → FeynmanKacOpNormBound) -/

section HilbertBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **C87-3 (Hilbert)**: FeynmanKacBound + StateNormBound → FeynmanKacOpNormBound(C_ψ²).

  Bridge theorem: absorbs Cauchy-Schwarz + state-norm bookkeeping into one constant.
  Requires InnerProductSpace (for Cauchy-Schwarz on @inner), but after this bridge
  all downstream reasoning is Banach (Section 1).

  Proof:
    |wCC| ≤ |inner(ψ_p, (T^n-P₀)ψ_q)|      (FeynmanKacBound)
         ≤ ‖ψ_p‖ * ‖(T^n-P₀)ψ_q‖           (Cauchy-Schwarz)
         ≤ ‖ψ_p‖ * (‖T^n-P₀‖ * ‖ψ_q‖)       (op-norm bound)
         ≤ C_ψ * (‖T^n-P₀‖ * C_ψ)           (StateNormBound)
         = C_ψ² * ‖T^n-P₀‖

  Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem feynmanKacBound_implies_opNormBound
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {C_ψ : ℝ}
    (hFK : FeynmanKacBound μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hψ : StateNormBound ψ_obs C_ψ) :
    FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ (C_ψ ^ 2) := by
  constructor
  · exact sq_nonneg C_ψ
  · intro N _ p q
    obtain ⟨n, hn_dist, hn_bound⟩ := hFK N p q
    refine ⟨n, hn_dist, ?_⟩
    have hC_ψ := hψ.1
    have hp := hψ.2 N p
    have hq := hψ.2 N q
    have hCS : |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))| ≤
        ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ := abs_real_inner_le_norm _ _
    have hopnorm_ineq : ‖(T ^ n - P₀) (ψ_obs N q)‖ ≤ ‖T ^ n - P₀‖ * ‖ψ_obs N q‖ :=
      ContinuousLinearMap.le_opNorm _ _
    calc |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
        ≤ |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))| := hn_bound
      _ ≤ ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ := hCS
      _ ≤ ‖ψ_obs N p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N q‖) :=
            mul_le_mul_of_nonneg_left hopnorm_ineq (norm_nonneg _)
      _ ≤ C_ψ * (‖T ^ n - P₀‖ * C_ψ) :=
            mul_le_mul hp (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
              (by positivity) hC_ψ
      _ = C_ψ ^ 2 * ‖T ^ n - P₀‖ := by ring

end HilbertBridge

/-! ### Section 3: Full chain C86 + C87 (Banach) -/

section ChainTheorem

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **C87-4 (Banach)**: Full chain: ‖T−P₀‖ ≤ lam + OpNormBound → ClayYangMillsPhysicalStrong.

  Chains C86 (`spectralGap_of_norm_le`) into C87-2 (`opNormBound_to_physicalStrong`).
  This is the master theorem for the live path:

    ‖T − P₀‖ ≤ lam (< 1)
         ↓  C86: spectralGap_of_norm_le
    HasSpectralGap T P₀ (-log lam) (‖1-P₀‖+1)
         ↓  C87-2: opNormBound_to_physicalStrong  + FeynmanKacOpNormBound
    ClayYangMillsPhysicalStrong

  After C87, the live bottleneck reduces to proving:
  (a) FeynmanKacOpNormBound (|wCC| ≤ C_fk * ‖T^n-P₀‖), and
  (b) ‖T_N − P₀‖ ≤ lam < 1 for the physical transfer matrix T_N.

  Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem normBound_opNormBound_to_physicalStrong
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (hPT : P₀ * T = P₀)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hnorm : ‖T - P₀‖ ≤ lam)
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  opNormBound_to_physicalStrong hopnorm
    (spectralGap_of_norm_le T P₀ hP₀_idem hTP hPT lam hlam0 hlam1 hnorm)
    hdistP

end ChainTheorem

end YangMills
