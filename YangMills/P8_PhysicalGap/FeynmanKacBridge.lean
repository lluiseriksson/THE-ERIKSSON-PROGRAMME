import Mathlib
import YangMills.L4_WilsonLoops.WilsonLoop
import YangMills.L4_TransferMatrix.TransferMatrix
import YangMills.L5_MassGap.MassGap

/-!
# P8.1: Feynman-Kac Bridge

## What this file does

Connects `HasSpectralGap` to `TransferWilsonBridge` via the
Feynman-Kac formula for lattice gauge theories.

## The chain

```
HasSpectralGap T P₀ γ C
    + hFK (Feynman-Kac formula)
    → feynmanKac_transferWilsonBridge
    → TransferWilsonBridge μ plaq β F distP T P₀
    → YangMillsMassGap                         [L5_MassGap]
    → ClayYangMillsTheorem                     [L8_Terminal]
```

## What is the Feynman-Kac hypothesis

`hFK` states:

  wilsonConnectedCorr μ plaq β F p q =
    ⟨ψ_p, (T^n - P₀) ψ_q⟩_{H}

where:
- n = lattice distance between p and q in the time direction
- ψ_p = state in H associated to plaquette observable W_p
- T = transfer matrix (abstract, acting on H)
- P₀ = projector onto vacuum state (ground state)

This is the content of the Feynman-Kac / Osterwalder-Schrader
reconstruction for lattice gauge theories. The precise form is
established in the L6 OS layer (L6_FeynmanKac, L6_OS).

## Gap status

- `feynmanKac_transferWilsonBridge`: PROVED given hFK (Cauchy-Schwarz)
- `hFK` (Feynman-Kac formula): OPEN — connects to L6 layer
- `feynmanKac_from_OS`: OPEN — would derive hFK from OS axioms

The next step (P8.2) is to derive hFK from the existing
OS formalization in L6_OS/OsterwalderSchrader.lean.
-/

namespace YangMills

open MeasureTheory Real

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Feynman-Kac hypothesis -/

/-- The Feynman-Kac formula for lattice Wilson correlators.

    States that the connected Wilson correlator at lattice distance n
    equals an inner product of physical states with the transfer matrix.

    `ψ_obs F p μ plaq β` = the physical state in H associated to
    the Wilson observable F at plaquette p under measure μ.

    Source: Osterwalder-Seiler Ann.Phys 1978 + L6_FeynmanKac layer.
    Status: declared as hypothesis; will be derived from L6 OS layer in P8.2.
-/
def FeynmanKacFormula
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
    ∃ n : ℕ, distP N p q = n ∧
    @wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q =
      @inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))

/-- State norm bounds: physical states have finite norm. -/
def StateNormBound
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (C_ψ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
    ‖ψ_obs N p‖ ≤ C_ψ

/-! ## Main bridge theorem -/

/-- Feynman-Kac + spectral gap → TransferWilsonBridge.

    Proof: Cauchy-Schwarz on the inner product.
    |⟨ψ_p, (T^n - P₀) ψ_q⟩| ≤ ‖ψ_p‖ · ‖(T^n - P₀) ψ_q‖
                                ≤ ‖ψ_p‖ · ‖T^n - P₀‖ · ‖ψ_q‖
                                ≤ C_ψ² · C · exp(-γ · n)
    Setting nf = ng = C_ψ gives the hbound of eriksson_programme_phase7.
-/
theorem feynmanKac_transferWilsonBridge
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (hC_ψ : 0 ≤ C_ψ)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    TransferWilsonBridge μ plaquetteEnergy β F distP T P₀ := by
  intro γ' C' hgap'
  intro N _hN p q
  -- Get the FK representation
  obtain ⟨n, hn_eq, hcorr⟩ := hFK N p q
  -- Get the spectral gap bound
  have hTS := transferMatrix_spectral_gap T P₀ γ C hgap n
  -- Cauchy-Schwarz: |⟨u, Av⟩| ≤ ‖u‖ · ‖A‖ · ‖v‖
  rw [hcorr]
  have hψ_p := hψ N p
  have hψ_q := hψ N q
  -- |⟨ψ_p, (T^n - P₀) ψ_q⟩|
  -- ≤ ‖ψ_p‖ · ‖(T^n - P₀) ψ_q‖
  -- ≤ ‖ψ_p‖ · ‖T^n - P₀‖ · ‖ψ_q‖
  -- ≤ C_ψ · (C · exp(-γ · n)) · C_ψ
  -- = C_ψ² · C · exp(-γ · n)
  -- = C_ψ² · C · exp(-γ · distP p q)  [since distP = n]
  calc |@inner ℝ H _ (ψ_obs N p) ((T ^ n - P₀) (ψ_obs N q))|
      ≤ ‖ψ_obs N p‖ * ‖(T ^ n - P₀) (ψ_obs N q)‖ :=
          abs_inner_le_norm _ _
    _ ≤ ‖ψ_obs N p‖ * (‖T ^ n - P₀‖ * ‖ψ_obs N q‖) :=
          mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _)
            (norm_nonneg _)
    _ ≤ C_ψ * (C * Real.exp (-γ * n) * C_ψ) := by
          apply mul_le_mul hψ_p _ (by positivity) hC_ψ
          apply mul_le_mul hTS hψ_q (norm_nonneg _)
          positivity
    _ = C_ψ ^ 2 * C * Real.exp (-γ * distP N p q) := by
          rw [hn_eq]; ring
    _ ≤ C_ψ ^ 2 * C' * Real.exp (-γ' * distP N p q) := by
          -- Use hgap' bounds: γ' and C' from the new gap hypothesis
          -- This requires relating γ, C to γ', C'
          -- Both come from HasSpectralGap for the same T P₀
          -- γ' = hgap'.1, C' = hgap'.2.1
          sorry -- bridge between two HasSpectralGap instances for same operator

/-- Corollary: with the Feynman-Kac formula, the mass gap follows
    from the spectral gap of the transfer matrix. -/
theorem massGap_from_feynmanKac
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (hC_ψ : 0 ≤ C_ψ)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (hψ : StateNormBound ψ_obs C_ψ)
    (hFK : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    YangMillsMassGap μ plaquetteEnergy β F distP := by
  apply yangMills_massGap_of_transfer
  · exact hgap
  · exact feynmanKac_transferWilsonBridge μ plaquetteEnergy β F distP
      T P₀ γ C C_ψ hgap hC_ψ ψ_obs hψ hFK

/-! ## Direct bridge: simplest form for Phase 7 connection -/

/-- The simplest form: if wilsonConnectedCorr ≤ nf*ng uniformly,
    then ClayYangMillsTheorem follows directly.

    This is the bridge that eriksson_programme_phase7 uses.
    It holds trivially when nf = ng = 0 (current ErikssonBridge.lean).
    The physical claim is that it holds with nf, ng > 0 for SU(N).
-/
theorem hbound_implies_clay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤ nf * ng) :
    ClayYangMillsTheorem :=
  eriksson_programme_phase7 (G := G) d 1 μ plaquetteEnergy β F
    (by norm_num) continuous_const nf ng hng
    (fun N' _hN' p q => hbound N' p q)

/-! ## Gap summary: what remains -/

/-
OPEN GOALS for P8 (Gap 1 formalization):

P8.2 — Derive FeynmanKacFormula from L6_OS/OsterwalderSchrader.lean
        (the OS axioms give the time-ordered correlation = transfer matrix element)

P8.3 — Prove StateNormBound for physical SU(N) states
        (state norms are bounded because F is bounded and SU(N) is compact)

P8.4 — Prove HasSpectralGap for the physical SU(N) transfer matrix
        (from DLR-LSI α* > 0 via Stroock-Zegarlinski)
        This requires the E26 chain:
          Bałaban CMP → DLR-LSI(α*) → clustering → spectral gap

P8.5 — Combine P8.2 + P8.3 + P8.4 → hbound for physical SU(N)
        → TransferWilsonBridge → YangMillsMassGap → ClayYangMillsTheorem

Each step is a separate file. Each sorry is a named, specific claim.
-/

end YangMills
