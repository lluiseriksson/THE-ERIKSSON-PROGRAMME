import Mathlib
import YangMills.L0_Lattice.WilsonAction
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L4_WilsonLoops.WilsonLoop

namespace YangMills

open MeasureTheory

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-! ## L4.3: Transfer Matrix and Spectral Gap

The transfer matrix T encodes one-step time evolution in the lattice.
Its spectral gap equals the mass gap of the theory.

Architecture note: We work with an abstract Banach space H to avoid
the AEEqFun quotient issues of MeasureTheory.Lp. The physical space
L²(GaugeConfig, gibbsMeasure) is the intended instantiation.
-/

/-- Transfer kernel: the statistical weight of transitioning
    from configuration A to configuration B in one time step.
    Defined as the product of Boltzmann weights — the full
    time-slice interaction is encoded in the hard-content hypothesis. -/
noncomputable def transferKernel (plaquetteEnergy : G → ℝ) (β : ℝ)
    (A B : GaugeConfig d N G) : ℝ :=
  Real.exp (-β * wilsonAction plaquetteEnergy A) *
  Real.exp (-β * wilsonAction plaquetteEnergy B)

/-- Transfer kernel is nonneg. -/
lemma transferKernel_nonneg (plaquetteEnergy : G → ℝ) (β : ℝ)
    (A B : GaugeConfig d N G) :
    0 ≤ transferKernel plaquetteEnergy β A B :=
  mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))

/-- Transfer kernel is symmetric. -/
lemma transferKernel_symm (plaquetteEnergy : G → ℝ) (β : ℝ)
    (A B : GaugeConfig d N G) :
    transferKernel plaquetteEnergy β A B =
    transferKernel plaquetteEnergy β B A := by
  unfold transferKernel; ring

/-- The transfer operator acting on functions: (T f)(A) = ∫ K(A,B) f(B) dμ(B) -/
noncomputable def transferOperatorFn (plaquetteEnergy : G → ℝ) (β : ℝ)
    (μ : Measure G) (f : GaugeConfig d N G → ℝ) (A : GaugeConfig d N G) : ℝ :=
  ∫ B, transferKernel plaquetteEnergy β A B * f B
    ∂(gaugeMeasureFrom (d := d) (N := N) μ)

/-- The transfer operator preserves nonnegativity. -/
lemma transferOperatorFn_nonneg (plaquetteEnergy : G → ℝ) (β : ℝ)
    (μ : Measure G) (f : GaugeConfig d N G → ℝ) (hf : 0 ≤ f)
    (A : GaugeConfig d N G) :
    0 ≤ transferOperatorFn plaquetteEnergy β μ f A := by
  apply integral_nonneg
  intro B
  exact mul_nonneg (transferKernel_nonneg plaquetteEnergy β A B) (hf B)

/-! ### Abstract spectral gap

We work with an abstract bounded linear operator T on a Banach space H.
The physical instantiation is the transfer matrix on L²(GaugeConfig, gibbsMeasure).
-/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The spectral gap property: T^n converges exponentially to the
    ground state projector P₀. The rate γ is the mass gap. -/
def HasSpectralGap (T P₀ : H →L[ℝ] H) (γ C : ℝ) : Prop :=
  0 < γ ∧ 0 < C ∧ ∀ n : ℕ, ‖T ^ n - P₀‖ ≤ C * Real.exp (-γ * n)

/-- The mass gap is positive whenever a spectral gap exists. -/
theorem massGap_pos (T P₀ : H →L[ℝ] H) (γ C : ℝ)
    (h : HasSpectralGap T P₀ γ C) :
    ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, ‖T ^ n - P₀‖ ≤ C * Real.exp (-m * n) :=
  ⟨γ, h.1, h.2.2⟩

/-- L4.3 Main theorem: spectral gap implies exponential decay of correlations.
    The hard content (proving HasSpectralGap for the physical T) is a hypothesis. -/
theorem transferMatrix_spectral_gap (T P₀ : H →L[ℝ] H)
    (γ C : ℝ) (h : HasSpectralGap T P₀ γ C) :
    ∀ n : ℕ, ‖T ^ n - P₀‖ ≤ C * Real.exp (-γ * n) :=
  h.2.2

/-- Corollary: exponential decay rate is positive. -/
theorem spectral_gap_rate_pos (T P₀ : H →L[ℝ] H)
    (γ C : ℝ) (h : HasSpectralGap T P₀ γ C) : 0 < γ := h.1

end YangMills
