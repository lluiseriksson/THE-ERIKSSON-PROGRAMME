import Mathlib
import YangMills.P8_PhysicalGap.FeynmanKacBridge

namespace YangMills

open MeasureTheory Real

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## P8.API: StateNormBound and HasSpectralGap structural lemmas (C78)

Clean sorry-free API for `StateNormBound` and `HasSpectralGap`.
These are constructor/monotonicity lemmas needed by downstream consumers
who supply concrete observer families or weakened spectral gap estimates.

All results are sorry-free.
Oracle: `[propext, Classical.choice, Quot.sound]`. -/

/-- **C78-1**: Explicit constructor for StateNormBound. -/
theorem stateNormBound_mk
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) (C_ψ : ℝ)
    (hC : 0 ≤ C_ψ)
    (hbound : ∀ (N : ℕ) [NeZero N] (p : ConcretePlaquette d N),
        ‖ψ_obs N p‖ ≤ C_ψ) :
    StateNormBound ψ_obs C_ψ :=
  ⟨hC, hbound⟩

/-- **C78-2**: StateNormBound is monotone in C_ψ. -/
theorem stateNormBound_mono
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) {C₁ C₂ : ℝ}
    (h : StateNormBound ψ_obs C₁) (hle : C₁ ≤ C₂) :
    StateNormBound ψ_obs C₂ := by
  constructor
  · exact le_trans h.1 hle
  · intro N _ p
    exact le_trans (h.2 N p) hle

/-- **C78-3**: Constant observer family has StateNormBound ‖ψ₀‖. -/
theorem stateNormBound_const (ψ₀ : H) :
    StateNormBound (fun (N : ℕ) (_ : ConcretePlaquette d N) => ψ₀) ‖ψ₀‖ := by
  constructor
  · exact norm_nonneg ψ₀
  · intro N _ p
    exact le_refl _

/-- **C78-4**: Zero observer family has StateNormBound 0. -/
theorem stateNormBound_zero :
    StateNormBound (fun (N : ℕ) (_ : ConcretePlaquette d N) => (0 : H)) 0 := by
  constructor
  · exact le_refl 0
  · intro N _ p
    simp

/-- **C78-5**: Scalar multiplication scales the bound. -/
theorem stateNormBound_smul
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) (C_ψ : ℝ) (c : ℝ)
    (h : StateNormBound ψ_obs C_ψ) :
    StateNormBound (fun N p => c • ψ_obs N p) (|c| * C_ψ) := by
  constructor
  · exact mul_nonneg (abs_nonneg c) h.1
  · intro N _ p
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h.2 N p) (abs_nonneg c)

/-- **C78-6**: HasSpectralGap is monotone: weaker γ' ≤ γ and larger C' ≥ C also hold. -/
theorem hasSpectralGap_mono (T P₀ : H →L[ℝ] H) {γ γ' C C' : ℝ}
    (h : HasSpectralGap T P₀ γ C)
    (hγ' : 0 < γ') (hγle : γ' ≤ γ) (hCle : C ≤ C') :
    HasSpectralGap T P₀ γ' C' := by
  refine ⟨hγ', h.2.1.trans_le hCle, fun n => ?_⟩
  have hbound := h.2.2 n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : Real.exp (-γ * ↑n) ≤ Real.exp (-γ' * ↑n) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC'nn : (0 : ℝ) ≤ C' := le_trans h.2.1.le hCle
  linarith [mul_le_mul hCle hexp (Real.exp_pos (-γ * ↑n)).le hC'nn]

/-! ## C82: Geometric decay implies HasSpectralGap -/

/-- **C82-T1 (sorry-free):** Geometric operator-norm bound implies `HasSpectralGap`.

    If `‖T^n - P₀‖ ≤ C · rⁿ` for all `n : ℕ`, with `0 < r < 1` and `0 < C`, then
    `HasSpectralGap T P₀ (-Real.log r) C`.

    Key identity: `rⁿ = exp(n · log r) = exp(-(-log r) · n) = exp(-γ · n)`
    where `γ := -log r > 0` by `Real.log_neg` since `r ∈ (0, 1)`.

    Mathematical significance: Sits on the NON-VACUOUS path to
    `ClayYangMillsPhysicalStrong` via `feynmanKac_to_physicalStrong`, which
    takes `HasSpectralGap T P₀ γ C` as its spectral hypothesis. This lemma
    reduces that hypothesis to a geometric power bound -- the natural form in
    transfer-matrix spectral theory.

    Oracle: propext, Classical.choice, Quot.sound only (0 sorry, 0 axiom). -/
theorem hasSpectralGap_of_geometric_decay
    (T P₀ : H →L[ℝ] H)
    (r C : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 < C)
    (hpow : ∀ n : ℕ, ‖T ^ n - P₀‖ ≤ C * r ^ n) :
    HasSpectralGap T P₀ (-Real.log r) C := by
  refine ⟨neg_pos.mpr (Real.log_neg hr0 hr1), hC, fun n => ?_⟩
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  calc ‖T ^ n - P₀‖
      ≤ C * r ^ n := hpow n
    _ = C * Real.exp (-(-Real.log r) * ↑n) := by
          congr 1
          simp only [neg_neg]
          rw [mul_comm, ← Real.log_pow, Real.exp_log hrn_pos]

end YangMills
