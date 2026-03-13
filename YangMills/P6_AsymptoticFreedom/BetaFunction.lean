import Mathlib
import YangMills.P4_Continuum.Phase4Assembly

namespace YangMills

open MeasureTheory Real Filter

/-! ## F6.1: Beta Function — discrete RG coupling recursion

F6.1 scope: algebraic-discrete layer only.
Analytic limits deferred to F6.2.
-/

noncomputable def betaCoeff (N : ℕ) : ℝ := 11 * N / (48 * π ^ 2)

theorem betaCoeff_pos (N : ℕ) (hN : 0 < N) : 0 < betaCoeff N := by
  unfold betaCoeff
  apply div_pos
  · exact mul_pos (by norm_num) (Nat.cast_pos.mpr hN)
  · exact mul_pos (by norm_num) (pow_pos pi_pos 2)

theorem betaCoeff_nonneg (N : ℕ) : 0 ≤ betaCoeff N :=
  div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
    (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt pi_pos) 2))

def InvCouplingSeq (b0 : ℝ) (r : ℕ → ℝ) (g0_inv_sq : ℝ) : ℕ → ℝ
  | 0 => g0_inv_sq
  | k + 1 => InvCouplingSeq b0 r g0_inv_sq k + b0 + r k

theorem invCoupling_mono (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 ≤ b0) (hr : ∀ k, 0 ≤ r k) :
    Monotone (InvCouplingSeq b0 r g0_inv_sq) := by
  apply monotone_nat_of_le_succ
  intro k
  simp [InvCouplingSeq]
  linarith [hr k]

theorem invCoupling_lower_bound (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hr : ∀ k, 0 ≤ r k) :
    ∀ k : ℕ, g0_inv_sq + k * b0 ≤ InvCouplingSeq b0 r g0_inv_sq k := by
  intro k
  induction k with
  | zero => simp [InvCouplingSeq]
  | succ n ih =>
    simp [InvCouplingSeq]
    push_cast
    linarith [hr n]

theorem invCoupling_pos (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 ≤ b0) (hg0 : 0 < g0_inv_sq) (hr : ∀ k, 0 ≤ r k) :
    ∀ k : ℕ, 0 < InvCouplingSeq b0 r g0_inv_sq k := by
  intro k
  have hbound := invCoupling_lower_bound b0 g0_inv_sq r hr k
  have hk : 0 ≤ (k : ℝ) * b0 := mul_nonneg (Nat.cast_nonneg k) hb0
  linarith

noncomputable def CouplingSeq (b0 : ℝ) (r : ℕ → ℝ) (g0_inv_sq : ℝ) (k : ℕ) : ℝ :=
  1 / InvCouplingSeq b0 r g0_inv_sq k

theorem couplingSeq_pos (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 ≤ b0) (hg0 : 0 < g0_inv_sq) (hr : ∀ k, 0 ≤ r k) :
    ∀ k : ℕ, 0 < CouplingSeq b0 r g0_inv_sq k :=
  fun k => div_pos one_pos (invCoupling_pos b0 g0_inv_sq r hb0 hg0 hr k)

theorem couplingSeq_antitone (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 ≤ b0) (hg0 : 0 < g0_inv_sq) (hr : ∀ k, 0 ≤ r k) :
    Antitone (CouplingSeq b0 r g0_inv_sq) := by
  intro m n hmn
  unfold CouplingSeq
  apply div_le_div_of_nonneg_left one_pos.le
    (invCoupling_pos b0 g0_inv_sq r hb0 hg0 hr m)
  exact invCoupling_mono b0 g0_inv_sq r hb0 hr hmn

/-- Abstract predicate: coupling vanishes in UV. Proof in F6.2. -/
def CouplingVanishesUV (b0 : ℝ) (r : ℕ → ℝ) (g0_inv_sq : ℝ) : Prop :=
  Tendsto (CouplingSeq b0 r g0_inv_sq) atTop (nhds 0)

def HasBetaAsymptotics (b0 : ℝ) (r : ℕ → ℝ) (g0_inv_sq : ℝ) : Prop :=
  0 < b0 ∧ 0 < g0_inv_sq ∧ (∀ k, 0 ≤ r k) ∧ CouplingVanishesUV b0 r g0_inv_sq

def HasBetaFunctionControl (m_lat : LatticeMassProfile) (b0 : ℝ) : Prop :=
  0 < b0 ∧ ∃ C : ℝ, ∀ N : ℕ, m_lat N ≤ C * (1 / (N + 1))

theorem asymptoticFreedom_of_convergence
    (m_lat : LatticeMassProfile)
    (m_phys : ℝ) (hm : 0 < m_phys)
    (hconv : Tendsto (renormalizedMass m_lat) atTop (nhds m_phys)) :
    HasAsymptoticFreedomControl m_lat :=
  ⟨m_phys, hm, hconv⟩

/-- F6.1 terminal: b0 > 0 + lower bound framework. -/
theorem phase6_betaFunction_framework (N : ℕ) (hN : 0 < N) :
    0 < betaCoeff N ∧
    ∀ (r : ℕ → ℝ) (g0_inv_sq : ℝ) (hr : ∀ k, 0 ≤ r k) (k : ℕ),
      g0_inv_sq + k * betaCoeff N ≤ InvCouplingSeq (betaCoeff N) r g0_inv_sq k :=
  ⟨betaCoeff_pos N hN,
   fun r g0_inv_sq hr k =>
     invCoupling_lower_bound (betaCoeff N) g0_inv_sq r hr k⟩

end YangMills
