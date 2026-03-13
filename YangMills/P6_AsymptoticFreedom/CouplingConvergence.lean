import Mathlib
import YangMills.P6_AsymptoticFreedom.BetaFunction

namespace YangMills

open MeasureTheory Real Filter Topology

/-! ## F6.2: Coupling Convergence — g_k → 0 and renormalized mass convergence

Pattern: tendsto_atTop_add_const_left for g0 + k*b0 → atTop.
-/

/-- k * b0 → atTop when b0 > 0. -/
theorem mul_const_tendsto_atTop (b0 : ℝ) (hb0 : 0 < b0) :
    Tendsto (fun k : ℕ => (k : ℝ) * b0) atTop atTop :=
  Tendsto.atTop_mul_const hb0 tendsto_natCast_atTop_atTop

/-- g0 + k * b0 → atTop. -/
theorem affine_tendsto_atTop (b0 g0 : ℝ) (hb0 : 0 < b0) :
    Tendsto (fun k : ℕ => g0 + (k : ℝ) * b0) atTop atTop :=
  tendsto_atTop_add_const_left _ g0 (mul_const_tendsto_atTop b0 hb0)

/-- InvCouplingSeq → atTop. -/
theorem invCoupling_tendsto_atTop (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 < b0) (hr : ∀ k, 0 ≤ r k) :
    Tendsto (InvCouplingSeq b0 r g0_inv_sq) atTop atTop :=
  tendsto_atTop_mono (invCoupling_lower_bound b0 g0_inv_sq r hr)
    (affine_tendsto_atTop b0 g0_inv_sq hb0)

/-- 1/x → 0 when x : ℝ → atTop. -/
theorem inv_tendsto_zero_of_atTop :
    Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
  simp_rw [one_div]; exact tendsto_inv_atTop_zero

/-- CouplingVanishesUV: g²_k → 0. -/
theorem coupling_tendsto_zero (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 < b0) (hr : ∀ k, 0 ≤ r k) :
    CouplingVanishesUV b0 r g0_inv_sq := by
  unfold CouplingVanishesUV CouplingSeq
  exact inv_tendsto_zero_of_atTop.comp
    (invCoupling_tendsto_atTop b0 g0_inv_sq r hb0 hr)

/-- HasBetaAsymptotics from positivity. -/
theorem hasBetaAsymptotics_of_pos (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 < b0) (hg0 : 0 < g0_inv_sq) (hr : ∀ k, 0 ≤ r k) :
    HasBetaAsymptotics b0 r g0_inv_sq :=
  ⟨hb0, hg0, hr, coupling_tendsto_zero b0 g0_inv_sq r hb0 hr⟩

/-- Constant mass profile: m_lat N = m_phys * latticeSpacing N. -/
noncomputable def constantMassProfile (m_phys : ℝ) : LatticeMassProfile :=
  fun N => m_phys * latticeSpacing N

theorem constantMassProfile_renormalized (m_phys : ℝ) (N : ℕ) :
    renormalizedMass (constantMassProfile m_phys) N = m_phys := by
  unfold renormalizedMass constantMassProfile latticeSpacing
  have h : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [h]

theorem constantMassProfile_converges (m_phys : ℝ) :
    Tendsto (renormalizedMass (constantMassProfile m_phys)) atTop (nhds m_phys) := by
  have h_eq : renormalizedMass (constantMassProfile m_phys) = fun _ => m_phys :=
    funext (constantMassProfile_renormalized m_phys)
  rw [h_eq]; exact tendsto_const_nhds

theorem constantMassProfile_af (m_phys : ℝ) (hm : 0 < m_phys) :
    HasAsymptoticFreedomControl (constantMassProfile m_phys) :=
  ⟨m_phys, hm, constantMassProfile_converges m_phys⟩

/-- F6.2 terminal. -/
theorem phase6_couplingConvergence
    (b0 g0_inv_sq : ℝ) (r : ℕ → ℝ)
    (hb0 : 0 < b0) (hg0 : 0 < g0_inv_sq) (hr : ∀ k, 0 ≤ r k)
    (m_phys : ℝ) (hm : 0 < m_phys) :
    HasBetaAsymptotics b0 r g0_inv_sq ∧
    HasAsymptoticFreedomControl (constantMassProfile m_phys) :=
  ⟨hasBetaAsymptotics_of_pos b0 g0_inv_sq r hb0 hg0 hr,
   constantMassProfile_af m_phys hm⟩

end YangMills
