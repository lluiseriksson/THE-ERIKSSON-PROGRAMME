import YangMills.OS.SpatialReconstruction
import YangMills.OS.DobrushinCorollary
import YangMills.OS.DobrushinTilt
import YangMills.OS.DobrushinTransport
import YangMills.OS.TransferGap

/-!
# Volume-uniform Osterwalder--Schrader reconstruction

This module is the mathematical lane associated with the separate provenance
cleanup in task (52). It composes the already verified spatial reconstruction
and Dobrushin transport layers. No numerical estimate is introduced here.
-/

open scoped BigOperators
open Finset

namespace YangMills.OS

open Dobrushin

variable {L : ℕ}

/-- Dress a real Euclidean boundary vector by `sqrt w` and regard it as a
complex vector in the reconstructed site space. -/
noncomputable def qEmbed (w : (Fin L → Fin 2) → ℝ)
    (u : (Fin L → Fin 2) → ℝ) : (Fin L → Fin 2) → ℂ :=
  fun σ => ((Real.sqrt (w σ) : ℝ) : ℂ) * ((u σ : ℝ) : ℂ)

/-- The dressing map is an isometry from the real Euclidean pairing to the
site form whenever the spatial weight is strictly positive. -/
theorem siteForm_qEmbed (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (u v : (Fin L → Fin 2) → ℝ) :
    siteForm w (qEmbed w u) (qEmbed w v) = ((∑ σ, u σ * v σ : ℝ) : ℂ) := by
  unfold siteForm qEmbed
  push_cast
  refine Finset.sum_congr
    (M := ℂ)
    (s₁ := (Finset.univ : Finset (Fin L → Fin 2)))
    (s₂ := Finset.univ) rfl ?_
  intro σ _
  rw [map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  have hs : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
    Real.mul_self_sqrt (hw σ).le
  have hσ : w σ ≠ 0 := (hw σ).ne'
  norm_cast
  field_simp
  have hs' : Real.sqrt (w σ) ^ 2 = w σ := by nlinarith [hs]
  rw [hs']
  ring

/-- Conjugating the forced reconstructed transfer operator by the dressing
map gives the symmetric weighted kernel. -/
theorem transferOp_qEmbed (w : (Fin L → Fin 2) → ℝ) (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (u : (Fin L → Fin 2) → ℝ) :
    transferOp w β (qEmbed w u)
      = qEmbed w (act (symWeighted w β) u) := by
  funext σ
  change transferOp w β
    (fun τ => ((Real.sqrt (w τ) : ℝ) : ℂ) * ((u τ : ℝ) : ℂ)) σ = _
  rw [transferOp_sqrtw (fun τ => (hw τ).le) β
    (fun τ => ((u τ : ℝ) : ℂ)) σ]
  unfold qEmbed act
  push_cast
  congr 1

/-- The preceding conjugation transports every finite power of the transfer
operator, not merely one step. -/
theorem transferOp_iterate_qEmbed (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (n : ℕ)
    (u : (Fin L → Fin 2) → ℝ) :
    (transferOp w β)^[n] (qEmbed w u)
      = qEmbed w ((act (symWeighted w β))^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact transferOp_qEmbed w hw β ((act (symWeighted w β))^[n] u)

/-- After Perron normalisation, the reconstructed transfer operator is
conjugate in one step to the Dobrushin tilt kernel. -/
theorem transferOp_qEmbed_tilt (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (β lam : ℝ)
    (u : (Fin L → Fin 2) → ℝ) :
    (lam : ℂ)⁻¹ • transferOp w β (qEmbed w u)
      = qEmbed w (act (fun σ τ => tiltKernel w β lam σ τ) u) := by
  rw [transferOp_qEmbed w hw β u]
  funext σ
  unfold qEmbed act
  simp only [Pi.smul_apply, smul_eq_mul, tiltKernel_apply]
  push_cast
  simp only [div_eq_mul_inv]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr (M := ℂ) rfl fun τ _ => ?_
  ring

/-- The normalised tilt conjugation is stable under every finite iterate. -/
theorem transferOp_qEmbed_tilt_iterate (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (β lam : ℝ) (n : ℕ)
    (u : (Fin L → Fin 2) → ℝ) :
    (((lam : ℂ)⁻¹ • transferOp w β)^[n]) (qEmbed w u)
      = qEmbed w ((act (fun σ τ => tiltKernel w β lam σ τ))^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact transferOp_qEmbed_tilt w hw β lam
        ((act (fun σ τ => tiltKernel w β lam σ τ))^[n] u)

/-- In the explicit Dobrushin window, one positive exponent works for every
spatial extent. The final clause records the exact conjugation that reads the
uniform tilt gap on the forced reconstructed transfer operator. -/
theorem os_reconstruction_uniform_gap (β γ : ℝ) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ‖projectedTransfer (opOf (tiltKernel (sliceW γ L) β lam))
            (vacOf Om)‖ ≤ Real.exp (-m) ∧
        (∀ u,
          (lam : ℂ)⁻¹ • transferOp (sliceW γ L) β
              (qEmbed (sliceW γ L) u)
            = qEmbed (sliceW γ L)
                (act (fun σ τ => tiltKernel (sliceW γ L) β lam σ τ) u)) := by
  obtain ⟨m, hm, hL⟩ := dobrushin_ising_uniform_gap β γ hα0 hα1 hwin
  refine ⟨m, hm, fun L => ?_⟩
  obtain ⟨lam, Om, hlam, hOm, hfix, hnorm⟩ := hL L
  exact ⟨lam, Om, hlam, hOm, hfix, hnorm,
    fun u => transferOp_qEmbed_tilt (sliceW γ L) (sliceW_pos γ L)
      β lam u⟩

end YangMills.OS
