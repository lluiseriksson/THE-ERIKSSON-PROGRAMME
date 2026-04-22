/-
  YangMills/ClayCore/SchurL26.lean

  Milestone L2.6 (main target): ∫ |tr U|² dHaar = 1 on SU(N).

  Final character-inner-product identity for the fundamental representation.
  Combines:
    * L2.5 (SchurL25.lean): ∫|tr|² decomposes to a sum of diagonal
      integrals ∫ U_{ii} · star U_{ii}, plus integrability and
      ℝ-coercion infrastructure.
    * L2.6 step 1c (SchurEntryDiagonal.lean): each entry integral
      ∫ U_{ij} · star U_{ij} = 1/N.

  Sum: ∑_{i : Fin N} (1/N) = N · (1/N) = 1.

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].
-/

import YangMills.ClayCore.SchurL25
import YangMills.ClayCore.SchurEntryDiagonal

noncomputable section

open MeasureTheory Matrix Complex Finset
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ} [NeZero N]

/-- Real-valued form of L2.6 step 1c:
    `∫ (normSq U_{ii} : ℝ) dHaar = 1/N` on SU(N). -/
lemma diag_normSq_integral_eq_inv_N (i : Fin N) :
    (∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N)) = (1 : ℝ) / N := by
  have hℂ : (∫ U, U.val i i * star (U.val i i) ∂(sunHaarProb N)) = 1 / (N : ℂ) :=
    sunHaarProb_entry_normSq_eq_inv_N i i
  have hreal := diag_integral_ofReal (N := N) i
  rw [hreal] at hℂ
  have hcast : (((1 : ℝ) / (N : ℝ) : ℝ) : ℂ) = 1 / (N : ℂ) := by
    push_cast; ring
  rw [← hcast] at hℂ
  exact_mod_cast hℂ

/-- **L2.6 main theorem**: `∫ |tr U|² dHaar = 1` on SU(N).

The character inner product `⟨χ_fund, χ_fund⟩` on SU(N) equals `1`,
a concrete Haar-integral witness of the irreducibility of the
fundamental representation. -/
theorem sunHaarProb_trace_normSq_integral_eq_one :
    (∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N)) = 1 := by
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdiag_ℂ : ∀ i : Fin N,
      (∫ U, U.val i i * star (U.val i i) ∂(sunHaarProb N)) = 1 / (N : ℂ) :=
    fun i => sunHaarProb_entry_normSq_eq_inv_N i i
  have htrace_ℂ : (∫ U, U.val.trace * star U.val.trace ∂(sunHaarProb N)) = 1 := by
    rw [integral_trace_mul_conj_trace_eq_sum]
    simp_rw [hdiag_ℂ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hpt : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      U.val.trace * star U.val.trace = ((Complex.normSq U.val.trace : ℝ) : ℂ) :=
    fun U => Complex.mul_conj U.val.trace
  have hIR : (∫ U, U.val.trace * star U.val.trace ∂(sunHaarProb N))
      = ((∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ) := by
    rw [MeasureTheory.integral_congr_ae (ae_of_all _ hpt)]
    exact integral_ofReal
  rw [hIR] at htrace_ℂ
  exact_mod_cast htrace_ℂ

end YangMills.ClayCore

end
