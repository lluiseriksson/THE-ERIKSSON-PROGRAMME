import YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Uniqueness of the finite CMP89 (2.46) alias system

The explicit stabilized solver already produces a solution for every source.
Because the alias fibre is finite and the precision is a square linear map,
surjectivity gives injectivity. This is the uniqueness input needed to
transport the complete point-source solution through the centered-alias
cycle; it introduces no inverse family and no extra analytic hypothesis.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Under the same literal nonvanishing gates used by the explicit solver,
the finite alias precision has at most one solution for each source. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_injective
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin d → ℂ)
    (hfine : ∀ m : CMP89Eq246AliasIndex d L j,
      m ≠ cmp89Eq249CentralAliasIndex d L j →
        cmp89Eq246EntireAliasFineSymbol d L j mass z m ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z ≠ 0)
    (hrow : cmp89Eq246EntireAliasAverageRow d L j z
        (cmp89Eq249CentralAliasIndex d L j) ≠ 0) :
    Function.Injective
      (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec := by
  let A := cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z
  have hsurj : Function.Surjective A.mulVec := by
    intro source
    refine ⟨cmp89Eq246StabilizedAliasFullSolution
      d L j mass a z source, ?_⟩
    exact cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution
      d L j mass a z source hfine hstabilized hrow
  have hsurjLin : Function.Surjective A.mulVecLin := by
    simpa only [Matrix.mulVecLin_apply] using hsurj
  have hinjLin : Function.Injective A.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).2 hsurjLin
  simpa only [Matrix.mulVecLin_apply] using hinjLin

end

end YangMills.RG
