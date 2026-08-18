import Mathlib

/-!
PRE-VALIDATION MINIMAL REPRODUCER: this file isolates the typed averaging
rewrite used by the P3 Schur layer.  It imports no project declaration and is
not compiler evidence for the physical chain.
-/

noncomputable section

example
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (P S C : K →L[ℝ] K) (b c : ℝ) (x : K)
    (hbase : b • C x - b ^ 2 • S (C x) + c • P (C x) = x) :
    x + b ^ 2 • S (C x) = b • C x + c • P (C x) := by
  rw [← hbase]
  abel_nf

example
    {K L : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    (R : K →L[ℝ] L) (P S C : K →L[ℝ] K) (b c : ℝ)
    (hRP : R.comp P = R)
    (hlinear : ∀ x,
      x + b ^ 2 • S (C x) = b • C x + c • P (C x)) :
    R.comp
        (ContinuousLinearMap.id ℝ K + b ^ 2 • S.comp C) =
      (b + c) • R.comp C := by
  apply ContinuousLinearMap.ext
  intro x
  have hRlinear := congrArg R (hlinear x)
  have hRPx : R (P (C x)) = R (C x) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : K →L[ℝ] L => T (C x)) hRP
  simp only [map_add, map_smul] at hRlinear
  rw [hRPx] at hRlinear
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_smul, add_smul] using
      hRlinear

end
