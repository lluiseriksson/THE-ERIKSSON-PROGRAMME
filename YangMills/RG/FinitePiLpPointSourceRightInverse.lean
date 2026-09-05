import YangMills.RG.FinitePiLpCombesThomas

/-!
# Point-source criterion for a finite right inverse

This finite-dimensional algebraic layer reduces an operator right-inverse
identity to the corresponding identities on the literal coordinate point
sources `singleFinitePiLp`.  The converse is recorded as well, so replacing an
operator equality by the point-source family neither weakens nor strengthens
the obligation.

No Green kernel, reflection formula, precision decomposition, decay estimate
or source equation is assumed or proved here.
-/

namespace YangMills.RG

noncomputable section

variable {ι g : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup g] [NormedSpace ℝ g]

/-- Two finite-field continuous linear maps compose to the identity exactly
when they do so on every literal coordinate point source. -/
theorem finitePiLp_comp_eq_id_iff_pointSources
    (A G : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    A.comp G = ContinuousLinearMap.id ℝ (FinitePiLpField ι g) ↔
      ∀ source v,
        A (G (singleFinitePiLp source v)) = singleFinitePiLp source v := by
  constructor
  · intro h source v
    have happ := congrArg
      (fun T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g =>
        T (singleFinitePiLp source v)) h
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using happ
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    calc
      A (G f) = A (G (∑ source,
          singleFinitePiLp source (f source))) := by
        rw [sum_singleFinitePiLp_eq]
      _ = ∑ source,
          A (G (singleFinitePiLp source (f source))) := by
        rw [map_sum, map_sum]
      _ = ∑ source, singleFinitePiLp source (f source) := by
        apply Finset.sum_congr rfl
        intro source _
        exact h source (f source)
      _ = f := sum_singleFinitePiLp_eq f

end

end YangMills.RG
