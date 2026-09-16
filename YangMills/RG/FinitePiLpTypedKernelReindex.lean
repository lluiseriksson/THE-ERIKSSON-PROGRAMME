/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernel

/-!
# Isometric reindexing of finite typed kernels

Dependent regional towers expose physically identical finite carriers through
different index types.  This file reindexes rectangular kernels by literal
finite equivalences and proves that exponential kernel bounds are preserved.
Unlike transport through type equality, this construction does not rely on
definitional equality of independently synthesized `Fintype` instances.
-/

namespace YangMills.RG

noncomputable section

universe u v w u' v'

/-- Reindexing by an equality cast is heterogeneously the identity.  This
lemma lets explicit isometric reindexing interact with dependent bundle
transport without eliminating a concrete recursive type equality. -/
theorem finitePiLpCongrLeft_cast_heq
    {ι ι' : Type u} {g : Type w}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (h : ι = ι') (f : FinitePiLpField ι g) :
    HEq ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
      (Equiv.cast h)).toContinuousLinearEquiv f) f := by
  subst ι'
  rfl

/-- Reindex both legs of a finite rectangular kernel through isometric
coordinate permutations. -/
noncomputable def finitePiLpTypedKernelReindex
    {ι : Type u} {κ : Type v} {ι' : Type u'} {κ' : Type v'} {g : Type w}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (sourceEquiv : ι ≃ ι') (targetEquiv : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    FinitePiLpField ι' g →L[ℝ] FinitePiLpField κ' g :=
  let sourceBack :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
      sourceEquiv.symm).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g targetEquiv).toContinuousLinearEquiv
  targetMap.toContinuousLinearMap.comp
    (T.comp sourceBack.toContinuousLinearMap)

/-- Isometric finite reindexing preserves an exponential kernel estimate,
with the distance pulled back through the same two coordinate equivalences. -/
theorem finitePiLpTypedExponentialKernelBound_reindex
    {ι : Type u} {κ : Type v} {ι' : Type u'} {κ' : Type v'} {g : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (sourceEquiv : ι ≃ ι') (targetEquiv : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g)
    (dist : κ → ι → ℕ) {A rate : ℝ}
    (hT : FinitePiLpTypedExponentialKernelBound T dist A rate) :
    FinitePiLpTypedExponentialKernelBound
      (finitePiLpTypedKernelReindex sourceEquiv targetEquiv T)
      (fun target source =>
        dist (targetEquiv.symm target) (sourceEquiv.symm source)) A rate := by
  refine ⟨hT.1, hT.2.1, ?_⟩
  intro source target v
  let sourceBack :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g
      sourceEquiv.symm).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g targetEquiv).toContinuousLinearEquiv
  have hsingle : sourceBack (singleFinitePiLp source v) =
      singleFinitePiLp (sourceEquiv.symm source) v := by
    rw [singleFinitePiLp_eq_toLp_single,
      singleFinitePiLp_eq_toLp_single]
    simpa only [sourceBack] using
      (LinearIsometryEquiv.piLpCongrLeft_single
        (p := (2 : ENNReal)) (𝕜 := ℝ) sourceEquiv.symm source v)
  have heval (f : FinitePiLpField κ g) :
      targetMap f target = f (targetEquiv.symm target) := by
    rfl
  change ‖targetMap (T (sourceBack (singleFinitePiLp source v))) target‖ ≤ _
  rw [hsingle, heval]
  exact hT.2.2 (sourceEquiv.symm source) (targetEquiv.symm target) v

end
end YangMills.RG
