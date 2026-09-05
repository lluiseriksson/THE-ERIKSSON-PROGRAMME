/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpTypedKernelReindex

/-!
# Exact algebra of finite typed-kernel reindexing

The physical generated precision and Green initially live on an active
counting-Hilbert carrier.  Reindexing both through one explicit finite
equivalence must preserve composition and identity before any complexification
or physical full-box dictionary is used.  This file proves those algebraic
laws for the existing literal isometric reindexing.

No physical operator, inverse, Green field, carrier equality, or complex
dictionary is accepted or identified here.
-/

namespace YangMills.RG

noncomputable section

universe u u' w

/-- The two explicitly opposed coordinate reindexings cancel on the finite
counting-Hilbert carrier.  This is kept named because the cancellation occurs
under an arbitrary continuous linear map in the composition theorem below. -/
private theorem piLpCongrLeft_inverse_apply
    {ι : Type u} {ι' : Type u'} {g : Type w}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι') (phi : FinitePiLpField ι g) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e.symm)
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e) phi) = phi := by
  simpa only [LinearIsometryEquiv.piLpCongrLeft_symm] using
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ g e).symm_apply_apply phi

/-- Reindexing both legs of two square kernels preserves their ordered
composition exactly. -/
theorem finitePiLpTypedKernelReindex_comp
    {ι : Type u} {ι' : Type u'} {g : Type w}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι')
    (S T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g) :
    (finitePiLpTypedKernelReindex e e S).comp
        (finitePiLpTypedKernelReindex e e T) =
      finitePiLpTypedKernelReindex e e (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpTypedKernelReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    piLpCongrLeft_inverse_apply]

/-- Reindexing the real identity through one finite equivalence is the
identity on the reindexed counting-Hilbert carrier. -/
theorem finitePiLpTypedKernelReindex_id
    {ι : Type u} {ι' : Type u'} {g : Type w}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι') :
    finitePiLpTypedKernelReindex e e
        (ContinuousLinearMap.id ℝ (FinitePiLpField ι g)) =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι' g) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpTypedKernelReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- An exact inverse law survives square finite reindexing in the same order.
The order is explicit so this one theorem transports both left- and
right-inverse laws. -/
theorem finitePiLpTypedKernelReindex_comp_eq_id
    {ι : Type u} {ι' : Type u'} {g : Type w}
    [Fintype ι] [Fintype ι']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (e : ι ≃ ι')
    (S T : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (hST : S.comp T =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g)) :
    (finitePiLpTypedKernelReindex e e S).comp
        (finitePiLpTypedKernelReindex e e T) =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι' g) := by
  calc
    (finitePiLpTypedKernelReindex e e S).comp
          (finitePiLpTypedKernelReindex e e T) =
        finitePiLpTypedKernelReindex e e (S.comp T) :=
      finitePiLpTypedKernelReindex_comp e S T
    _ = finitePiLpTypedKernelReindex e e
          (ContinuousLinearMap.id ℝ (FinitePiLpField ι g)) := by rw [hST]
    _ = ContinuousLinearMap.id ℝ (FinitePiLpField ι' g) :=
      finitePiLpTypedKernelReindex_id e

end

end YangMills.RG
