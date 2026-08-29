import YangMills.RG.FinitePiLpTypedKernelReindexAlgebra

/-!
SCRATCH ONLY: this file is neither imported nor compiler-verified and is not
evidence.

# Rectangular algebra for finite kernel reindexing

The existing sealed algebra treats square operators.  Covariant derivatives
are rectangular (sites to bonds), so the physical C6d dictionary needs the
same composition and adjoint laws with three independently pinned carriers.
-/

namespace YangMills.RG

noncomputable section

universe u v w u' v' w' z

/-- Rectangular reindexing preserves an ordered composition when the middle
carrier uses the same explicit equivalence on both sides. -/
theorem finitePiLpTypedKernelReindex_rect_comp
    {ι : Type u} {κ : Type v} {λ : Type w}
    {ι' : Type u'} {κ' : Type v'} {λ' : Type w'} {g : Type z}
    [Fintype ι] [Fintype κ] [Fintype λ]
    [Fintype ι'] [Fintype κ'] [Fintype λ']
    [NormedAddCommGroup g] [NormedSpace ℝ g]
    (eι : ι ≃ ι') (eκ : κ ≃ κ') (eλ : λ ≃ λ')
    (S : FinitePiLpField κ g →L[ℝ] FinitePiLpField λ g)
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    (finitePiLpTypedKernelReindex eκ eλ S).comp
        (finitePiLpTypedKernelReindex eι eκ T) =
      finitePiLpTypedKernelReindex eι eλ (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  simp [finitePiLpTypedKernelReindex,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- Taking the adjoint swaps the two explicit coordinate equivalences. -/
theorem finitePiLpTypedKernelReindex_adjoint
    {ι : Type u} {κ : Type v} {ι' : Type u'} {κ' : Type v'} {g : Type z}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [CompleteSpace g]
    (eι : ι ≃ ι') (eκ : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    (finitePiLpTypedKernelReindex eι eκ T).adjoint =
      finitePiLpTypedKernelReindex eκ eι T.adjoint := by
  unfold finitePiLpTypedKernelReindex
  simp only [ContinuousLinearMap.adjoint_comp]
  simp

/-- The Gram operator of a rectangular kernel transports as a square
operator on its source carrier. -/
theorem finitePiLpTypedKernelReindex_adjoint_comp_self
    {ι : Type u} {κ : Type v} {ι' : Type u'} {κ' : Type v'} {g : Type z}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [CompleteSpace g]
    (eι : ι ≃ ι') (eκ : κ ≃ κ')
    (T : FinitePiLpField ι g →L[ℝ] FinitePiLpField κ g) :
    finitePiLpTypedKernelReindex eι eι (T.adjoint.comp T) =
      (finitePiLpTypedKernelReindex eι eκ T).adjoint.comp
        (finitePiLpTypedKernelReindex eι eκ T) := by
  rw [finitePiLpTypedKernelReindex_adjoint]
  exact (finitePiLpTypedKernelReindex_rect_comp eι eκ eι
    T.adjoint T).symm

end

end YangMills.RG
