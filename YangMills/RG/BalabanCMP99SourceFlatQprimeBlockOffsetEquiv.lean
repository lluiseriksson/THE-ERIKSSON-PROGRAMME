/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99BlockContour

/-!
# Internal offsets are exactly one physical owner block

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

The one-block Fourier amplitude is indexed by `FinBox d M`, whereas the
literal CMP99 block average sums over fine sites certified to belong to one
coarse owner block.  This file constructs the missing equivalence between
those two finite carriers from `cmp99BlockEmbed` and
`cmp99BlockOffsetOfMem`.

Honest scope: this is an exact carrier dictionary only.  It does not evaluate
the transported block average on a Fourier mode, choose a gauge transport,
identify the weighted adjoint, or diagonalize `Q'^* Q'`.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {d M N' : ℕ} [NeZero d] [NeZero M] [NeZero N']

/-- Recovering the internal offset of an embedded block site is exact. -/
@[simp] theorem cmp99BlockOffsetOfMem_embed
    (y : FinBox d N') (r : FinBox d M) :
    cmp99BlockOffsetOfMem y (cmp99BlockEmbed y r)
        (cmp99BlockEmbed_mem_blockOf y r) = r := by
  funext i
  apply Fin.ext
  simp only [cmp99BlockOffsetOfMem, cmp99BlockEmbed]
  omega

/-- Canonical equivalence between internal offsets and the complete fine
sites of one owner block. -/
def cmp99BlockOffsetEquiv (y : FinBox d N') :
    FinBox d M ≃
      {x : FinBox d (M * N') // x ∈ blockOf M N' y} where
  toFun r := ⟨cmp99BlockEmbed y r, cmp99BlockEmbed_mem_blockOf y r⟩
  invFun x := cmp99BlockOffsetOfMem y x.1 x.2
  left_inv r := cmp99BlockOffsetOfMem_embed y r
  right_inv x := by
    apply Subtype.ext
    exact cmp99BlockEmbed_offsetOfMem y x.1 x.2

/-- Reindex a sum over one complete physical owner block by its literal
`M^d` internal offsets. -/
theorem sum_blockSites_eq_sum_offsets
    {A : Type*} [AddCommMonoid A]
    (y : FinBox d N')
    (f : {x : FinBox d (M * N') // x ∈ blockOf M N' y} → A) :
    (∑ x, f x) = ∑ r : FinBox d M, f (cmp99BlockOffsetEquiv y r) := by
  simpa using ((cmp99BlockOffsetEquiv y).sum_comp f).symm

end

end YangMills.RG
