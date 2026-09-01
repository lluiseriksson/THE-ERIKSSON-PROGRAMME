import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointPhase

/-!
# PRE-VALIDATION: CMP89 (2.48) is not a same-scale endpoint kernel

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

CMP89 (2.48) is the kernel of `G_j Q_j^*`: its target is a fine-lattice site
and its source is a unit/coarse-lattice site.  The sealed source dictionary
therefore uses the fine displacement `x - M*y`, equivalently the negative of
`cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement`.

This module records a concrete arithmetic counterexample to replacing that
typed displacement by the same-scale expression `x-y`.  It does not claim
that two analytic kernel values are unequal; it refutes only the endpoint
identification at exactly the level where the convention is chosen.
-/

namespace YangMills.RG

open YangMills

/-- At block factor two, the same integer representatives denote different
physical endpoints when the source coordinate belongs to the coarse lattice.
Thus `x-y` cannot definitionally replace the source-faithful fine-to-coarse
displacement `x-2*y`. -/
theorem cmp89Eq248_sameScaleEndpoint_ne_fineToCoarseEndpoint_example :
    let x : FinBox 1 (2 * 2) := fun _ => ⟨0, by norm_num⟩
    let y : FinBox 1 2 := fun _ => ⟨1, by norm_num⟩
    (fun mu => ((x mu).val : ℤ) - ((y mu).val : ℤ)) ≠
      (fun mu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement 2 x y mu) := by
  dsimp [cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement]
  intro h
  have h0 := congrFun h (0 : Fin 1)
  norm_num at h0

end YangMills.RG
