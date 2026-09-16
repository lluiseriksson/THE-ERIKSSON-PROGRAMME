import YangMills.RG.BalabanCMP99SourceGeneratedScaledGradient
open YangMills YangMills.RG

theorem chain_unique {d M N depth : ℕ} [NeZero M]
    {Omega : ActiveGaugeRegion d N}
    (a b : CMP99SourceActiveRegionChain d M N Omega depth) : a = b := by
  induction a with
  | stop Omega => cases b; rfl
  | step Omega h tail ih =>
      cases b with
      | step Omega h' tail' =>
          have ht : tail = tail' := ih tail'
          cases ht
          rfl

#check congrArg
#check congrArg₂
#check HEq.trans
#check heq_iff_eq
#check eqRec_heq_iff_heq
#check cast_heq
