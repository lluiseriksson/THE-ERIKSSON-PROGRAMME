import YangMills.RG.BalabanCMP102Eq80SourcePi4FaaDiBrunoPhysicalDomainExpansionAt
#check WithTop.coe_le_coe
#check ENat.coe_le_coe
#check Nat.cast_le
#check OrderedFinpartition.length_le
example {n : ℕ} (p : OrderedFinpartition n) :
    (p.length : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr (OrderedFinpartition.length_le p))
