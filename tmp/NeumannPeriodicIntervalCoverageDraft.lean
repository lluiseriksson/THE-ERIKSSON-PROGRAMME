import YangMills.RG.NeumannImageIntervalCoverage

/-!
PRE-VALIDATION: source present; .olean not materialized; compiler result
not verified. Independent M1/M2 draft, not part of the running cold gate.

FULL directions use one periodic branch, not two reflecting branches.
Coverage varies both translation and the original half-open interval point.
This is not a Green identity, summability theorem or physical inverse.
Period P and owner divisor B remain distinct quantities.
-/

namespace YangMills.RG

theorem neumannPeriodicInterval_periodQuotient
    (P : ℤ) (hP : 0 < P) (n : neumannImageIntervalPoint P) (k : ℤ) :
    (n.1 + P * k) / P = k := by
  rw [Int.ediv_eq_iff_of_pos hP]
  have hn0 := n.2.1
  have hn1 := n.2.2
  constructor <;> nlinarith

theorem neumannPeriodicInterval_periodRemainder
    (P : ℤ) (hP : 0 < P) (n : neumannImageIntervalPoint P) (k : ℤ) :
    (n.1 + P * k) % P = n.1 := by
  have h := Int.ediv_mul_add_emod (n.1 + P * k) P
  rw [neumannPeriodicInterval_periodQuotient P hP n k] at h
  nlinarith

/-- The source point varies here. No unused reflection bit is admitted. -/
theorem neumannPeriodicIntervalFamily_injective (P : ℤ) (hP : 0 < P) :
    Function.Injective (fun p : ℤ × neumannImageIntervalPoint P =>
      p.2.1 + P * p.1) := by
  rintro ⟨k,n⟩ ⟨l,v⟩ he
  change n.1 + P * k = v.1 + P * l at he
  have hq := congrArg (fun u : ℤ => u / P) he
  have hr := congrArg (fun u : ℤ => u % P) he
  rw [neumannPeriodicInterval_periodQuotient P hP n k,
    neumannPeriodicInterval_periodQuotient P hP v l] at hq
  rw [neumannPeriodicInterval_periodRemainder P hP n k,
    neumannPeriodicInterval_periodRemainder P hP v l] at hr
  exact Prod.ext hq (Subtype.ext hr)

/-- Euclidean remainder includes negative lattice sites without clipping. -/
theorem neumannPeriodicIntervalFamily_surjective (P : ℤ) (hP : 0 < P) :
    Function.Surjective (fun p : ℤ × neumannImageIntervalPoint P =>
      p.2.1 + P * p.1) := by
  intro u
  have hr0 := Int.emod_nonneg u (ne_of_gt hP)
  have hr1 := Int.emod_lt_of_pos u hP
  have hu := Int.ediv_mul_add_emod u P
  refine ⟨⟨u / P, ⟨u % P, hr0, hr1⟩⟩, ?_⟩
  change u % P + P * (u / P) = u
  nlinarith

theorem neumannPeriodicIntervalFamily_bijective (P : ℤ) (hP : 0 < P) :
    Function.Bijective (fun p : ℤ × neumannImageIntervalPoint P =>
      p.2.1 + P * p.1) :=
  ⟨neumannPeriodicIntervalFamily_injective P hP,
    neumannPeriodicIntervalFamily_surjective P hP⟩

/-- FULL periodic shift in fine units, with owner in block units.
No averaging coefficient or fibre cardinality is introduced. -/
theorem neumannIntegerPeriodicOwner
    (B N n k : ℤ) (hB : 0 < B) :
    (n + B * (k * N)) / B = n / B + k * N := by
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt hB)]

end YangMills.RG

#print axioms YangMills.RG.neumannPeriodicInterval_periodQuotient
#print axioms YangMills.RG.neumannPeriodicInterval_periodRemainder
#print axioms YangMills.RG.neumannPeriodicIntervalFamily_injective
#print axioms YangMills.RG.neumannPeriodicIntervalFamily_surjective
#print axioms YangMills.RG.neumannPeriodicIntervalFamily_bijective
#print axioms YangMills.RG.neumannIntegerPeriodicOwner
