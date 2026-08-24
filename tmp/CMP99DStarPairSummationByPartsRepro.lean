import YangMills.RG.FiniteTorusCurlDiv

/-!
Minimal PRE-VALIDATION elaboration repro for the sign in CMP99 (3.36).
This is not a promoted project module and carries no physical-source claim.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

variable {d N : ℕ} [NeZero N]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pure finite reindexing used by the physical adjointness proof. -/
theorem cmp99SumOrderedPairSplit_repro
    {ι M : Type*} [Fintype ι] [LinearOrder ι] [AddCommMonoid M]
    (lower upper : ι → ι → M) :
    (∑ nu : ι, ∑ mu : ι,
        if mu < nu then lower mu nu
        else if nu < mu then upper nu mu
        else 0) =
      ∑ mu : ι, ∑ nu : ι,
        if mu < nu then lower mu nu + upper mu nu else 0 := by
  classical
  calc
    _ = (∑ nu : ι, ∑ mu : ι,
          if mu < nu then lower mu nu else 0) +
        (∑ nu : ι, ∑ mu : ι,
          if nu < mu then upper nu mu else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro nu _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro mu _
      by_cases hmunu : mu < nu
      · simp [hmunu, hmunu.asymm]
      · by_cases hnumu : nu < mu
        · simp [hmunu, hnumu]
        · simp [hmunu, hnumu]
    _ = (∑ mu : ι, ∑ nu : ι,
          if mu < nu then lower mu nu else 0) +
        (∑ mu : ι, ∑ nu : ι,
          if mu < nu then upper mu nu else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ mu : ι, ∑ nu : ι,
          (if mu < nu then lower mu nu else 0) +
          (if mu < nu then upper mu nu else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ∑ mu : ι, ∑ nu : ι,
          if mu < nu then lower mu nu + upper mu nu else 0 := by
      apply Finset.sum_congr rfl
      intro mu _
      apply Finset.sum_congr rfl
      intro nu _
      by_cases hmunu : mu < nu <;> simp [hmunu]

def cmp99PhysicalPlaquetteSigmaEquiv_repro :
    ConcretePlaquette d N ≃
      Σ x : FinBox d N, Σ mu : Fin d, {nu : Fin d // mu < nu} where
  toFun := fun p => ⟨p.site, p.dir1, ⟨p.dir2, p.hlt⟩⟩
  invFun := fun q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv := by rintro ⟨x, mu, nu, hmunu⟩; rfl
  right_inv := by rintro ⟨x, mu, nu, hmunu⟩; rfl

theorem cmp99SumPhysicalPlaquette_eq_sigma_repro
    {M : Type*} [AddCommMonoid M] (f : ConcretePlaquette d N → M) :
    (∑ p : ConcretePlaquette d N, f p) =
      ∑ x : FinBox d N, ∑ mu : Fin d, ∑ nu : {nu : Fin d // mu < nu},
        f ⟨x, mu, nu.1, nu.2⟩ := by
  let e := cmp99PhysicalPlaquetteSigmaEquiv_repro (d := d) (N := N)
  calc
    _ = ∑ q : Σ x : FinBox d N, Σ mu : Fin d, {nu : Fin d // mu < nu},
          f (e.symm q) := by
      exact Fintype.sum_equiv e _ _ (fun p => by simp)
    _ = _ := by
      rw [Fintype.sum_sigma, Fintype.sum_sigma]

/-- One independent direction pair contributes exactly one scaled curl term
to the codifferential pairing. -/
theorem cmp99DStarPairSummationByParts_repro
    (eta : ℝ) (A : FinBox d N → Fin d → V)
    (F : FinBox d N → V) (mu nu : Fin d) :
    (∑ x : FinBox d N,
        inner ℝ (A x nu) ((-eta⁻¹) • torusBackwardDiff mu F x))
      + (∑ x : FinBox d N,
          inner ℝ (A x mu) (eta⁻¹ • torusBackwardDiff nu F x)) =
        ∑ x : FinBox d N,
          inner ℝ (eta⁻¹ • torusCurl A mu nu x) (F x) := by
  have hmu := sum_inner_torusBackwardDiff
    (fun x : FinBox d N => A x nu) F mu
  have hnu := sum_inner_torusBackwardDiff
    (fun x : FinBox d N => A x mu) F nu
  simp only [inner_smul_right, inner_smul_left, RCLike.conj_to_real,
    torusCurl, inner_sub_left]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hmu, hnu]
  ring

#print axioms YangMills.RG.cmp99DStarPairSummationByParts_repro
#print axioms YangMills.RG.cmp99SumOrderedPairSplit_repro
#print axioms YangMills.RG.cmp99PhysicalPlaquetteSigmaEquiv_repro
#print axioms YangMills.RG.cmp99SumPhysicalPlaquette_eq_sigma_repro

end YangMills.RG
