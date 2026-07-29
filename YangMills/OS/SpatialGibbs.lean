import YangMills.OS.PerronGap

/-!
# O-2 — the measure the spectral results were about

Papers 5–8 of this lane studied an **operator**: a strictly positive kernel on
the spatial configuration space `Fin L → Fin 2`, its Perron vacuum, and the
strict separation of its spectrum.  None of them exhibited a **measure**.  That
gap is not cosmetic.  A transfer operator is a matrix until something says which
Gibbs weights it transfers; without that, the vacuum is an eigenvector and the
gap is a statement about eigenvalues, and neither is yet a statement about a
statistical-mechanical system.

The one-dimensional chain already has this bridge (`Z2Identification`:
`z2PathWeight` is defined from Boltzmann weights alone, and `z2PathSum_eq_iterate`
identifies path sums with iterates of the operator).  This module builds the same
bridge for the **spatial** object, where the configuration space of a single time
slice is `Fin L → Fin 2` rather than `Fin 2`.

## What is proved

* `pathSum_eq_iterate` — for any symmetric kernel on any finite type, the sum
  over space-time paths of `A(first) · B(last) · (product of bond weights)` is
  the matrix element `⟨A, K^N B⟩`.  Definition side: no operator.  Conclusion
  side: only the operator.
* `gibbsWeight_eq_dressed` — **the dressing identity.**  The honest
  two-dimensional Gibbs weight, `∏ w(slice) · ∏ K(consecutive slices)`, equals
  `√w(first) · √w(last)` times the path weight of the SYMMETRISED kernel.  The
  boundary factors are the entire price of self-adjointness.
* `gibbsPathSum_eq_symPathSum` and `gibbsPathSum_eq_iterate` — hence every
  Gibbs correlation of the spatial system is a matrix element of a self-adjoint
  transfer operator between boundary-dressed observables.
* `symVacuum_exists` — the symmetrised kernel has its own strictly positive
  Perron vacuum, so the object the bridge lands on is the object papers 7 and 8
  analysed.
* `perp_invariant`, `iterate_perp_le` and `connected_decay` — the fluctuation
  sector is invariant, and under an explicit contraction hypothesis on that
  sector the connected two-point function decays geometrically in the time
  separation.

## What is NOT proved, and is not claimed

The contraction hypothesis of §4 is carried as a **theorem hypothesis**, never
as an axiom, and it is not discharged here.  Papers 7 and 8 give a STRICT gap
with no modulus, and a strict inequality between finitely many eigenvalues does
not by itself produce the operator-norm bound the decay rate needs; converting
one into the other requires the spectral maximum over the fluctuation sector,
which this module does not construct.  So: no rate is derived from the earlier
papers here, and in particular **nothing uniform in `L`** is obtained or
suggested.

Reflection positivity is not addressed.  Nothing here concerns `SU(N)`, the
continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §0  Space-time paths over an arbitrary finite type

Everything in this section is generic: a finite set of single-slice states and
an arbitrary kernel on it.  The spatial content enters only in §1. -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- The weight of a space-time configuration: the product of the bond weights
along the time direction.  `N` bonds join `N + 1` slices. -/
noncomputable def pathWeight (K : ι → ι → ℝ) {N : ℕ} (X : Fin (N + 1) → ι) : ℝ :=
  ∏ t : Fin N, K (X t.castSucc) (X t.succ)

theorem pathWeight_pos {K : ι → ι → ℝ} (hK : ∀ i j, 0 < K i j) {N : ℕ}
    (X : Fin (N + 1) → ι) : 0 < pathWeight K X :=
  Finset.prod_pos fun _ _ => hK _ _

/-- Splitting a sum over paths at the first slice. -/
theorem sum_cons (n : ℕ) (F : (Fin (n + 2) → ι) → ℝ) :
    ∑ X : Fin (n + 2) → ι, F X
      = ∑ s : ι, ∑ Y : Fin (n + 1) → ι, F (Fin.cons s Y) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 2) => ι).sum_comp F, Fintype.sum_prod_type]
  rfl

/-- The path weight splits off its first bond. -/
theorem pathWeight_cons (K : ι → ι → ℝ) (n : ℕ) (s : ι) (Y : Fin (n + 1) → ι) :
    pathWeight K (Fin.cons s Y : Fin (n + 2) → ι) = K s (Y 0) * pathWeight K Y := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  congr 1

/-- One application of the kernel to an observable. -/
noncomputable def act (K : ι → ι → ℝ) (A : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, K i j * A j

/-- The unnormalised two-point sum over space-time paths.  **No operator occurs
in this definition**, nor in the definition of `pathWeight` it depends on. -/
noncomputable def pathSum (K : ι → ι → ℝ) (N : ℕ) (A B : ι → ℝ) : ℝ :=
  ∑ X : Fin (N + 1) → ι, A (X 0) * B (X (Fin.last N)) * pathWeight K X

theorem pathSum_zero (K : ι → ι → ℝ) (A B : ι → ℝ) :
    pathSum K 0 A B = ∑ i, A i * B i := by
  unfold pathSum
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold pathWeight
  simp

/-- **The induction step**: one bond is absorbed into the left observable.
Symmetry of the kernel is what lets the bond be read in either direction. -/
theorem pathSum_succ {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (n : ℕ)
    (A B : ι → ℝ) : pathSum K (n + 1) A B = pathSum K n (act K A) B := by
  unfold pathSum
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have hact : act K A (Y 0) = ∑ s, K s (Y 0) * A s := by
    unfold act
    exact Finset.sum_congr rfl fun s _ => by rw [hK (Y 0) s]
  rw [hact, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show (Fin.last (n + 1)) = (Fin.last n).succ from rfl]
  simp only [Fin.cons_zero, Fin.cons_succ, pathWeight_cons]
  ring

/-- **THE BRIDGE, generic form.**  A sum over space-time paths weighted by
Boltzmann factors equals a matrix element of the iterated kernel.  The left side
mentions no operator; the right side mentions nothing else. -/
theorem pathSum_eq_iterate {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (N : ℕ)
    (A B : ι → ℝ) : pathSum K N A B = ∑ i, (act K)^[N] A i * B i := by
  induction N generalizing A with
  | zero => simpa using pathSum_zero K A B
  | succ n ih => rw [pathSum_succ hK, ih, Function.iterate_succ_apply]

/-- The partition function is the path sum of the constant observable. -/
noncomputable def partitionOf (K : ι → ι → ℝ) (N : ℕ) : ℝ :=
  ∑ X : Fin (N + 1) → ι, pathWeight K X

theorem partitionOf_eq_pathSum (K : ι → ι → ℝ) (N : ℕ) :
    partitionOf K N = pathSum K N (fun _ => 1) (fun _ => 1) := by
  unfold partitionOf pathSum
  exact Finset.sum_congr rfl fun X _ => by ring

theorem partitionOf_pos {K : ι → ι → ℝ} (hK : ∀ i j, 0 < K i j) [Nonempty ι]
    (N : ℕ) : 0 < partitionOf K N :=
  Finset.sum_pos (fun X _ => pathWeight_pos hK X) ⟨fun _ => Classical.arbitrary ι,
    Finset.mem_univ _⟩

end Generic

/-! ## §1  The spatial Gibbs measure

The two-dimensional system: `N + 1` time slices, each a spatial configuration
`Fin L → Fin 2`.  The weight carries a spatial factor `w` at **every** slice and
a time-bond factor between consecutive slices.  This is written from Boltzmann
weights alone. -/

/-- The Gibbs weight of a space-time configuration of the spatial system. -/
noncomputable def gibbsWeight {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) {N : ℕ}
    (X : Fin (N + 1) → (Fin L → Fin 2)) : ℝ :=
  (∏ t : Fin (N + 1), w (X t)) *
    ∏ t : Fin N, spatialKernel β (X t.castSucc) (X t.succ)

theorem gibbsWeight_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) {N : ℕ} (X : Fin (N + 1) → (Fin L → Fin 2)) :
    0 < gibbsWeight w β X := by
  unfold gibbsWeight
  exact mul_pos (Finset.prod_pos fun t _ => hw _)
    (Finset.prod_pos fun t _ => spatialKernel_pos β _ _)

/-- The partition function of the spatial system. -/
noncomputable def gibbsPartition {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (N : ℕ) : ℝ :=
  ∑ X : Fin (N + 1) → (Fin L → Fin 2), gibbsWeight w β X

theorem gibbsPartition_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (N : ℕ) : 0 < gibbsPartition w β N :=
  Finset.sum_pos (fun X _ => gibbsWeight_pos hw β X)
    ⟨fun _ _ => 0, Finset.mem_univ _⟩

/-- The unnormalised two-point function of the spatial system. -/
noncomputable def gibbsPathSum {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (N : ℕ)
    (A B : (Fin L → Fin 2) → ℝ) : ℝ :=
  ∑ X : Fin (N + 1) → (Fin L → Fin 2),
    A (X 0) * B (X (Fin.last N)) * gibbsWeight w β X

/-- The two-point function in the measure. -/
noncomputable def gibbsCorr {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (N : ℕ)
    (A B : (Fin L → Fin 2) → ℝ) : ℝ :=
  gibbsPathSum w β N A B / gibbsPartition w β N

/-! ## §2  The dressing identity — where the measure meets the operator -/

/-- Boundary dressing of an observable by the square root of the spatial
weight. -/
noncomputable def dress {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (A : (Fin L → Fin 2) → ℝ) (σ : Fin L → Fin 2) : ℝ :=
  Real.sqrt (w σ) * A σ

/-- **THE DRESSING IDENTITY.**  The honest Gibbs weight equals the path weight
of the SYMMETRISED kernel, times a factor supported entirely on the two boundary
slices.  Self-adjointness of the transfer operator costs exactly those two
factors and nothing in the bulk. -/
theorem gibbsWeight_eq_dressed {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {N : ℕ} (X : Fin (N + 1) → (Fin L → Fin 2)) :
    gibbsWeight w β X
      = Real.sqrt (w (X 0)) * Real.sqrt (w (X (Fin.last N)))
          * pathWeight (symWeighted w β) X := by
  have hsplit : pathWeight (symWeighted w β) X
      = (∏ t : Fin N, Real.sqrt (w (X t.castSucc)))
        * (∏ t : Fin N, spatialKernel β (X t.castSucc) (X t.succ))
        * (∏ t : Fin N, Real.sqrt (w (X t.succ))) := by
    unfold pathWeight symWeighted
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  -- the two truncated products are the full product with one endpoint removed
  have hcast : (∏ t : Fin N, Real.sqrt (w (X t.castSucc)))
      * Real.sqrt (w (X (Fin.last N)))
      = ∏ t : Fin (N + 1), Real.sqrt (w (X t)) :=
    (Fin.prod_univ_castSucc (fun t : Fin (N + 1) => Real.sqrt (w (X t)))).symm
  have hsucc : Real.sqrt (w (X 0)) * (∏ t : Fin N, Real.sqrt (w (X t.succ)))
      = ∏ t : Fin (N + 1), Real.sqrt (w (X t)) :=
    (Fin.prod_univ_succ (fun t : Fin (N + 1) => Real.sqrt (w (X t)))).symm
  have hsq : (∏ t : Fin (N + 1), Real.sqrt (w (X t)))
      * (∏ t : Fin (N + 1), Real.sqrt (w (X t)))
      = ∏ t : Fin (N + 1), w (X t) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => Real.mul_self_sqrt (le_of_lt (hw (X t)))
  -- combine the three in one step: rewriting them separately would let the
  -- second rewrite consume the pattern the third one needs
  have key : (∏ t : Fin (N + 1), w (X t))
      = ((∏ t : Fin N, Real.sqrt (w (X t.castSucc))) * Real.sqrt (w (X (Fin.last N))))
        * (Real.sqrt (w (X 0)) * (∏ t : Fin N, Real.sqrt (w (X t.succ)))) := by
    rw [hcast, hsucc]; exact hsq.symm
  unfold gibbsWeight
  rw [hsplit, key]
  ring

/-- **Gibbs correlations are matrix elements.**  The unnormalised two-point
function of the spatial system is the path sum of the symmetrised kernel between
boundary-dressed observables. -/
theorem gibbsPathSum_eq_symPathSum {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (N : ℕ) (A B : (Fin L → Fin 2) → ℝ) :
    gibbsPathSum w β N A B
      = pathSum (symWeighted w β) N (dress w A) (dress w B) := by
  unfold gibbsPathSum pathSum dress
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [gibbsWeight_eq_dressed hw β X]
  ring

/-- **THE BRIDGE for the spatial system.**  Every Gibbs two-point sum is a
matrix element of an iterated self-adjoint transfer operator. -/
theorem gibbsPathSum_eq_iterate {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (N : ℕ) (A B : (Fin L → Fin 2) → ℝ) :
    gibbsPathSum w β N A B
      = ∑ σ, (act (symWeighted w β))^[N] (dress w A) σ * dress w B σ := by
  rw [gibbsPathSum_eq_symPathSum hw β N A B,
    pathSum_eq_iterate (symWeighted_symm w β) N]

/-- The partition function is the same matrix element at the dressed constant
observable. -/
theorem gibbsPartition_eq_iterate {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (N : ℕ) :
    gibbsPartition w β N
      = ∑ σ, (act (symWeighted w β))^[N] (dress w (fun _ => 1)) σ
          * dress w (fun _ => 1) σ := by
  have h : gibbsPartition w β N = gibbsPathSum w β N (fun _ => 1) (fun _ => 1) := by
    unfold gibbsPartition gibbsPathSum
    exact Finset.sum_congr rfl fun X _ => by ring
  rw [h, gibbsPathSum_eq_iterate hw β N]

/-- **The normalised expectation is a RATIO of two matrix elements.**  The
bridge above identifies the unnormalised two-point SUM; the expectation in the
measure divides it by the partition function, which is the same matrix element
at the constant observable.  Stated separately because the distinction is real:
the numerator alone is not the correlation. -/
theorem gibbsCorr_eq_ratio_iterate {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (N : ℕ) (A B : (Fin L → Fin 2) → ℝ) :
    gibbsCorr w β N A B
      = (∑ σ, (act (symWeighted w β))^[N] (dress w A) σ * dress w B σ)
        / (∑ σ, (act (symWeighted w β))^[N] (dress w (fun _ => 1)) σ
              * dress w (fun _ => 1) σ) := by
  unfold gibbsCorr
  rw [gibbsPathSum_eq_iterate hw β N A B, gibbsPartition_eq_iterate hw β N]

/-- The denominator of that ratio is strictly positive, so the expectation is
well defined and the identity is not an artefact of division by zero. -/
theorem gibbsCorr_denom_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (N : ℕ) :
    0 < ∑ σ, (act (symWeighted w β))^[N] (dress w (fun _ => 1)) σ
          * dress w (fun _ => 1) σ := by
  rw [← gibbsPartition_eq_iterate hw β N]
  exact gibbsPartition_pos hw β N

/-! ## §3  The vacuum of the symmetrised kernel

The bridge lands on `symWeighted`.  This section checks that the object it lands
on is the one papers 7 and 8 analysed: a strictly positive kernel, hence with a
Perron vacuum. -/

/-- The symmetrised kernel has a strictly positive Perron vacuum, in the
Euclidean normalisation the operator side asks for. -/
theorem symVacuum_exists {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) :
    ∃ (v : (Fin L → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < v σ) ∧ 0 < lam ∧
      (∀ σ, ∑ τ, symWeighted w β σ τ * v τ = lam * v σ) ∧
      (∀ σ, ∑ τ, normalizedKernel (symWeighted w β) lam σ τ * unitVacuum v τ
          = unitVacuum v σ) ∧
      (∑ σ, unitVacuum v σ * unitVacuum v σ = 1) := by
  obtain ⟨v, lam, hv, _, hlam, hvE⟩ :=
    exists_pos_eigenvector (symWeighted w β) (symWeighted_pos hw β)
  exact ⟨v, lam, hv, hlam, hvE,
    unitVacuum_fixed hv (ne_of_gt hlam) hvE, unitVacuum_norm hv⟩

/-- Acting with the normalised kernel fixes the unit vacuum, in the `act`
notation of §0. -/
theorem act_normalized_unitVacuum {L : ℕ} {A : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ}
    {v : (Fin L → Fin 2) → ℝ} {lam : ℝ} (hv : ∀ σ, 0 < v σ) (hlam : lam ≠ 0)
    (hvE : ∀ σ, ∑ τ, A σ τ * v τ = lam * v σ) :
    act (normalizedKernel A lam) (unitVacuum v) = unitVacuum v :=
  funext fun σ => unitVacuum_fixed hv hlam hvE σ

/-! ## §4  The fluctuation sector, and decay of the connected function

The transfer operator preserves the orthogonal complement of the vacuum.  Under
an explicit contraction hypothesis on that complement --- carried as a
hypothesis, never as an axiom --- the connected two-point function decays
geometrically in the time separation. -/

section Decay

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem eucNorm_nonneg (v : ι → ℝ) : 0 ≤ eucNorm v := Real.sqrt_nonneg _

theorem eucNorm_mul_self (v : ι → ℝ) : eucNorm v * eucNorm v = ∑ i, v i * v i :=
  Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

/-- Cauchy--Schwarz in the elementary form this section uses. -/
theorem abs_sum_mul_le (u v : ι → ℝ) :
    |∑ i, u i * v i| ≤ eucNorm u * eucNorm v := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hu : (∑ i, u i ^ 2) = eucNorm u * eucNorm u := by
    rw [eucNorm_mul_self]; exact Finset.sum_congr rfl fun i _ => sq (u i)
  have hv : (∑ i, v i ^ 2) = eucNorm v * eucNorm v := by
    rw [eucNorm_mul_self]; exact Finset.sum_congr rfl fun i _ => sq (v i)
  rw [hu, hv] at hcs
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (eucNorm_nonneg u) (eucNorm_nonneg v)) ?_
  rw [sq_abs]
  calc (∑ i, u i * v i) ^ 2
      ≤ eucNorm u * eucNorm u * (eucNorm v * eucNorm v) := hcs
    _ = (eucNorm u * eucNorm v) ^ 2 := by ring

/-- Acting with a symmetric kernel is symmetric under the pairing. -/
theorem act_pairing_symm {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (u v : ι → ℝ) :
    ∑ i, act K u i * v i = ∑ i, u i * act K v i := by
  unfold act
  calc ∑ i, (∑ j, K i j * u j) * v i
      = ∑ i, ∑ j, K i j * u j * v i := by simp_rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, K i j * u j * v i := Finset.sum_comm
    _ = ∑ i, ∑ j, u i * (K i j * v j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hK j i]; ring
    _ = ∑ i, u i * ∑ j, K i j * v j := by simp_rw [Finset.mul_sum]

/-- **The fluctuation sector is invariant.**  If an observable is orthogonal to
the vacuum, so is its image. -/
theorem perp_invariant {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) {Ω : ι → ℝ}
    (hfix : act K Ω = Ω) {u : ι → ℝ} (hperp : ∑ i, Ω i * u i = 0) :
    ∑ i, Ω i * act K u i = 0 := by
  rw [← act_pairing_symm hK Ω u, hfix, hperp]

/-- Iterates stay in the fluctuation sector. -/
theorem iterate_perp {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) {Ω : ι → ℝ}
    (hfix : act K Ω = Ω) {u : ι → ℝ} (hperp : ∑ i, Ω i * u i = 0) (n : ℕ) :
    ∑ i, Ω i * (act K)^[n] u i = 0 := by
  induction n generalizing u with
  | zero => simpa using hperp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (perp_invariant hK hfix hperp)

/-- **Geometric contraction on the fluctuation sector.**  The hypothesis is
explicit and is not discharged in this module. -/
theorem iterate_norm_le {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) {Ω : ι → ℝ}
    (hfix : act K Ω = Ω) {r : ℝ} (hr : 0 ≤ r)
    (hcontr : ∀ u : ι → ℝ, (∑ i, Ω i * u i = 0) → eucNorm (act K u) ≤ r * eucNorm u)
    {u : ι → ℝ} (hperp : ∑ i, Ω i * u i = 0) (n : ℕ) :
    eucNorm ((act K)^[n] u) ≤ r ^ n * eucNorm u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc eucNorm ((act K)^[n] (act K u)) ≤ r ^ n * eucNorm (act K u) :=
            ih (perp_invariant hK hfix hperp)
        _ ≤ r ^ n * (r * eucNorm u) :=
            mul_le_mul_of_nonneg_left (hcontr u hperp) (pow_nonneg hr n)
        _ = r ^ (n + 1) * eucNorm u := by ring

/-- **Exponential clustering of the connected two-point function.**  For an
observable in the fluctuation sector, the time-separated correlation is bounded
by `r^n` times the squared norm.  With `r < 1` this is exponential decay in the
time separation `n`. -/
theorem connected_decay {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) {Ω : ι → ℝ}
    (hfix : act K Ω = Ω) {r : ℝ} (hr : 0 ≤ r)
    (hcontr : ∀ u : ι → ℝ, (∑ i, Ω i * u i = 0) → eucNorm (act K u) ≤ r * eucNorm u)
    {u : ι → ℝ} (hperp : ∑ i, Ω i * u i = 0) (n : ℕ) :
    |∑ i, u i * (act K)^[n] u i| ≤ r ^ n * (eucNorm u * eucNorm u) := by
  calc |∑ i, u i * (act K)^[n] u i| ≤ eucNorm u * eucNorm ((act K)^[n] u) :=
        abs_sum_mul_le u _
    _ ≤ eucNorm u * (r ^ n * eucNorm u) :=
        mul_le_mul_of_nonneg_left (iterate_norm_le hK hfix hr hcontr hperp n)
          (eucNorm_nonneg u)
    _ = r ^ n * (eucNorm u * eucNorm u) := by ring

end Decay

/-! ## §4b  Non-vacuity of the contraction hypothesis

A hypothesis-carrying theorem is worthless if nothing satisfies the hypothesis.
The witness below satisfies symmetry, the fixed vacuum, and the contraction
bound *with equality* at any prescribed `r`, so §4 is not a statement about an
empty class --- and, at `0 < r < 1`, not one about a class where the conclusion
is trivial. -/

section Witness

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem eucNorm_smul (c : ℝ) (u : ι → ℝ) :
    eucNorm (fun i => c * u i) = |c| * eucNorm u := by
  unfold eucNorm
  rw [show (∑ i, c * u i * (c * u i)) = c ^ 2 * ∑ i, u i * u i by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The witness kernel: the rank-one projection onto a unit vector, plus `r`
times its complement. -/
noncomputable def gapWitness (Ω : ι → ℝ) (r : ℝ) (i j : ι) : ℝ :=
  Ω i * Ω j + r * ((if i = j then 1 else 0) - Ω i * Ω j)

theorem gapWitness_symm (Ω : ι → ℝ) (r : ℝ) (i j : ι) :
    gapWitness Ω r i j = gapWitness Ω r j i := by
  unfold gapWitness
  rw [mul_comm (Ω i) (Ω j)]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- On the fluctuation sector the witness acts as multiplication by `r`. -/
theorem gapWitness_act_perp {Ω : ι → ℝ} (r : ℝ) {u : ι → ℝ}
    (hperp : ∑ i, Ω i * u i = 0) :
    act (gapWitness Ω r) u = fun i => r * u i := by
  funext i
  unfold act gapWitness
  have hexp : ∀ j, (Ω i * Ω j + r * ((if i = j then 1 else 0) - Ω i * Ω j)) * u j
      = (1 - r) * (Ω i * (Ω j * u j)) + r * ((if i = j then 1 else 0) * u j) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hperp]
  simp

/-- The witness fixes the vacuum. -/
theorem gapWitness_fix {Ω : ι → ℝ} (hΩ : ∑ i, Ω i * Ω i = 1) (r : ℝ) :
    act (gapWitness Ω r) Ω = Ω := by
  funext i
  unfold act gapWitness
  have hexp : ∀ j, (Ω i * Ω j + r * ((if i = j then 1 else 0) - Ω i * Ω j)) * Ω j
      = (1 - r) * (Ω i * (Ω j * Ω j)) + r * ((if i = j then 1 else 0) * Ω j) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hΩ]
  simp
  ring

/-- **The hypotheses of §4 are jointly satisfiable at every rate.**  For any
unit vector and any `0 ≤ r`, the witness is symmetric, fixes the vacuum, and
contracts the fluctuation sector by exactly `r`. -/
theorem gapWitness_contracts {Ω : ι → ℝ} (hΩ : ∑ i, Ω i * Ω i = 1) {r : ℝ}
    (hr : 0 ≤ r) :
    (∀ i j, gapWitness Ω r i j = gapWitness Ω r j i) ∧
      act (gapWitness Ω r) Ω = Ω ∧
      ∀ u : ι → ℝ, (∑ i, Ω i * u i = 0) →
        eucNorm (act (gapWitness Ω r) u) ≤ r * eucNorm u := by
  refine ⟨gapWitness_symm Ω r, gapWitness_fix hΩ r, fun u hperp => ?_⟩
  rw [gapWitness_act_perp r hperp, eucNorm_smul, abs_of_nonneg hr]

/-- **The fluctuation sector is not the zero space.**  With two distinct states
and a strictly positive vacuum there is a nonzero observable orthogonal to it,
so the decay statement of §4 is not quantified over an empty set. -/
theorem exists_nonzero_perp {Ω : ι → ℝ} (hΩ : ∀ i, 0 < Ω i) {i₀ i₁ : ι}
    (hne : i₀ ≠ i₁) :
    ∃ u : ι → ℝ, (∑ i, Ω i * u i = 0) ∧ u ≠ 0 := by
  refine ⟨fun i => (if i = i₀ then Ω i₁ else 0) - (if i = i₁ then Ω i₀ else 0), ?_, ?_⟩
  · have hsplit : ∀ i : ι, Ω i * ((if i = i₀ then Ω i₁ else 0) - (if i = i₁ then Ω i₀ else 0))
        = (if i = i₀ then Ω i₀ * Ω i₁ else 0) - (if i = i₁ then Ω i₁ * Ω i₀ else 0) := by
      intro i
      by_cases h0 : i = i₀
      · subst h0; rw [if_pos rfl, if_pos rfl, if_neg hne, if_neg hne]; ring
      · by_cases h1 : i = i₁
        · subst h1; rw [if_neg h0, if_neg h0, if_pos rfl, if_pos rfl]; ring
        · rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1]; ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ i₀ (fun _ => Ω i₀ * Ω i₁),
      Finset.sum_ite_eq' Finset.univ i₁ (fun _ => Ω i₁ * Ω i₀)]
    simp
    ring
  · intro hzero
    have h := congrFun hzero i₀
    simp only [if_pos rfl, if_neg (Ne.symm hne ∘ Eq.symm), Pi.zero_apply] at h
    rcases sub_eq_zero.mp h with h'
    exact absurd h' (ne_of_gt (hΩ i₁))

end Witness

/-! ## §5  The two halves joined

The Gibbs correlation of the spatial system, at time separation `N`, is a matrix
element of the self-adjoint transfer operator between dressed observables; and
that matrix element decays geometrically once the fluctuation sector contracts.
Both halves are stated for the same object. -/

/-- **The endpoint of O-2.**  For a dressed observable orthogonal to the vacuum,
the unnormalised Gibbs two-point function of the spatial system decays
geometrically in the time separation.  The measure is on the left-hand side, the
operator estimate on the right, and the dressing identity is what joins them. -/
theorem gibbs_connected_decay {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ}
    (hfix : act (symWeighted w β) Ω = Ω) {r : ℝ} (hr : 0 ≤ r)
    (hcontr : ∀ u, (∑ σ, Ω σ * u σ = 0) →
      eucNorm (act (symWeighted w β) u) ≤ r * eucNorm u)
    {A : (Fin L → Fin 2) → ℝ} (hperp : ∑ σ, Ω σ * dress w A σ = 0) (N : ℕ) :
    |gibbsPathSum w β N A A|
      ≤ r ^ N * (eucNorm (dress w A) * eucNorm (dress w A)) := by
  rw [gibbsPathSum_eq_iterate hw β N A A]
  have hcomm : ∑ σ, (act (symWeighted w β))^[N] (dress w A) σ * dress w A σ
      = ∑ σ, dress w A σ * (act (symWeighted w β))^[N] (dress w A) σ :=
    Finset.sum_congr rfl fun σ _ => mul_comm _ _
  rw [hcomm]
  exact connected_decay (symWeighted_symm w β) hfix hr hcontr hperp N

end YangMills.OS
