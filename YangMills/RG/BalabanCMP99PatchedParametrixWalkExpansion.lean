import YangMills.RG.BalabanCMP99GeneralizedRandomWalkSummability
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann

/-!
# CMP99 patched parametrix as an ordered generalized-walk series

The localized Neumann correction constructed previously is

`Ppatch * sum_n (-D)^n`,

where both `Ppatch` and `D` are finite sums of chart-local operators.  This
module expands every homogeneous degree into the literal noncommutative walk
shape of CMP99 equation (3.107): one distinguished head chart followed by an
ordered list of defect charts.

The expansion is proved in a general semiring and therefore does not commute
operator factors.  It also derives the standard `A * rho^|omega|` term bound
from bounds on the head and continuation factors, eliminating that bound as
an independent assumption for any concretely instantiated operator family.

Honest scope: the continuation label here is `Unit` and records the patched
defect as a single operator species split by chart.  Identifying the separate
source operators `R_alpha(X)`, proving the physical overlap restriction, and
deriving the spatial kernel estimate (3.108) remain downstream obligations.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

universe u v

/-- Ordered product associated with a finite tuple.  Unlike `Finset.prod`,
this definition is valid in a noncommutative monoid. -/
def cmp99OrderedTupleProduct {ι : Type u} {E : Type v} [Monoid E]
    (R : ι → E) {n : ℕ} (word : Fin n → ι) : E :=
  ((List.ofFn word).map R).prod

@[simp]
theorem cmp99OrderedTupleProduct_cons
    {ι : Type u} {E : Type v} [Monoid E]
    (R : ι → E) {n : ℕ} (i : ι) (word : Fin n → ι) :
    cmp99OrderedTupleProduct R (Fin.cons i word) =
      R i * cmp99OrderedTupleProduct R word := by
  simp [cmp99OrderedTupleProduct]

/-- Noncommutative expansion of a power of a finite sum into ordered words. -/
theorem sum_pow_eq_sum_cmp99OrderedTupleProduct
    {ι : Type u} {E : Type v} [Fintype ι] [Semiring E]
    (R : ι → E) :
    ∀ n : ℕ, (∑ i, R i) ^ n =
      ∑ word : Fin n → ι, cmp99OrderedTupleProduct R word := by
  intro n
  induction n with
  | zero => simp [cmp99OrderedTupleProduct]
  | succ n ih =>
      rw [pow_succ', ih, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Fintype.sum_prod_type']
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => ι)]
      apply Fintype.sum_congr
      intro word
      exact (cmp99OrderedTupleProduct_cons R word.1 word.2).symm

/-- The raw generalized walk associated with a head and an ordered chart
tuple.  The unique label records that this checkpoint has one continuation
species. -/
def cmp99SingleSpeciesWalk {ι : Type u} (head : ι)
    {n : ℕ} (word : Fin n → ι) : CMP99GeneralizedWalk Unit ι :=
  ⟨head, (List.ofFn word).map fun domain => ⟨(), domain⟩⟩

@[simp]
theorem cmp99SingleSpeciesWalk_length {ι : Type u} (head : ι)
    {n : ℕ} (word : Fin n → ι) :
    (cmp99SingleSpeciesWalk head word).length = n := by
  simp [cmp99SingleSpeciesWalk, CMP99GeneralizedWalk.length]

/-- The generalized-walk term is literally the head factor followed by the
ordered continuation tuple. -/
theorem cmp99SingleSpeciesWalk_term
    {ι : Type u} {E : Type v} [Monoid E]
    (R0 R : ι → E) (head : ι) {n : ℕ} (word : Fin n → ι) :
    (cmp99SingleSpeciesWalk head word).term R0 (fun _ => R) =
      R0 head * cmp99OrderedTupleProduct R word := by
  simp only [cmp99SingleSpeciesWalk, CMP99GeneralizedWalk.term,
    cmp99OrderedTupleProduct, List.map_map, List.prod_cons]
  congr 1

/-- One head sum times the `n`-th power of a continuation sum is exactly the
sum of the corresponding source-shaped generalized-walk terms. -/
theorem sum_mul_sum_pow_eq_sum_cmp99SingleSpeciesWalk_term
    {ι : Type u} {E : Type v} [Fintype ι] [Semiring E]
    (R0 R : ι → E) (n : ℕ) :
    (∑ head, R0 head) * (∑ domain, R domain) ^ n =
      ∑ head, ∑ word : Fin n → ι,
        (cmp99SingleSpeciesWalk head word).term R0 (fun _ => R) := by
  rw [sum_pow_eq_sum_cmp99OrderedTupleProduct R n, Finset.sum_mul]
  simp_rw [Finset.mul_sum, cmp99SingleSpeciesWalk_term]

private theorem cmp99ContinuationNormProduct_le
    {Label : Type u} {Domain : Type v} {E : Type*}
    [NormedRing E]
    (R : Label → Domain → E) (rho : ℝ) (hrho : 0 ≤ rho)
    (hR : ∀ label domain, ‖R label domain‖ ≤ rho) :
    ∀ tail : List (CMP99WalkStep Label Domain),
      (tail.map fun step => ‖R step.label step.domain‖).prod ≤
        rho ^ tail.length := by
  intro tail
  induction tail with
  | nil => simp
  | cons step tail ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc
        ‖R step.label step.domain‖ *
            (tail.map fun next => ‖R next.label next.domain‖).prod ≤
            rho * rho ^ tail.length :=
          mul_le_mul (hR step.label step.domain) ih
            (List.prod_nonneg fun x hx => by
              obtain ⟨next, _hnext, rfl⟩ := List.mem_map.mp hx
              exact norm_nonneg _)
            hrho
        _ = rho ^ (tail.length + 1) := by rw [pow_succ']

private theorem norm_cmp99ContinuationProduct_le
    {Label : Type u} {Domain : Type v} {E : Type*}
    [NormedRing E]
    (R : Label → Domain → E) (rho : ℝ) (hrho : 0 ≤ rho)
    (hR : ∀ label domain, ‖R label domain‖ ≤ rho)
    (tail : List (CMP99WalkStep Label Domain)) (htail : tail ≠ []) :
    ‖(tail.map fun step => R step.label step.domain).prod‖ ≤
      rho ^ tail.length := by
  exact (List.norm_prod_le' (by simpa using htail)).trans
    (by simpa only [List.map_map] using
      cmp99ContinuationNormProduct_le R rho hrho hR tail)

/-- Factorwise head and continuation bounds produce the visible CMP99 term
majorant; it need not be supplied separately. -/
theorem CMP99GeneralizedWalk.norm_term_le_of_factor_bounds
    {Label : Type u} {Domain : Type v} {E : Type*}
    [NormedRing E]
    (R0 : Domain → E) (R : Label → Domain → E)
    (A rho : ℝ) (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hR0 : ∀ domain, ‖R0 domain‖ ≤ A)
    (hR : ∀ label domain, ‖R label domain‖ ≤ rho)
    (walk : CMP99GeneralizedWalk Label Domain) :
    ‖walk.term R0 R‖ ≤ A * rho ^ walk.length := by
  cases htail : walk.tail with
  | nil =>
      simpa [CMP99GeneralizedWalk.term, CMP99GeneralizedWalk.length, htail]
        using hR0 walk.head
  | cons step tail =>
      calc
        ‖R0 walk.head *
            (walk.tail.map fun next => R next.label next.domain).prod‖ ≤
            ‖R0 walk.head‖ *
              ‖(walk.tail.map fun next => R next.label next.domain).prod‖ :=
          norm_mul_le _ _
        _ ≤ A * rho ^ walk.tail.length :=
          mul_le_mul (hR0 walk.head)
            (norm_cmp99ContinuationProduct_le R rho hrho hR walk.tail
              (by rw [htail]; exact List.cons_ne_nil step tail))
            (norm_nonneg _) hA
        _ = A * rho ^ walk.length := rfl

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The distinguished chart-head contribution `C_i P_i` to the patched
parametrix. -/
noncomputable def cmp99PhysicalPatchHead
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (i : ↥charts) :
    PhysicalEndomorphism d N Nc :=
  (cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
    (physicalBondProjection (core i))

/-- The chart-local continuation is the negative patch defect.  Its sign is
the one appearing in `sum_n (-D)^n`. -/
noncomputable def cmp99PhysicalPatchContinuation
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (i : ↥charts) :
    PhysicalEndomorphism d N Nc :=
  -((K - cmp99LocalizedPhysicalPrecision K (enlarged i) mass).comp
      ((cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
        (physicalBondProjection (core i))))

theorem sum_cmp99PhysicalPatchHead
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (∑ i : ↥charts,
        cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i) =
      cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK := by
  rw [cmp99PatchedPhysicalParametrix]
  simpa only [cmp99PhysicalPatchHead] using
    (Finset.sum_coe_sort charts fun i =>
    (cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
      (physicalBondProjection (core i)))

theorem sum_cmp99PhysicalPatchContinuation
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (∑ i : ↥charts,
        cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK i) =
      -cmp99PatchedPhysicalParametrixDefect
        charts K enlarged core hc hmass hK := by
  rw [cmp99PatchedPhysicalParametrixDefect]
  simp only [cmp99PhysicalPatchContinuation, Finset.sum_neg_distrib]
  congr 1
  simpa only using
    (Finset.sum_coe_sort charts fun i =>
    (K - cmp99LocalizedPhysicalPrecision K (enlarged i) mass).comp
      ((cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK).comp
        (physicalBondProjection (core i))))

/-- Exact degree-`n` bridge from the localized defect Neumann expansion to
the ordered generalized-walk syntax.  No commutation of chart operators is
used. -/
theorem cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_walk_sum
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (n : ℕ) :
    cmp99PatchedPhysicalParametrix charts K enlarged core hc hmass hK *
        (-cmp99PatchedPhysicalParametrixDefect
          charts K enlarged core hc hmass hK) ^ n =
      ∑ head : ↥charts, ∑ word : Fin n → ↥charts,
        (cmp99SingleSpeciesWalk head word).term
          (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK) := by
  rw [← sum_cmp99PhysicalPatchHead charts K enlarged core hc hmass hK,
    ← sum_cmp99PhysicalPatchContinuation charts K enlarged core hc hmass hK]
  exact sum_mul_sum_pow_eq_sum_cmp99SingleSpeciesWalk_term _ _ n

/-- The complete corrected patched covariance is the countable sum of its
finite ordered generalized-walk layers.  The only analytic input here is the
already exposed contraction of the patched defect. -/
theorem cmp99CorrectedPatchedPhysicalCovariance_eq_tsum_walk_layers
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD : ‖cmp99PatchedPhysicalParametrixDefect
      charts K enlarged core hc hmass hK‖ < 1) :
    cmp99CorrectedPatchedPhysicalCovariance
        charts K enlarged core hc hmass hK =
      ∑' n : ℕ, ∑ head : ↥charts, ∑ word : Fin n → ↥charts,
        (cmp99SingleSpeciesWalk head word).term
          (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            charts K enlarged core hc hmass hK) := by
  let P := cmp99PatchedPhysicalParametrix
    charts K enlarged core hc hmass hK
  have hs : Summable (fun n : ℕ =>
      (-cmp99PatchedPhysicalParametrixDefect
        charts K enlarged core hc hmass hK) ^ n) :=
    summable_cmp99PatchedDefectNeumannInverse hD
  change P * (∑' n : ℕ,
    (-cmp99PatchedPhysicalParametrixDefect
      charts K enlarged core hc hmass hK) ^ n) = _
  rw [← hs.tsum_mul_left P]
  apply tsum_congr
  intro n
  simpa [P] using
    cmp99PatchedPhysicalParametrix_mul_neg_defect_pow_eq_walk_sum
      charts K enlarged core hc hmass hK n

/-- Coordinate projections on an arbitrary finite physical volume are
nonexpansive.  This volume-generic form is used by the chart-head estimate. -/
theorem norm_physicalBondProjection_le_one_anyVolume
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) :
    ‖(physicalBondProjection S : PhysicalEndomorphism d N Nc)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hsq : ‖physicalBondProjection S x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro b _hb
    by_cases hbS : b ∈ S
    · rw [physicalBondProjection_apply_mem S hbS]
    · simp [physicalBondProjection_apply_not_mem S hbS, sq_nonneg ‖x b‖]
  nlinarith [norm_nonneg (physicalBondProjection S x), norm_nonneg x]

/-- The distinguished local-covariance head has the direct coercive inverse
bound; no chart-dependent constant occurs. -/
theorem norm_cmp99PhysicalPatchHead_le
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) (i : ↥charts) :
    ‖cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i‖ ≤
      (min c mass)⁻¹ := by
  have hmin : 0 < min c mass := lt_min hc hmass
  have hC :
      ‖cmp99LocalizedPhysicalCovariance
          K (enlarged i) hc hmass hK‖ ≤ (min c mass)⁻¹ := by
    simpa only [cmp99LocalizedPhysicalCovariance] using
      norm_covarianceOfIsCoerciveCLM_le
        (cmp99LocalizedPhysicalPrecision K (enlarged i) mass)
        hmin (isCoerciveCLM_cmp99LocalizedPhysicalPrecision K (enlarged i) hK)
  calc
    ‖cmp99PhysicalPatchHead charts K enlarged core hc hmass hK i‖ ≤
        ‖cmp99LocalizedPhysicalCovariance K (enlarged i) hc hmass hK‖ *
          ‖(physicalBondProjection (core i) : PhysicalEndomorphism d N Nc)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (min c mass)⁻¹ * 1 :=
      mul_le_mul hC (norm_physicalBondProjection_le_one_anyVolume (core i))
        (norm_nonneg _) (inv_nonneg.mpr hmin.le)
    _ = (min c mass)⁻¹ := mul_one _

/-- A chart-local continuation inherits an operator-norm bound from the
physical exponential defect kernel and a visible exponential row sum. -/
theorem norm_cmp99PhysicalPatchContinuation_le
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {R NR : ℕ} {M c mass κ σ Ssum Sdef : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ)
    (hSsum : 0 ≤ Ssum) (hSdef : 0 ≤ Sdef)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumDef : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(((((κ - σ) - σ) - σ) * (dist x z : ℝ)))) ≤ Sdef)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (i : ↥charts) :
    ‖cmp99PhysicalPatchContinuation
        charts K enlarged core hc hmass hK i‖ ≤
      cmp99SingleDefectDecayAmplitude M κ R c mass Ssum * Sdef := by
  have hExp :=
    cmp99SinglePhysicalParametrixDefect_exponentialKernelBound
      K (hsub i i.property) dist hsymm hself htri hM hc hmass hσ h3σκ
      hSsum hsum hrange hbound hK hNR htilt
  have hOp := physicalOpNorm_le_of_exponentialKernelBound
    dist hsymm hSdef hExp hsumDef
  simpa only [cmp99PhysicalPatchContinuation, norm_neg] using hOp

private def cmp99PhysicalComposeList
    {d N Nc : ℕ} [NeZero N]
    (headOp : PhysicalEndomorphism d N Nc)
    (tail : List (PhysicalEndomorphism d N Nc)) :
    PhysicalEndomorphism d N Nc :=
  tail.foldl (fun acc next => acc.comp next) headOp

private theorem physicalHead_mul_listProd_eq_composeList
    {d N Nc : ℕ} [NeZero N]
    (headOp : PhysicalEndomorphism d N Nc)
    (tail : List (PhysicalEndomorphism d N Nc)) :
    headOp * tail.prod = cmp99PhysicalComposeList headOp tail := by
  induction tail generalizing headOp with
  | nil => simp [cmp99PhysicalComposeList]
  | cons next tail ih =>
      rw [List.prod_cons, ← mul_assoc, ih]
      rfl

private theorem norm_physicalComposeList_le
    {d N Nc : ℕ} [NeZero N]
    (headOp : PhysicalEndomorphism d N Nc)
    {Chart : Type*} (continuation : Chart → PhysicalEndomorphism d N Nc)
    (A rho : ℝ) (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hhead : ‖headOp‖ ≤ A)
    (hcontinuation : ∀ i, ‖continuation i‖ ≤ rho) :
    ∀ tail : List Chart,
      ‖cmp99PhysicalComposeList headOp (tail.map continuation)‖ ≤
        A * rho ^ tail.length := by
  intro tail
  induction tail generalizing headOp A with
  | nil =>
      simp only [cmp99PhysicalComposeList, List.map_nil, List.foldl_nil,
        List.length_nil, pow_zero, mul_one]
      exact hhead
  | cons i tail ih =>
      have hnext : ‖headOp.comp (continuation i)‖ ≤ A * rho := by
        calc
          ‖headOp.comp (continuation i)‖ ≤ ‖headOp‖ * ‖continuation i‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ A * rho :=
            mul_le_mul hhead (hcontinuation i) (norm_nonneg _) hA
      change ‖cmp99PhysicalComposeList
        (headOp.comp (continuation i)) (tail.map continuation)‖ ≤
          A * rho ^ (i :: tail).length
      calc
        ‖cmp99PhysicalComposeList
            (headOp.comp (continuation i)) (tail.map continuation)‖ ≤
            (A * rho) * rho ^ tail.length :=
          ih (headOp := headOp.comp (continuation i)) (A := A * rho)
            (mul_nonneg hA hrho) hnext
        _ = A * rho ^ (i :: tail).length := by
          simp only [List.length_cons, pow_succ']
          ring

/-- The patched chart walk now satisfies its geometric-in-length norm bound
from physical coercivity, kernel decay, and row-sum data.  The former `hterm`
binder is absent. -/
theorem norm_cmp99PhysicalSingleSpeciesWalk_term_le
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    (charts : Finset ι)
    (K : PhysicalEndomorphism d N Nc)
    (enlarged core : ι → Finset (PhysicalBond d N))
    (hsub : ∀ i, i ∈ charts → core i ⊆ enlarged i)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {R NR : ℕ} {M c mass κ σ Ssum Sdef : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ)
    (hSsum : 0 ≤ Ssum) (hSdef : 0 ≤ Sdef)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumDef : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(((((κ - σ) - σ) - σ) * (dist x z : ℝ)))) ≤ Sdef)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (R : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (head : ↥charts) {n : ℕ} (word : Fin n → ↥charts) :
    ‖(cmp99SingleSpeciesWalk head word).term
        (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK)
        (fun _ => cmp99PhysicalPatchContinuation
          charts K enlarged core hc hmass hK)‖ ≤
      (min c mass)⁻¹ *
        (cmp99SingleDefectDecayAmplitude M κ R c mass Ssum * Sdef) ^ n := by
  have hmin : 0 < min c mass := lt_min hc hmass
  have hAmp : 0 ≤ cmp99SingleDefectDecayAmplitude M κ R c mass Ssum := by
    dsimp [cmp99SingleDefectDecayAmplitude]
    positivity
  rw [cmp99SingleSpeciesWalk_term, cmp99OrderedTupleProduct,
    physicalHead_mul_listProd_eq_composeList]
  simpa only [List.length_ofFn] using
    norm_physicalComposeList_le
      (cmp99PhysicalPatchHead charts K enlarged core hc hmass hK head)
      (cmp99PhysicalPatchContinuation charts K enlarged core hc hmass hK)
      (min c mass)⁻¹
      (cmp99SingleDefectDecayAmplitude M κ R c mass Ssum * Sdef)
      (inv_nonneg.mpr hmin.le) (mul_nonneg hAmp hSdef)
      (norm_cmp99PhysicalPatchHead_le charts K enlarged core hc hmass hK head)
      (fun i => norm_cmp99PhysicalPatchContinuation_le
        charts K enlarged core hsub dist hsymm hself htri hM hc hmass hσ h3σκ
        hSsum hSdef hsum hsumDef hrange hbound hK hNR htilt i)
      (List.ofFn word)

end

end YangMills.RG
