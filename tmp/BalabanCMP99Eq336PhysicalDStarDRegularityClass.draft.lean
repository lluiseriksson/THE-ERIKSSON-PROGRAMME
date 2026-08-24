import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClass
import YangMills.RG.FiniteTorusCurlDiv

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 (3.36): the ordinary physical `d_eta^* d_eta` condition

Printed p. 396 separates (3.36) from the first-difference condition (3.35).
The operator below uses the ordinary ordered curl and the negative backward
difference dictated by finite-torus summation by parts.  Both factors of
`eta^-1` remain visible.

Before promotion, the sign/orientation must additionally be sealed by a named
adjointness theorem for one- and two-cochains.  A successful elaboration of
these definitions alone is not source-identification evidence.
-/

namespace YangMills.RG

noncomputable section

variable {d N Nc : ℕ}
variable [NeZero d] [NeZero N] [NeZero Nc]

/-- Reindex an ordered double sum by the unique increasing orientation.

The diagonal contributes zero.  Every unordered pair contributes its lower-to-
upper and upper-to-lower terms exactly once.  Keeping this elementary
orientation lemma explicit prevents the independent-plaquette inner product
from acquiring a spurious factor two. -/
theorem cmp99SumOrderedPairSplit
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
          ((if mu < nu then lower mu nu else 0) +
            (if mu < nu then upper mu nu else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro mu _
      rw [← Finset.sum_add_distrib]
    _ = ∑ mu : ι, ∑ nu : ι,
          if mu < nu then lower mu nu + upper mu nu else 0 := by
      apply Finset.sum_congr rfl
      intro mu _
      apply Finset.sum_congr rfl
      intro nu _
      by_cases hmunu : mu < nu <;> simp [hmunu]

/-- Rewrite a proof-dependent finite sum over strict upper directions as the
corresponding subtype sum.  This is the precise bridge between an ordered-pair
split and the repository's independent-plaquette index. -/
theorem cmp99SumIfLt_eq_sumSubtype
    {ι M : Type*} [Fintype ι] [LinearOrder ι] [AddCommMonoid M]
    (mu : ι) (f : ∀ nu : ι, mu < nu → M) :
    (∑ nu : ι, if hmunu : mu < nu then f nu hmunu else 0) =
      ∑ nu : {nu : ι // mu < nu}, f nu.1 nu.2 := by
  classical
  rw [Finset.sum_subtype]

/-- Source-independent coordinates for a concrete physical plaquette: a site,
the lower direction, and the upper direction carrying its strict-order proof. -/
def cmp99PhysicalPlaquetteSigmaEquiv :
    ConcretePlaquette d N ≃
      Σ x : FinBox d N, Σ mu : Fin d, {nu : Fin d // mu < nu} where
  toFun := fun p => ⟨p.site, p.dir1, ⟨p.dir2, p.hlt⟩⟩
  invFun := fun q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv := by
    intro p
    rcases p with ⟨x, mu, nu, hmunu⟩
    rfl
  right_inv := by
    intro q
    rcases q with ⟨x, mu, nu, hmunu⟩
    rfl

/-- A sum over the repository's concrete physical plaquettes is literally the
iterated sum over sites and independent direction pairs. -/
theorem cmp99SumPhysicalPlaquette_eq_sigma
    {M : Type*} [AddCommMonoid M] (f : ConcretePlaquette d N → M) :
    (∑ p : ConcretePlaquette d N, f p) =
      ∑ x : FinBox d N, ∑ mu : Fin d, ∑ nu : {nu : Fin d // mu < nu},
        f ⟨x, mu, nu.1, nu.2⟩ := by
  let e := cmp99PhysicalPlaquetteSigmaEquiv (d := d) (N := N)
  calc
    _ = ∑ q : Σ x : FinBox d N, Σ mu : Fin d, {nu : Fin d // mu < nu},
          f (e.symm q) := by
      exact Fintype.sum_equiv e _ _ (fun p => by simp)
    _ = _ := by
      simp only [Fintype.sum_sigma]
      rfl

/-- Extend a physical two-cochain from the independent plaquettes `mu < nu`
to all ordered direction pairs.  This is the convention needed to write the
codifferential as one unrestricted sum without introducing a factor two. -/
def cmp99PhysicalOrderedTwoValue
    (F : PhysicalGaugeTwoCochain d N Nc)
    (mu nu : Fin d) (x : FinBox d N) : SUNLieCoord Nc :=
  if hmunu : mu < nu then
    F ⟨x, mu, nu, hmunu⟩
  else if hnumu : nu < mu then
    -F ⟨x, nu, mu, hnumu⟩
  else
    0

/-- The literal scaled ordinary exterior derivative on the independent
physical plaquettes. -/
noncomputable def cmp99PhysicalScaledD1OneCochain
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeTwoCochain d N Nc :=
  WithLp.toLp 2 fun p =>
    eta⁻¹ • torusCurl (fun x nu => A (x, nu)) p.dir1 p.dir2 p.site

/-- Antisymmetric extension of the scaled independent-plaquette derivative
recovers the ordered curl in every orientation. -/
@[simp] theorem cmp99PhysicalOrderedTwoValue_scaledD1
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc)
    (mu nu : Fin d) (x : FinBox d N) :
    cmp99PhysicalOrderedTwoValue
        (cmp99PhysicalScaledD1OneCochain eta A) mu nu x =
      eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu x := by
  by_cases hmunu : mu < nu
  · simp [cmp99PhysicalOrderedTwoValue, cmp99PhysicalScaledD1OneCochain,
      hmunu]
  · by_cases hnumu : nu < mu
    · simp [cmp99PhysicalOrderedTwoValue, cmp99PhysicalScaledD1OneCochain,
        hmunu, hnumu, torusCurl_swap]
    · have hmueqnu : mu = nu :=
        le_antisymm (not_lt.mp hnumu) (not_lt.mp hmunu)
      subst nu
      simp [cmp99PhysicalOrderedTwoValue]

/-- Explicit codifferential in the independent-plaquette convention.  Its
identification with the Hilbert adjoint of
`cmp99PhysicalScaledD1OneCochain` is the named theorem immediately below. -/
noncomputable def cmp99PhysicalDStarOneCochain
    (eta : ℝ) (F : PhysicalGaugeTwoCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc :=
  WithLp.toLp 2 fun b =>
    (-eta⁻¹) • ∑ mu : Fin d,
      torusBackwardDiff mu
        (fun y => cmp99PhysicalOrderedTwoValue F mu b.2 y)
        b.1

/-- Pairwise summation by parts for one independent plaquette orientation.
The two one-cochain components contribute with opposite signs, and together
give exactly one ordered-plaquette curl term.  This is the local algebraic
reason that the independent-plaquette convention carries no factor two. -/
theorem cmp99PhysicalDStar_pair_inner
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc)
    (F : PhysicalGaugeTwoCochain d N Nc)
    (mu nu : Fin d) (hmunu : mu < nu) :
    (∑ x : FinBox d N,
        inner ℝ (A (x, nu))
          ((-eta⁻¹) • torusBackwardDiff mu
            (fun y => F ⟨y, mu, nu, hmunu⟩) x))
      + (∑ x : FinBox d N,
          inner ℝ (A (x, mu))
            (eta⁻¹ • torusBackwardDiff nu
              (fun y => F ⟨y, mu, nu, hmunu⟩) x)) =
        ∑ x : FinBox d N,
          inner ℝ
            (eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu x)
            (F ⟨x, mu, nu, hmunu⟩) := by
  have hmu := sum_inner_torusBackwardDiff
    (fun x : FinBox d N => A (x, nu))
    (fun x : FinBox d N => F ⟨x, mu, nu, hmunu⟩) mu
  have hnu := sum_inner_torusBackwardDiff
    (fun x : FinBox d N => A (x, mu))
    (fun x : FinBox d N => F ⟨x, mu, nu, hmunu⟩) nu
  simp only [inner_smul_right, inner_smul_left, RCLike.conj_to_real,
    torusCurl, inner_sub_left]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hmu, hnu]
  ring

/-- The explicit codifferential is the Hilbert adjoint of the literal scaled
ordinary exterior derivative on independent physical plaquettes.

This theorem closes the sign/orientation gate for (3.36): the two ordered
orientations are combined once, the diagonal vanishes, and the final sum is
reindexed to the repository's concrete plaquette type. -/
theorem cmp99PhysicalDStarOneCochain_inner
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc)
    (F : PhysicalGaugeTwoCochain d N Nc) :
    inner ℝ A (cmp99PhysicalDStarOneCochain eta F) =
      inner ℝ (cmp99PhysicalScaledD1OneCochain eta A) F := by
  classical
  calc
    inner ℝ A (cmp99PhysicalDStarOneCochain eta F) =
        ∑ x : FinBox d N, ∑ nu : Fin d, ∑ mu : Fin d,
          inner ℝ (A (x, nu))
            ((-eta⁻¹) • torusBackwardDiff mu
              (fun y => cmp99PhysicalOrderedTwoValue F mu nu y) x) := by
      rw [PiLp.inner_apply, Fintype.sum_prod_type]
      simp only [cmp99PhysicalDStarOneCochain, Finset.smul_sum, inner_sum]
    _ = ∑ nu : Fin d, ∑ mu : Fin d, ∑ x : FinBox d N,
          inner ℝ (A (x, nu))
            ((-eta⁻¹) • torusBackwardDiff mu
              (fun y => cmp99PhysicalOrderedTwoValue F mu nu y) x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro nu _
      rw [Finset.sum_comm]
    _ = ∑ nu : Fin d, ∑ mu : Fin d,
          if hmunu : mu < nu then
            ∑ x : FinBox d N,
              inner ℝ (A (x, nu))
                ((-eta⁻¹) • torusBackwardDiff mu
                  (fun y => F ⟨y, mu, nu, hmunu⟩) x)
          else if hnumu : nu < mu then
            ∑ x : FinBox d N,
              inner ℝ (A (x, nu))
                (eta⁻¹ • torusBackwardDiff mu
                  (fun y => F ⟨y, nu, mu, hnumu⟩) x)
          else 0 := by
      apply Finset.sum_congr rfl
      intro nu _
      apply Finset.sum_congr rfl
      intro mu _
      by_cases hmunu : mu < nu
      · simp [cmp99PhysicalOrderedTwoValue, hmunu, hmunu.asymm]
      · by_cases hnumu : nu < mu
        · simp [cmp99PhysicalOrderedTwoValue, hmunu, hnumu,
            torusBackwardDiff, smul_sub]
        · simp [cmp99PhysicalOrderedTwoValue, hmunu, hnumu,
            torusBackwardDiff]
    _ = ∑ mu : Fin d, ∑ nu : Fin d,
          if hmunu : mu < nu then
            (∑ x : FinBox d N,
                inner ℝ (A (x, nu))
                  ((-eta⁻¹) • torusBackwardDiff mu
                    (fun y => F ⟨y, mu, nu, hmunu⟩) x)) +
              ∑ x : FinBox d N,
                inner ℝ (A (x, mu))
                  (eta⁻¹ • torusBackwardDiff nu
                    (fun y => F ⟨y, mu, nu, hmunu⟩) x)
          else 0 := by
      exact cmp99SumOrderedPairSplit
        (fun mu nu =>
          if hmunu : mu < nu then
            ∑ x : FinBox d N,
              inner ℝ (A (x, nu))
                ((-eta⁻¹) • torusBackwardDiff mu
                  (fun y => F ⟨y, mu, nu, hmunu⟩) x)
          else 0)
        (fun mu nu =>
          if hmunu : mu < nu then
            ∑ x : FinBox d N,
              inner ℝ (A (x, mu))
                (eta⁻¹ • torusBackwardDiff nu
                  (fun y => F ⟨y, mu, nu, hmunu⟩) x)
          else 0)
    _ = ∑ mu : Fin d, ∑ nu : Fin d,
          if hmunu : mu < nu then
            ∑ x : FinBox d N,
              inner ℝ
                (eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu x)
                (F ⟨x, mu, nu, hmunu⟩)
          else 0 := by
      apply Finset.sum_congr rfl
      intro mu _
      apply Finset.sum_congr rfl
      intro nu _
      by_cases hmunu : mu < nu
      · simp only [hmunu, dite_true]
        exact cmp99PhysicalDStar_pair_inner eta A F mu nu hmunu
      · simp [hmunu]
    _ = ∑ mu : Fin d, ∑ nu : {nu : Fin d // mu < nu},
          ∑ x : FinBox d N,
            inner ℝ
              (eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu.1 x)
              (F ⟨x, mu, nu.1, nu.2⟩) := by
      apply Finset.sum_congr rfl
      intro mu _
      exact cmp99SumIfLt_eq_sumSubtype mu
        (fun nu hmunu =>
          ∑ x : FinBox d N,
            inner ℝ
              (eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu x)
              (F ⟨x, mu, nu, hmunu⟩))
    _ = ∑ x : FinBox d N, ∑ mu : Fin d,
          ∑ nu : {nu : Fin d // mu < nu},
            inner ℝ
              (eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu.1 x)
              (F ⟨x, mu, nu.1, nu.2⟩) := by
      calc
        _ = ∑ mu : Fin d, ∑ x : FinBox d N,
              ∑ nu : {nu : Fin d // mu < nu},
                inner ℝ
                  (eta⁻¹ • torusCurl (fun y k => A (y, k)) mu nu.1 x)
                  (F ⟨x, mu, nu.1, nu.2⟩) := by
            apply Finset.sum_congr rfl
            intro mu _
            rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = inner ℝ (cmp99PhysicalScaledD1OneCochain eta A) F := by
      rw [PiLp.inner_apply, cmp99SumPhysicalPlaquette_eq_sigma]
      rfl

/-- Literal ordinary `d_eta^* d_eta A` candidate from (3.36).

The inner `eta^-1` forms the ordered exterior derivative.  The outer
`-eta^-1` is its codifferential under the repository's convention that the
backward difference is the negative adjoint of the forward difference. -/
noncomputable def cmp99PhysicalDStarDOneCochain
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc :=
  WithLp.toLp 2 fun b =>
    (-eta⁻¹) • ∑ mu : Fin d,
      torusBackwardDiff mu
        (fun y => eta⁻¹ •
          torusCurl (fun x nu => A (x, nu)) mu b.2 y)
        b.1

/-- The literal ordered-curl formula is the explicit codifferential applied
to the scaled independent-plaquette exterior derivative. -/
theorem cmp99PhysicalDStarDOneCochain_eq_dStar_scaledD1
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc) :
    cmp99PhysicalDStarDOneCochain eta A =
      cmp99PhysicalDStarOneCochain eta
        (cmp99PhysicalScaledD1OneCochain eta A) := by
  apply PiLp.ext
  intro b
  rcases b with ⟨x, nu⟩
  simp [cmp99PhysicalDStarDOneCochain,
    cmp99PhysicalDStarOneCochain]

@[simp] theorem cmp99PhysicalDStarDOneCochain_apply
    (eta : ℝ) (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (nu : Fin d) :
    cmp99PhysicalDStarDOneCochain eta A (x, nu) =
      (-eta⁻¹) • ∑ mu : Fin d,
        torusBackwardDiff mu
          (fun y => eta⁻¹ •
            torusCurl (fun z k => A (z, k)) mu nu y)
          x := by
  rfl

/-- Literal local clause `|d_eta^* d_eta A| < bound` from (3.36). -/
def CMP99PhysicalDStarDOneCochainBoundOn
    (cube : Finset (FinBox d N)) (eta : ℝ)
    (A : PhysicalGaugeOneCochain d N Nc) (bound : ℝ) : Prop :=
  ∀ x, x ∈ cube → ∀ nu : Fin d,
    ‖cmp99PhysicalDStarDOneCochain eta A (x, nu)‖ < bound

variable {L N' Mlarge n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Mlarge]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Literal third-power majorant in (3.36). -/
def cmp99Eq336PhysicalDStarDMajorant
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (eta alpha0 : ℝ) : ℝ :=
  (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 *
    ((cmp99Eq335PhysicalScaleSpacing C eta)⁻¹) ^ 3

/-- Per-cube data for the joint (3.35)--(3.36) regularity class.
The (3.35) datum is stored literally, so the stronger class derives the
weaker one instead of duplicating potentially inconsistent witnesses. -/
structure CMP99Eq336PhysicalCubeRegularityData
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (eta alpha0 : ℝ) where
  eq335 : CMP99Eq335PhysicalCubeRegularityData C U eta alpha0
  dStarD_bound :
    CMP99PhysicalDStarDOneCochainBoundOn C.carrier eta
      eq335.logarithmicRepresentative
      (cmp99Eq336PhysicalDStarDMajorant C eta alpha0)

/-- Source membership in the class satisfying both printed conditions
(3.35) and (3.36), for every admissible cube. -/
structure CMP99Eq336PhysicalRegularityClass
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (eta alpha0 : ℝ) : Prop where
  eta_pos : 0 < eta
  alpha0_pos : 0 < alpha0
  onCube :
    ∀ C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge
        scaleExtent S scaleExtent_pos,
      Nonempty (CMP99Eq336PhysicalCubeRegularityData C U eta alpha0)

/-- Forget (3.36) and recover literal membership in the (3.35) class. -/
noncomputable def CMP99Eq336PhysicalRegularityClass.toEq335
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 : ℝ}
    (R : CMP99Eq336PhysicalRegularityClass
      (Mlarge := Mlarge) (S := S) (scaleExtent_pos := scaleExtent_pos)
      U eta alpha0) :
    CMP99Eq335PhysicalRegularityClass
      (Mlarge := Mlarge) (S := S) (scaleExtent_pos := scaleExtent_pos)
      U eta alpha0 where
  eta_pos := R.eta_pos
  alpha0_pos := R.alpha0_pos
  onCube := fun C => Nonempty.map
    (fun D : CMP99Eq336PhysicalCubeRegularityData C U eta alpha0 => D.eq335)
    (R.onCube C)

end

end YangMills.RG
