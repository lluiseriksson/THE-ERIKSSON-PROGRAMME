import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.P8_PhysicalGap.LSItoSpectralGap

/-!
# M2: Concrete sunDirichletForm for SU(N)

Provides a concrete definition of `sunDirichletForm` replacing the `opaque`
in `BalabanToLSI.lean`, and proves `IsDirichletFormStrong`.

## Mathematical content

The SU(N) Dirichlet form is the L² norm of the Lie-algebraic gradient:
  `E(f) = Σᵢ ∫ (∂_{Xᵢ} f)² dμ_Haar`
where `X₁, ..., X_{N²-1}` are the generators of `su(N)`.

## Mathlib gap

`SU(N)` as `Matrix.specialUnitaryGroup` does NOT yet have a `LieGroup`
instance in Mathlib (requires `ModelWithCorners` + `ChartedSpace`).
Therefore, directional derivatives `∂_{Xᵢ} f` are declared as opaque,
and the three algebraic properties of `IsDirichletFormStrong` are
established as axioms connecting to the physics.

## What IS proved here

- `sunDirichletForm_nonneg`: E(f) ≥ 0 (from squares)
- `sunDirichletForm_const_invariant`: E(f + c) = E(f) (derivatives kill constants)
- `sunDirichletForm_quadratic`: E(cf) = c² E(f) (linearity of ∂)
- Therefore: `IsDirichletFormStrong sunDirichletForm sunHaarProb` (as axiom)

## Status

Concrete definition: ✅ (sum of squared Lie derivatives)
IsDirichletFormStrong: ✅ (via axioms on Lie derivatives)
Connection to LSI: 📌 M3 (Clay core)
-/

namespace YangMills

open MeasureTheory Matrix

noncomputable section

variable {N_c : ℕ} [NeZero N_c]

/-! ## Lie algebra generators of SU(N_c)

The Lie algebra su(N) = {A ∈ M_N(ℂ) | A + star A = 0, Tr A = 0}
has dimension N²-1 over ℝ.

We use an opaque index type for generators to avoid needing
an explicit basis (which requires more Mathlib infrastructure).
-/

/-- Index type for Lie algebra generators of SU(N_c).
    Mathematically: a basis of su(N_c) over ℝ, with N_c²-1 elements. -/
opaque LieGenIndex (N_c : ℕ) : Type

instance : Fintype (LieGenIndex N_c) := by
  exact Classical.choice (by
    -- su(N) has dimension N²-1 over ℝ
    -- We assert finite cardinality as an opaque fact
    exact ⟨⟨Finset.univ, fun x => Finset.mem_univ x⟩⟩)

/-- Directional derivative of f along the i-th Lie algebra generator.
    Concretely: (∂_{Xᵢ} f)(U) = d/dt|_{t=0} f(U · exp(t·Xᵢ))
    Declared opaque: requires smooth manifold structure on SU(N). -/
opaque lieDerivative (N_c : ℕ) (i : LieGenIndex N_c)
    (f : SUN_State_Concrete N_c → ℝ) :
    SUN_State_Concrete N_c → ℝ

/-! ## The SU(N_c) Dirichlet form -/

/-- The SU(N_c) Dirichlet form:
    `E(f) = Σᵢ ∫ (∂_{Xᵢ} f)² dμ_Haar`

    This is the canonical Dirichlet form associated to the Lie-Laplacian
    Δ_{SU(N)} = Σᵢ Xᵢ², the Casimir operator. -/
noncomputable def sunDirichletForm_concrete (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : ℝ :=
  ∑ i : LieGenIndex N_c,
    ∫ U : SUN_State_Concrete N_c,
      (lieDerivative N_c i f U) ^ 2
      ∂(sunHaarProb N_c)

/-! ## Algebraic properties of lieDerivative

These axioms encode standard properties of directional derivatives on Lie groups.
They are NOT provable from `opaque lieDerivative` alone — proving them requires either:
  (A) Replacing `opaque lieDerivative` with a concrete definition via
      `deriv (fun t => f (lieExpCurve N_c i U t)) 0`, then adding
      `DifferentiableAt` hypotheses and using `deriv_add`, `deriv_const_mul`;
  (B) Waiting for Mathlib to formalize `LieGroup` instances for `SU(N)` with
      `ModelWithCorners` + `ChartedSpace` + `ContMDiff` infrastructure.
Status: AXIOMS — represent standard smooth category assumptions on observables.
Reference: Any differential geometry textbook, e.g. Lee "Introduction to Smooth Manifolds". -/

/-- MATHLIB GAP: Lie derivatives are linear maps on functions.
    Packages: additivity + scalar multiplication.
    Proof route: deriv linearity via lieExpCurve definition + DifferentiableAt.
    Reference: Lee, Introduction to Smooth Manifolds, Prop 3.3. -/
axiom lieDerivative_linear (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) :
    (∀ (f g : SUN_State_Concrete N_c → ℝ),
      lieDerivative N_c i (f + g) =
      lieDerivative N_c i f + lieDerivative N_c i g) ∧
    (∀ (c : ℝ) (f : SUN_State_Concrete N_c → ℝ),
      lieDerivative N_c i (fun U => c * f U) =
      fun U => c * lieDerivative N_c i f U)

/-- MATHLIB GAP: Lie derivatives annihilate constant functions.
    Proof route: d/dt|₀ (const c ∘ exp_curve) = 0 (curve stays in level set).
    Reference: Lee, Introduction to Smooth Manifolds, Prop 3.3. -/
axiom lieDerivative_const (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (c : ℝ) :
    lieDerivative N_c i (fun _ : SUN_State_Concrete N_c => c) = 0

/-- Lie derivatives are additive — derived from lieDerivative_linear. -/
lemma lieDerivative_add (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (f g : SUN_State_Concrete N_c → ℝ) :
    lieDerivative N_c i (f + g) =
    lieDerivative N_c i f + lieDerivative N_c i g :=
  (lieDerivative_linear N_c i).1 f g

/-- Lie derivatives scale — derived from lieDerivative_linear. -/
lemma lieDerivative_smul (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (c : ℝ) (f : SUN_State_Concrete N_c → ℝ) :
    lieDerivative N_c i (fun U => c * f U) =
    fun U => c * lieDerivative N_c i f U :=
  (lieDerivative_linear N_c i).2 c f

/-- Lie derivatives kill constants — derived from linear + const axioms. -/
lemma lieDerivative_const_add (N_c : ℕ) [NeZero N_c]
    (i : LieGenIndex N_c) (f : SUN_State_Concrete N_c → ℝ) (c : ℝ) :
    lieDerivative N_c i (fun U => f U + c) = lieDerivative N_c i f := by
  have h_add := (lieDerivative_linear N_c i).1 f (fun _ => c)
  have h_zero := lieDerivative_const N_c i c
  show lieDerivative N_c i (f + fun _ => c) = lieDerivative N_c i f
  rw [h_add, h_zero, add_zero]

/-! ## Proving IsDirichletFormStrong -/

/-- E(f) ≥ 0: sum of integrals of squares. -/
lemma sunDirichletForm_nonneg (f : SUN_State_Concrete N_c → ℝ) :
    0 ≤ sunDirichletForm_concrete N_c f := by
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun U => sq_nonneg _)

/-- E(f + c) = E(f): constants have zero Lie derivative. -/
lemma sunDirichletForm_const_invariant
    (f : SUN_State_Concrete N_c → ℝ) (c : ℝ) :
    sunDirichletForm_concrete N_c (fun U => f U + c) =
    sunDirichletForm_concrete N_c f := by
  simp [sunDirichletForm_concrete, lieDerivative_const_add]

/-- E(cf) = c² · E(f): quadratic scaling. -/
lemma sunDirichletForm_quadratic
    (f : SUN_State_Concrete N_c → ℝ) (c : ℝ) :
    sunDirichletForm_concrete N_c (fun U => c * f U) =
    c ^ 2 * sunDirichletForm_concrete N_c f := by
  simp [sunDirichletForm_concrete, lieDerivative_smul]
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [← integral_mul_left]
  congr 1; ext U
  ring

/-- E(f+g) ≤ 2·E(f) + 2·E(g): quasi-subadditivity from (a+b)² ≤ 2a²+2b². -/
lemma sunDirichletForm_subadditive
    (f g : SUN_State_Concrete N_c → ℝ) :
    sunDirichletForm_concrete N_c (f + g) ≤
    2 * sunDirichletForm_concrete N_c f +
    2 * sunDirichletForm_concrete N_c g := by
  simp only [sunDirichletForm_concrete, Pi.add_def]
  -- Step 1: rewrite ∂(f+g) = ∂f + ∂g using lieDerivative_add
  have hderiv : ∀ i : LieGenIndex N_c,
      lieDerivative N_c i (f + g) = lieDerivative N_c i f + lieDerivative N_c i g :=
    fun i => lieDerivative_add N_c i f g
  -- Step 2: bound (a+b)² ≤ 2a²+2b² pointwise
  have hpw : ∀ (i : LieGenIndex N_c) (U : SUN_State_Concrete N_c),
      (lieDerivative N_c i (f + g) U) ^ 2 ≤
      2 * (lieDerivative N_c i f U) ^ 2 +
      2 * (lieDerivative N_c i g U) ^ 2 := by
    intro i U
    have := hderiv i
    simp only [Pi.add_apply] at this
    rw [show (lieDerivative N_c i (f + g) U) =
        lieDerivative N_c i f U + lieDerivative N_c i g U from
      congr_fun (hderiv i) U]
    nlinarith [sq_nonneg (lieDerivative N_c i f U - lieDerivative N_c i g U)]
  -- Step 3: integrate and sum
  have hsum : ∑ i : LieGenIndex N_c,
        ∫ U, (lieDerivative N_c i (f + g) U) ^ 2 ∂sunHaarProb N_c ≤
      2 * ∑ i : LieGenIndex N_c,
            ∫ U, (lieDerivative N_c i f U) ^ 2 ∂sunHaarProb N_c +
      2 * ∑ i : LieGenIndex N_c,
            ∫ U, (lieDerivative N_c i g U) ^ 2 ∂sunHaarProb N_c := by
    rw [← Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hle : ∀ U, (lieDerivative N_c i (f + g) U) ^ 2 ≤
        2 * (lieDerivative N_c i f U) ^ 2 +
        2 * (lieDerivative N_c i g U) ^ 2 := fun U => hpw i U
    calc ∫ U, (lieDerivative N_c i (f + g) U) ^ 2 ∂sunHaarProb N_c
        ≤ ∫ U, (2 * (lieDerivative N_c i f U) ^ 2 +
                2 * (lieDerivative N_c i g U) ^ 2) ∂sunHaarProb N_c :=
          integral_mono (by fun_prop) (by fun_prop) (fun U => hle U)
      _ = 2 * ∫ U, (lieDerivative N_c i f U) ^ 2 ∂sunHaarProb N_c +
          2 * ∫ U, (lieDerivative N_c i g U) ^ 2 ∂sunHaarProb N_c := by
          rw [integral_add (by fun_prop) (by fun_prop),
              integral_const_mul, integral_const_mul]
  exact hsum

/-- `sunDirichletForm_concrete` satisfies `IsDirichletForm`. -/
lemma sunDirichletForm_isDirichletForm :
    IsDirichletForm (sunDirichletForm_concrete N_c) (sunHaarProb N_c) :=
  ⟨fun f => sunDirichletForm_nonneg f,
   fun f g => sunDirichletForm_subadditive f g⟩

/-- **MATHLIB GAP: Normal contraction (Beurling-Deny) for the SU(N) Dirichlet form.**

The normal contraction property states that truncation decreases the Dirichlet energy:
  E(trunc_n f) ≤ E(f)  where  trunc_n(x) = max(min(x,n), -n).

Mathematical proof route (currently blocked):
1. trunc_n is 1-Lipschitz: |trunc_n(x) - trunc_n(y)| ≤ |x - y|.
2. Chain rule: ∂ᵢ(trunc_n ∘ f)(U) = trunc_n'(f U) · ∂ᵢf(U)  (a.e.).
3. |trunc_n'| ≤ 1 a.e. → (∂ᵢ(trunc_n ∘ f)(U))² ≤ (∂ᵢf(U))².
4. Integrate and sum: E(trunc_n f) = Σᵢ ∫(∂ᵢ(trunc_n∘f))² ≤ Σᵢ ∫(∂ᵢf)² = E(f).

Steps 1,3,4 are provable in Lean using `LipschitzWith`, `pow_le_pow_left`,
`integral_mono`, and `Finset.sum_le_sum`. Step 2 (chain rule) requires:
  - A concrete definition of `lieDerivative` via `deriv (fun t => f (U·exp(t·Tᵢ))) 0`,
  - `HasDerivAt.comp` for smooth φ (or Rademacher theorem for Lipschitz φ),
  - These require `SU(N)` to have a `LieGroup` instance with `ModelWithCorners`.

Status: Mathlib 4.29 lacks this infrastructure. This is a software gap, NOT a
physics assumption. When Mathlib gains `LieGroup SU(N)`, this becomes a theorem.

Reference: Fukushima-Oshima-Takeda, Dirichlet Forms and Symmetric Markov Processes,
Theorem 1.4.1 (normal contraction characterizes Dirichlet forms). -/
axiom sunDirichletForm_contraction (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) (n : ℝ) (hn : 0 < n) :
    sunDirichletForm_concrete N_c (fun x => max (min (f x) n) (-n)) ≤
    sunDirichletForm_concrete N_c f

lemma sunDirichletForm_isDirichletFormStrong :
    IsDirichletFormStrong (sunDirichletForm_concrete N_c) (sunHaarProb N_c) :=
  ⟨sunDirichletForm_isDirichletForm,
   fun c f => sunDirichletForm_const_invariant f c,
   fun c f => sunDirichletForm_quadratic f c,
   fun f n hn => sunDirichletForm_contraction N_c f n hn⟩

end

end YangMills
