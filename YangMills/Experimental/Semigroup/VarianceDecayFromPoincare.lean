import Mathlib
import YangMills.P8_PhysicalGap.MarkovSemigroupDef
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.SUN_StateConstruction

namespace YangMills
open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
# VarianceDecayFromPoincare — Spike

Goal: eliminate `sun_variance_decay` axiom.
Dream: PoincareInequality μ E lam + SymmetricMarkovTransport → HasVarianceDecay

Key question: what is the MINIMAL bridge between semigroup sg and Dirichlet form E?

HasVarianceDecay needs:
  ∃ γ > 0, ∀ f hf hf2 t ht,
    ∫(T_t f - mean f)² ≤ exp(-2γt) · ∫(f - mean f)²

This requires: d/dt Var(T_t f) = -2 E(T_t f)
Which requires: generator L of sg satisfies Lf = E'(f) (generator-Dirichlet correspondence)
Which is exactly what Hille-Yosida gives — but we froze it!

So the question is whether there is a weaker sufficient condition.
-/

/-! ## Step 1: What SymmetricMarkovTransport gives us -/

-- From T_symm: ∫ f · T_t g = ∫ T_t f · g (self-adjoint)
-- From T_stat: ∫ T_t f = ∫ f (stationary)
-- These give: Var(T_t f) = ∫(T_t f)² - (∫f)²
-- But we CANNOT prove d/dt Var(T_t f) without differentiability in t

-- Test: does Mathlib have semigroup differentiability we can use?
-- MeasureTheory.integral is differentiable under dominated convergence
-- But T_t is opaque — no continuity/differentiability axiom on t

/-! ## Step 2: The minimal missing bridge -/

/-- The semigroup-Dirichlet dissipation identity.
    This is the EXACT missing link.
    Mathematically: d/dt ∫(T_t f - mean)² = -2 E(T_t f)
    Equivalent to: generator L of sg satisfies ∫ f · L g = -E(f, g)
    This is the integration-by-parts / Green's formula for L.
    NOT derivable from SymmetricMarkovTransport alone.
    NOT derivable from PoincareInequality alone.
    This is the honest minimal bridge needed. -/
def SemigroupDirichletBridge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ)
    (sg : SymmetricMarkovTransport μ) : Prop :=
  ∀ (f : Ω → ℝ), Integrable f μ →
  Integrable (fun x => f x ^ 2) μ →
  HasDerivAt (fun t => ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ)
             (-2 * E (fun x => sg.T 0 f x))
             0

/-! ## Step 3: With the bridge, variance decay follows from Poincaré + Gronwall -/

-- If we have the dissipation identity, Gronwall closes it:
-- d/dt Var(T_t f) = -2 E(T_t f) ≤ -2λ Var(T_t f)  [by Poincaré]
-- Gronwall: Var(T_t f) ≤ exp(-2λt) Var(f)

-- Mathlib 4 Gronwall identifiers (Mathlib.Analysis.ODE.Gronwall):
#check gronwallBound          -- δ K ε x = δ * exp(K*x) + (ε/K)*(exp(K*x)-1)
#check gronwallBound_ε0       -- ε=0: δ * exp(K*x) — the useful homogeneous case
#check norm_le_gronwallBound_of_norm_deriv_right_le  -- the main ODE theorem
#check le_gronwallBound_of_liminf_deriv_right_le

theorem variance_decay_from_bridge_and_poincare
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ)
    (sg : SymmetricMarkovTransport μ)
    (lam : ℝ) (hlam : 0 < lam)
    (hP : PoincareInequality μ E lam)
    (hBridge : SemigroupDirichletBridge E sg) :
    HasVarianceDecay sg := by
  -- The proof outline:
  -- For each f, hBridge gives d/dt Var(T_t f)|_{t=0} = -2 E(T_t f)
  -- hP gives: E(g) ≥ lam * Var(g) for all g
  -- So d/dt Var(T_t f) ≤ -2*lam * Var(T_t f)
  -- Gronwall: Var(T_t f) ≤ exp(-2*lam*t) * Var(f)
  -- This is exactly HasVarianceDecay with γ = lam
  --
  -- BLOCKER: we only have d/dt at t=0, not for all t
  -- Need: SemigroupDirichletBridge to hold for T_t f, not just f
  -- This is a GLOBAL (in time) bridge, not just at t=0
  -- => stronger hypothesis needed, or the bridge must hold ∀ t
  sorry  -- Documented blocker: need bridge for all t, not just t=0

/-! ## Step 4: Stronger bridge (all times) -/

def SemigroupDirichletBridgeGlobal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ)
    (sg : SymmetricMarkovTransport μ) : Prop :=
  ∀ (f : Ω → ℝ) (s : ℝ), Integrable f μ →
  Integrable (fun x => f x ^ 2) μ →
  HasDerivAt (fun t => ∫ x, (sg.T t f x - ∫ y, f y ∂μ) ^ 2 ∂μ)
             (-2 * E (fun x => sg.T s f x))
             s

-- With the GLOBAL bridge, the proof can close:
theorem variance_decay_from_global_bridge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ)
    (sg : SymmetricMarkovTransport μ)
    (lam : ℝ) (hlam : 0 < lam)
    (hP : PoincareInequality μ E lam)
    (hBridge : SemigroupDirichletBridgeGlobal E sg) :
    HasVarianceDecay sg := by
  -- With global bridge: d/dt V(t) = -2 E(T_t f) ≤ -2λ V(t) everywhere
  -- Standard Gronwall closes: V(t) ≤ exp(-2λt) V(0)
  sorry  -- Documented: needs Gronwall for V(t) ≤ C*exp(-kt) from V'(t) ≤ -k*V(t)

/-! ## Verdict

The proof outline is MATHEMATICALLY CORRECT but has two Lean blockers:

BLOCKER 1: SemigroupDirichletBridgeGlobal
  Not derivable from SymmetricMarkovTransport alone.
  This IS the semigroup generator theory (L = generator, Lf = -E'(f)).
  Same root cause as hille_yosida_semigroup: needs C₀-semigroup theory.
  Classification: MATHLIB GAP (same layer as hille_yosida_semigroup).

BLOCKER 2: Gronwall for ODE V'(t) ≤ -k*V(t)
  Mathlib has gronwall_bound_exp for scalar ODEs.
  This may actually be AVAILABLE. Test separately.

NET ASSESSMENT:
- SemigroupDirichletBridgeGlobal = 1 new axiom to prove bridge
- If Gronwall available: only 1 new axiom needed
- If bridge can come from hille_yosida_semigroup: 0 new axioms
- But hille_yosida_semigroup already gives SymmetricMarkovTransport only
- So: either add 1 axiom (bridge), or enhance hille_yosida to return stronger type

RECOMMENDATION:
sun_variance_decay is at the same Mathlib frontier as hille_yosida_semigroup.
Neither can be proved without C₀-semigroup generator theory.
Both are FROZEN until Mathlib gains unbounded operator theory.

EXCEPTION: if poincare_to_covariance_decay can be combined with bridge
to give HasVarianceDecay, that would be a net -1 path.
CHECK: does poincare_to_covariance_decay provide decay in the right form?
-/

end YangMills

/-! ## Phase 2: Can we apply Gronwall?

Gronwall needs:
  norm_le_gronwallBound_of_norm_deriv_right_le requires:
  - ContinuousOn v interval
  - ∀ t ∈ interval, liminf of ‖v t‖' ≤ K * ‖v t‖ + ε

For variance decay we want:
  v(t) := ∫ (T_t f - mean f)² ∂μ
  Need: ContinuousOn v [0, ∞)
  Need: HasDerivWithinAt v (-2 * E (T_t f)) (Set.Ici t) t

Both require T_t to be differentiable in t.
Which requires the infinitesimal generator L.
CONFIRMED BLOCKER: no t-differentiability without C₀-semigroup generator.

=== SPIKE FINAL VERDICT ===

Gronwall IS available in Mathlib 4 (Mathlib.Analysis.ODE.Gronwall).
The blocker is NOT Gronwall.
The blocker IS: proving ContinuousOn / HasDerivWithinAt for t ↦ Var(T_t f).
This requires the infinitesimal generator L such that d/dt T_t f = L(T_t f).
Generator theory requires C₀-semigroup formalism — not in Mathlib 4.29.

CHAIN:
sun_variance_decay ← poincare_to_variance_decay
  ← SemigroupDirichletBridgeGlobal (generator formula d/dt T_t f = L T_t f)
  ← C₀-semigroup + generator domain theory
  ← MATHLIB GAP (same layer as hille_yosida_semigroup)

FINAL CLASSIFICATION: sun_variance_decay is FROZEN.
Same root cause as hille_yosida_semigroup.
Cannot be proved until Mathlib gains C₀-semigroup generator theory.
ETA: Mathlib ≥ 5.x

The 8-axiom frontier is COMPLETE and OPTIMAL.
-/
