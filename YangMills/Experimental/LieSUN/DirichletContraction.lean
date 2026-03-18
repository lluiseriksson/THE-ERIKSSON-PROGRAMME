import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.Experimental.LieSUN.LieDerivReg_v4

open scoped Matrix
open MeasureTheory YangMills

/-!
# DirichletContraction — No-Go Spike

Question: can sunDirichletForm_contraction be eliminated with net < 0 axioms?

VERDICT: NO. Documented below.

## Analysis

sunDirichletForm_contraction states:
  E(clip_n f) ≤ E(f)  where clip_n x = max (min x n) (-n)

### Attempt 1: Transfer through LieDerivReg

LieDerivReg requires DifferentiableAt ℝ (fun t => f (curve U t)) 0.
clip_n has kinks at ±n: not differentiable there.
Therefore: LieDerivReg CANNOT be transferred through clip_n.
This attempt FAILS.

### Attempt 2 (Route B): Replace with Lipschitz composition axiom

The axiom below replaces sunDirichletForm_contraction.
Net: 1 axiom IN, 1 axiom OUT = 0.
This attempt gives NO improvement.

### Conclusion

sunDirichletForm_contraction is an honest Mathlib gap:
  Beurling-Deny normal contraction / Sobolev chain rule on Lie groups.
Keep it as an axiom. P8 frontier stays at 7.

PIVOT: hille_yosida_semigroup decomposition.
-/

noncomputable def clip (n : ℝ) (x : ℝ) : ℝ := max (min x n) (-n)

-- clip_zero: easy scalar fact
theorem clip_zero (n : ℝ) (hn : 0 < n) : clip n 0 = 0 := by
  unfold clip
  have h1 : min (0 : ℝ) n = 0 := min_eq_left (le_of_lt hn)
  have h2 : max (0 : ℝ) (-n) = 0 := max_eq_left (by linarith)
  simp [h1, h2]

/-- Route B: honest replacement axiom.
    1-Lipschitz scalar maps do not increase Dirichlet energy.
    This is the Beurling-Deny contraction: requires weak derivatives on Lie groups.
    NET COST: replacing sunDirichletForm_contraction with this = net 0. -/
axiom dirichlet_lipschitz_contraction (N_c : ℕ) [NeZero N_c]
    (φ : ℝ → ℝ) (hφ : ∀ x y, |φ x - φ y| ≤ |x - y|) (hφ0 : φ 0 = 0)
    (f : SUN_State_Concrete N_c → ℝ) :
    (∑ i : Fin (N_c ^ 2 - 1),
      ∫ U, (lieD' N_c i (fun x => φ (f x)) U) ^ 2 ∂(sunHaarProb N_c)) ≤
    (∑ i : Fin (N_c ^ 2 - 1),
      ∫ U, (lieD' N_c i f U) ^ 2 ∂(sunHaarProb N_c))

-- Spike complete: net 0, do not integrate.
