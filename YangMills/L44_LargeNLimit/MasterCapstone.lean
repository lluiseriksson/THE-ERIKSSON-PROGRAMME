/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson, Cowork agent (Claude)
-/
import YangMills.L44_LargeNLimit.HooftCoupling
import YangMills.L44_LargeNLimit.PlanarDominance

/-!
# `L44_LargeNLimit.MasterCapstone`: bundled large-N expansion

This module is the **capstone of the L44 block**. It bundles the
't Hooft coupling and planar-dominance into a single Lean theorem
encoding the **'t Hooft large-N organising principle**:

  *In the limit `N_c → ∞` with `λ = g² · N_c` held fixed:*
  - *the 't Hooft coupling `λ` is the natural perturbative parameter,*
  - *the reduced beta function `β_λ(λ) = -(11/3) · λ²` is `N_c`-independent,*
  - *only planar (genus-0) diagrams contribute at leading order,*
  - *non-planar diagrams are suppressed by `(1/N²)^g` for genus `g`.*

The capstone closes L44 as a clean 3-file block:

* `HooftCoupling.lean` — the 't Hooft coupling and reduced beta function.
* `PlanarDominance.lean` — genus-suppression and planar dominance.
* `MasterCapstone.lean` (this file) — bundled statement.

## Connection to L42 and L43

L44 is the **third complementary view of confinement** in the
project's pure-Yang-Mills physics-anchoring arc:

| Block | View | Order parameter / structural content |
|---|---|---|
| L42 | Continuous (area law) | String tension `σ > 0`, mass gap `m_gap` |
| L43 | Discrete (center) | `Z_N` invariance, Polyakov loop `⟨P⟩ = 0` |
| L44 | Asymptotic (large-N) | 't Hooft coupling `λ`, planar dominance |

Together, L42 + L43 + L44 give the **triple structural**
characterisation of pure Yang-Mills phenomenology: continuous
(string-like), discrete (symmetry-group), asymptotic (1/N expansion).

## Strategy

The capstone is a `structure` `LargeNLimitBundle` that packages:
- a `1 ≤ N_c` (gauge-group rank),
- a positive `g_sq` (coupling at fixed scale),
- a positive genus `g` for which planar dominance applies (or `g = 0`).

The master theorem `L44_master_capstone` produces:
- `λ = g² · N_c > 0` (positivity of the 't Hooft coupling),
- `β_λ(λ) ≤ 0` (asymptotic freedom in `λ`),
- planar-dominance bound `genusSuppressionFactor g N_c ≤ 1/4` for `g ≥ 1, N_c ≥ 2`.

## Status

This file is structural physics scaffolding. **Status (2026-04-25)**:
produced in workspace, not yet built with `lake build`. Proofs reduce
to direct applications of the prior files.
-/

namespace L44_LargeNLimit

/-! ## §1. The bundled large-N structure -/

/-- **`LargeNLimitBundle`**: the unified bundle of inputs and outputs
    for the L44 block.

    Inputs (constructor fields):
    - `N_c ≥ 2` (gauge group rank with non-trivial planar/non-planar
       distinction; for `N_c = 1` the gauge group is trivial).
    - `g_sq > 0` (Yang-Mills coupling squared at a fixed scale).

    Outputs (proven via the prior files):
    - `λ = g² · N_c > 0`.
    - `β_λ(λ) ≤ 0` (asymptotic freedom in `λ`).
    - `genusSuppressionFactor g N_c ≤ 1/4` for `g ≥ 1`. -/
structure LargeNLimitBundle where
  N_c : ℕ
  N_c_ge_two : 2 ≤ N_c
  g_sq : ℝ
  g_sq_pos : 0 < g_sq

/-- **'t Hooft coupling output**. -/
noncomputable def LargeNLimitBundle.lam (bundle : LargeNLimitBundle) : ℝ :=
  hooftCoupling bundle.N_c bundle.g_sq

/-- **Reduced beta function output**. -/
noncomputable def LargeNLimitBundle.betaReduced
    (bundle : LargeNLimitBundle) : ℝ :=
  hooftBetaReduced bundle.lam

/-! ## §2. The master theorem -/

/-- **`L44_master_capstone`**: the master theorem of the L44 block.

    Given a `LargeNLimitBundle`, it produces:
    - `λ > 0` (positivity).
    - `β_λ(λ) ≤ 0` (asymptotic freedom in `λ`).
    - For any `g ≥ 1`, `genusSuppressionFactor g N_c ≤ 1/4`
      (planar dominance with uniform bound).

    All three follow from the structural inputs via the prior L44
    files. -/
theorem L44_master_capstone (bundle : LargeNLimitBundle) :
    0 < bundle.lam ∧
    bundle.betaReduced ≤ 0 ∧
    (∀ g : ℕ, 1 ≤ g → genusSuppressionFactor g bundle.N_c ≤ 1/4) := by
  refine ⟨?_, ?_, ?_⟩
  · -- λ > 0 from `hooftCoupling_pos`.
    have h_N_ge_one : 1 ≤ bundle.N_c := by linarith [bundle.N_c_ge_two]
    exact hooftCoupling_pos h_N_ge_one bundle.g_sq_pos
  · -- β_λ ≤ 0 from `hooftBetaReduced_nonpos`.
    exact hooftBetaReduced_nonpos bundle.lam
  · -- Planar dominance bound from `genusSuppression_le_quarter`.
    intro g hg
    exact genusSuppression_le_quarter bundle.N_c_ge_two hg

#print axioms L44_master_capstone

/-! ## §3. SU(2) and SU(3) instances -/

/-- **SU(2) bundle**: at `N_c = 2`. -/
def bundle_SU2 (g_sq : ℝ) (h_g : 0 < g_sq) : LargeNLimitBundle where
  N_c := 2
  N_c_ge_two := le_refl 2
  g_sq := g_sq
  g_sq_pos := h_g

/-- **SU(3) bundle (= QCD)**: at `N_c = 3`. -/
def bundle_SU3 (g_sq : ℝ) (h_g : 0 < g_sq) : LargeNLimitBundle where
  N_c := 3
  N_c_ge_two := by norm_num
  g_sq := g_sq
  g_sq_pos := h_g

/-- **SU(2) capstone instance**. -/
theorem L44_capstone_SU2 (g_sq : ℝ) (h_g : 0 < g_sq) :
    0 < (bundle_SU2 g_sq h_g).lam ∧
    (bundle_SU2 g_sq h_g).betaReduced ≤ 0 ∧
    (∀ g : ℕ, 1 ≤ g → genusSuppressionFactor g 2 ≤ 1/4) :=
  L44_master_capstone (bundle_SU2 g_sq h_g)

/-- **SU(3) capstone instance**. -/
theorem L44_capstone_SU3 (g_sq : ℝ) (h_g : 0 < g_sq) :
    0 < (bundle_SU3 g_sq h_g).lam ∧
    (bundle_SU3 g_sq h_g).betaReduced ≤ 0 ∧
    (∀ g : ℕ, 1 ≤ g → genusSuppressionFactor g 3 ≤ 1/4) :=
  L44_master_capstone (bundle_SU3 g_sq h_g)

#print axioms L44_capstone_SU3

/-! ## §4. The L42-L43-L44 triple-view conceptual bridge -/

/-- **Triple-view conceptual bridge** between L42, L43, and L44
    (proved at the structural level only):

    | Block | View | Statement |
    |---|---|---|
    | L42 | Continuous (area law) | `σ > 0`, `m_gap = c_Y · Λ_QCD` |
    | L43 | Discrete (center) | `Z_N` invariant, `⟨P⟩ = 0` |
    | L44 | Asymptotic (large-N) | `λ` running, planar dominance |

    The three together provide the **complete structural characterisation
    of pure Yang-Mills phenomenology**:
    - L42 captures the **continuous string-like behavior** (area law).
    - L43 captures the **discrete symmetry-breaking structure** (center).
    - L44 captures the **asymptotic 1/N organising principle**.

    Substantively connecting them — e.g., proving that the L42 string
    tension and L43 Polyakov loop and L44 't Hooft coupling are
    consistent for a given Wilson Gibbs measure — requires the
    actual SU(N) Yang-Mills measure, which the project does not yet
    provide.

    Encoded as a `theorem` whose body is `trivial` — conceptual
    signpost, not substantive claim. -/
theorem L42_L43_L44_triple_view_bridge : True := trivial

/-! ## §5. The L44 takeaway -/

/-- **L44 takeaway** (proved at the structural level only):

    The 't Hooft large-N organising principle is now formalised in
    Lean:
    - the 't Hooft coupling `λ = g² · N_c` is the natural perturbative
      parameter,
    - asymptotic freedom holds in `λ` (one-loop),
    - planar diagrams dominate at leading order with non-planar
      diagrams suppressed by at least 1/4.

    The substantive open work is **deriving the actual large-N
    behavior** of pure Yang-Mills observables (glueball masses,
    string tension, Wilson loops in the planar limit), not the
    structural large-N organising principle itself. -/
theorem L44_takeaway : True := trivial

end L44_LargeNLimit
