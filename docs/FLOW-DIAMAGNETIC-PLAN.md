# FLOW-DIAMAGNETIC-PLAN.md — the flow-sliced / diamagnetic UV campaign

**Status:** DRAFT v0.1 (2026-07-02). Produced in an external adversarial review
session (maintainer ↔ two AI reviewers, cross-checking each other). Nothing in
this plan is formalized yet; all Lean signatures below are **blueprints**
pending elaboration against the pinned Mathlib commit.

**Honest scope (read first).** This campaign targets the *producer* side of
`hRpoly` only. Full success buys the **lattice (M3) mass gap** through the
existing marginal assembly. It does **not** touch M4/M5 — continuum limit,
OS/Wightman reconstruction, continuum mass gap. Clay distance stays
~0% (<0.1%) regardless of outcome, and every status document must keep
saying so.

---

## 0. Verdict being implemented

The Ward substrate (`ApproxWardComplex`, `expect_decomposition_bound`,
`expect_profile_bound_of_exact_ward`, `WardPolymer`;
`docs/SUSY-HRPOLY-ACCELERATION-PLAN.md`) is a **consumer-side algebraic
bridge**: it converts an *assumed* decomposition `H_X = Q·B_X + R_X` into a
consumable activity profile. It does not produce Balaban's R-operation and
does not discharge `hRpoly`.

Core mathematical correction driving this plan: **the dangerous term is not
Q-exact.** Ward identities and Haar orthogonality kill odd /
nontrivial-representation terms. The term obstructing `κ₀ > 1` is even,
gauge-invariant, and marginal — it is `tr F²`, the term that renormalizes the
coupling. It is *extracted and absorbed into `g_{k+1}`*, never cancelled.
Gauge symmetry's real role is to reduce the counterterm basis to a single
coupling. The honest decomposition is

```
H = Loc₂(H) + Q·B + R^irr ,   Loc₂(H) = a_k(X) · tr F² ,
```

and the entire difficulty lives in proving the extraction is local, uniform
in the background, hole-compatible, and leaves `κ₀ > 1` (i.e. two-loop
accuracy, since `g_k ~ 1/(βk)` makes `Σ g_k` diverge but `Σ g_k^{κ₀}`
converge for `κ₀ > 1`).

The campaign attacks this along **two independent branches** (see §5):

- **Kernel branch** — scheme-agnostic bricks (diamagnetic domination,
  Gaussian IBP, BK/BBF tree interpolation, tree entropy). These feed *any*
  small-field RG step, flow-sliced **or** classical Balaban. Unconditional
  investment: `PostLocRemainder` does not know who produced it.
- **Measure branch** — the risky bet (flow-sliced measure transport, local
  Jacobian, background-independence / split-symmetry a.k.a. Nielsen node,
  marginal extraction). Kill-tested in a hierarchical scalar marginal model
  before any 4D YM work.

**Order of fire: PR 0 → PR 1 → nothing else until both are green with
witnesses.**

---

## 1. PR 0 — the abstract marginal producer

New file, no gauge, no polymers, no flow: e.g.
`YangMills/RG/MarginalRecursion.lean`.

Purpose: the first **theorem** (not hypothesis) feeding the existing marginal
consumer, which needs summability of `Σ_k g_k^{κ₀}` for some `κ₀ > 1` — not
`κ₀ = 2` specifically. This PR has standalone value even if the whole
flow-diamagnetic route later dies.

### 1.1 Core theorem: the invariant (not the decay directly)

The headline `∀ k, 1 ≤ k → …` is **not directly inductive** (the base case
needs k = 0 information). Prove the three-part invariant first; everything
else is a corollary.

```lean
theorem marginal_recursion_invariant
    (g : ℕ → ℝ) {β C : ℝ}
    (hβ : 0 < β) (hC : 0 ≤ C)
    (hstep : ∀ k, |g (k+1) - (g k - β * g k ^ 2)| ≤ C * g k ^ 3)
    (hg0 : 0 < g 0)
    (hsmallC : C * g 0 ≤ β / 2)        -- smallness as PRODUCTS, never quotients
    (hsmallβ : 3 * β * g 0 ≤ 1) :
    ∀ k, 0 < g k ∧ g k ≤ g 0 ∧
         1 / g 0 + (β / 2) * (k : ℝ) ≤ 1 / g k
```

Corollaries:

```lean
theorem marginal_recursion_decay :
    ∀ k, 1 ≤ k → 0 < g k ∧ g k ≤ 2 / (β * (k : ℝ))

theorem marginal_recursion_sq_summable :
    Summable (fun k => g k ^ 2)

theorem marginal_recursion_rpow_summable {κ : ℝ} (hκ : 1 < κ) :
    Summable (fun k => g k ^ κ)        -- Real.rpow; needs 0 < g k, from invariant
```

### 1.2 Proof (complete; no mathematical decisions left)

*Base* `k = 0`: `0 < g 0 ≤ g 0` and `1/g 0 + 0 ≤ 1/g 0`.

*Step*: assume the invariant at `k`.

1. From `g k ≤ g 0` and `hsmallC`: `C * g k ≤ β / 2`, hence
   `|ρ_k| ≤ C * g k ^ 3 ≤ (β/2) * g k ^ 2` where
   `ρ_k := g (k+1) - (g k - β g k²)`.
2. **Upper:** `g (k+1) ≤ g k - β g k² + (β/2) g k² = g k - (β/2) g k² < g k ≤ g 0`.
3. **Lower:** `g (k+1) ≥ g k - (3β/2) g k² = g k (1 - (3β/2) g k)`.
   From `hsmallβ`: `(3β/2) g k ≤ (3β/2) g 0 ≤ 1/2`, so
   `g (k+1) ≥ g k / 2 > 0`.
4. **Inverse increment:**
   `1/g (k+1) - 1/g k = (g k - g (k+1)) / (g k · g (k+1))`.
   Numerator `≥ (β/2) g k²` (step 2); denominator `≤ g k²` (step 2 gives
   `g (k+1) ≤ g k`). Hence the increment `≥ β/2`; telescoping gives the
   third invariant clause at `k+1`.

*Decay*: for `k ≥ 1`, `1/g k ≥ (β/2) k > 0`, and `0 < g k` lets you invert:
`g k ≤ 2/(β k)`.

*Summability*: compare with `(2/β)^κ · k^{-κ}` against the p-series
(`κ > 1`). Implementation notes: `Real.rpow` monotonicity needs the
positivity threaded explicitly; do **not** compute `π²/6`, comparison
suffices.

### 1.3 Non-vacuity witnesses (mandatory, in Lean, not in prose)

Take `β = 1`, `C = 1`, `g k = 1/(k+4)`. Verified algebra (checked by hand in
the review session):

- `g (k+1) - (g k - g k²) = 1/(k+5) - 1/(k+4) + 1/(k+4)²
  = 1/((k+4)²(k+5)) ≤ 1/(k+4)³ = C · g k ³`.
- Smallness: `C·g 0 = 1/4 ≤ 1/2 = β/2`; `3β·g 0 = 3/4 ≤ 1`.
- **Conclusion-consistency check** (certifies the theorem statement itself is
  not accidentally false): `1/g 0 + (β/2)k = 4 + k/2 ≤ k + 4 = 1/g k`. ✓
- Sanity corollary on the witness: `Tendsto g atTop (𝓝 0)`.

### 1.4 PR 0 traps ledger

- Smallness hypotheses as products (`C * g 0 ≤ β / 2`), never
  `min (β/(2C), …)`: Lean's `x / 0 = 0` silently empties the window at
  `C = 0`.
- `hstep` via `|·| ≤`, not `∃ ρ, …` — saves a destructuring per induction
  step.
- Provide both `^ 2` (`Monoid.npow`) and `rpow` corollaries; the consumer
  picks.

### 1.5 Honest label

This discharges the **analysis side** of the marginal flow. That the actual
YM RG step satisfies this recursion with these constants, *nonperturbatively*,
is CMP 109-adjacent content and remains part of the monster (measure branch +
fusion, §5).

---

## 2. PR 1 — compressed diamagnetic domination (the kill-test)

New file: e.g. `YangMills/RG/Diamagnetic.lean`.

Purpose: background-field-uniform kernel decay in ~5 lemmas of
finite-dimensional algebra, replacing (for the *decay input only*) the
gauge-fixed random-walk expansions of the classical route
(CMP 116 (2.7)–(2.10) / `hrootPieces`). If this brick does not go in clean,
the strategy dies early and cheap — by design.

### 2.1 Acceptance criteria (all eight are gating)

1. **Single space.** `H = ℓ²(V; ℂ^{Nc})`, i.e.
   `abbrev Color := EuclideanSpace ℂ (Fin Nc)`,
   `abbrev GaugeHilbert := PiLp 2 (fun _ : V => Color)`.
   **No dependent fibers `E x`, no per-vertex types** — dependent transport
   along index equalities is the death of this PR.
2. **Holes by compression**, never `Subtype` restriction:
   `A_{Ω,U} = P_Ω ∘ A_U ∘ P_Ω` in the ambient space.
3. **Mathlib unitaries** (`unitary` submonoid / `LinearIsometryEquiv` /
   existing C*-API). No bespoke `LinkUnitary` structure. The norm-one fact is
   an imported/reexported lemma and the **first `example` in the file**:
   `‖(u : …)‖ = 1` for unitaries.
4. **Norm discipline.** ℓ²-operator norm (the C*-norm) on blocks throughout.
   **Frobenius is forbidden**: `‖U‖_F = √Nc` makes the domination *false* —
   a path of length n would pick up `Nc^{n/2}`. If a draft compiles under
   Frobenius, it compiles proving something else.
5. **Ambient-degree Dirichlet convention.**
   `Δ_{Ω,U} = A_{Ω,U} − D·I` with `D` the *ambient torus* degree (`2d`),
   including at hole boundaries. (Subgraph degree breaks the `e^{−Dτ}`
   factorization and forces Kato–Simon semigroup domination — out of budget.)
6. **Double compression in the kernel definition:**

   ```
   K_{Ω,U}(τ) = P_Ω · exp(τ (A_{Ω,U} − D·I)) · P_Ω .
   ```

   Rationale: the `n = 0` term of the exponential is the identity of *all of
   H*; without the outer compressions the ghost diagonal mode `e^{−Dτ}·δ_{xy}`
   survives **outside Ω**. With them, for `x, y ∈ Ω` the kernel is exactly
   the walk sum with all vertices in Ω (empty walk included when `x = y`) —
   the intended Dirichlet semantics. The scalar comparator `K_{Ω,0}` uses the
   **same** double-compressed convention. Equivalent convention note: the
   compressed generator `P(A_U − D·I)P` agrees on Ω-blocks (idempotence /
   commutation of `P` with `P A_U P`); we fix the ambient `−D·I` version as
   the algebraically cheaper one.
7. **Central mandatory lemma** `adjacency_pow_block_eq_sum_walks`, stated on
   the **regular ambient graph with compression** (this is the only statement
   in the package where a weak version can silently fail to feed the holes
   case).
8. **Non-vacuity witnesses** (§2.4).

### 2.2 The three lemmas (L1 carries all the content)

```lean
-- L1 (the kill-test): induction on n, splitting the last step.
theorem adjacency_pow_block_eq_sum_walks
    (Ω : Finset V) (U : GaugeConnection V Nc) (n : ℕ) (x y : V) :
    block y x ((P Ω ∘L A_U ∘L P Ω) ^ n)
      = ∑ γ ∈ WalksInside Ω x y n, parallelTransport U γ

-- L2: triangle + submultiplicativity + unitary norm one.
theorem covariant_walk_sum_norm_le_card … :
    ‖∑ γ ∈ WalksInside Ω x y n, parallelTransport U γ‖
      ≤ (Fintype.card (WalksInside Ω x y n) : ℝ)

-- L3: scalar bookkeeping (ℕ → ℝ cast).
theorem scalar_adjacency_pow_eq_card_walks … :
    (A_Ω_scalar ^ n) y x = (Fintype.card (WalksInside Ω x y n) : ℝ)
```

### 2.3 The exponential step (routine by design)

`−D·I` is central, so `exp(τ(A_{Ω,U} − D·I)) = e^{−Dτ} · exp(τ A_{Ω,U})`
(`Commute.exp_add` or current Mathlib name), then coefficientwise series
comparison with `τⁿ/n! ≥ 0` for `τ ≥ 0`:

```
‖ block y x (K_{Ω,U}(τ)) ‖ ≤ (K_{Ω,0}(τ))_{yx}      (τ ≥ 0).
```

### 2.4 Non-vacuity witnesses (mandatory)

- **Habitation.** Small torus or diamond graph:
  `example : 1 ≤ Fintype.card (WalksInside Ω x y n) := by decide` (or
  `norm_num`). Guards against a definition error making `WalksInside`
  empty and the whole theorem a vacuous `0 ≤ 0`.
- **Strictness.** Diagonal-neighbor pair on a small ℤ² torus; two length-2
  walks `x→a→y`, `x→b→y`. Connection: `U_{xa} = U_{ay} = U_{xb} = I`,
  `U_{by} = −I ∈ SU(2)` (center element, `det(−I) = 1` in even dimension;
  realizable with a *single* connection since the four links are
  independent, and `−I` central makes transport order irrelevant). Then the
  walk sum is `I + (−I) = 0`, so `LHS = 0 < 2 = RHS`. A genuinely
  non-commuting SU(2) element may be placed on an unrelated link; strictness
  must not depend on it.
- **Sanity (cheap regression).** `Ω =` full torus, `U ≡ 1`: the bound is an
  equality.

### 2.5 PR 1 out-of-scope ledger (so it does not oversell itself)

- The **curvature/potential term** of any linearized-flow kernel (the
  Kato/Duhamel factor `e^{τ‖F‖}`) is deliberately excluded; it belongs to
  the post-`Loc₂` pipeline in the small-field region. PR 1 dominates the
  *free* covariant walk generator only.
- **Order-of-operations as a type invariant.** Diamagnetic domination is a
  cancellation-killing machine. When wired into the pipeline, its API must
  accept only post-extraction objects (`PostLocRemainder`), never a raw
  `LocalActivity`. Misuse must fail at type-check, not by human discipline.

---

## 3. The ladder behind the kill-tests (do **not** start before double green)

```
2.5   activity_le_tree_product      -- the real analytic content between
                                    -- "kernel decays" and "activity decays"
2.75  GaussianIBPFunctional         -- interface, coordinate-free
2.9   BK / BBF interpolation        -- true producer for connected /
                                    -- non-polynomial activities
      tree_entropy_bound            -- entropic half (open)
```

Notes fixed in the review session:

- **2.75 interface must be coordinate-free.** The IBP field is
  `E[⟨ℓ, X⟩ · F(X)] = E[⟨Cℓ, ∇F(X)⟩]` with `C` the covariance operator — no
  basis, no index family `ℓ_j`, no `Finset Pairing` in the signature. The
  tree lemma consumes IBP directly by leaf-peeling; pairings never
  materialize as objects. The pairing *bound* is not cheaper than the Wick
  *identity* (same induction), so the interface is the IBP itself.
  Realization against Mathlib's measure-theoretic Gaussians is a separate,
  off-critical-path brick — **verify Mathlib's multivariate Gaussian support,
  do not presuppose it** (no Isserlis/Wick statement was found in a public
  search).
- **2.9 must be named now.** For exponentials of local actions and connected
  parts, pairing-type bounds do not suffice; the true producer of
  `activity_le_tree_product` is a Brydges–Kennedy / Battle–Brydges–Federbush
  interpolation formula. In finite dimension this is a concrete theorem
  about Gaussian moments, not folklore — but it is a brick of its own.
- **Entropy half.** The geometric stitching
  `d_M(Y) + 1 ≤ Σ_X (d_M(X) + 1)` exists; the connected-sum / tree entropy
  estimate is the open half.
- **Absorption ledger.** `B^{|T|}` with `|T| ≤ |X|` absorbs into the
  `e^{|X|}` local window **iff `log B ≤ 1`**; otherwise pay by shrinking `κ`
  or enlarging `H₀`. Must be explicit in the final bound.
- **Consumer interface stays the repo's Appendix-F form**
  (`H₀ ≤ c₀`, `κ ≥ 3κ₀ + 3`,
  `|H(X)| ≤ H₀ e^{−κ d_M(X, mod Ω^c)}`), feeding
  `omegaHolePolymerSystem…_of_metric_bound`. Do **not** front-face the
  `(3^d)² · 2^{3^d+1} q < 1` constant — that is one sufficient condition of
  one concrete consumer, not the interface.

---

## 4. Measure branch (the risky bet, kill-tested elsewhere first)

```
FlowMeasureTransport
  → LocalJacobianAction
  → BackgroundIndependence / NielsenIdentity   -- the named obstruction
  → MarginalExtraction
  → PostLocRemainder
```

- Exact lattice gauge covariance of the Wilson flow
  (`Φ_τ(g·U) = g·Φ_τ(U)`) removes the *gauge* Ward defect by construction.
  It does **not** by itself deliver background independence: any scheme
  whose cutoff/regulator depends on the background inherits the
  split-symmetry problem, controlled in the functional-RG literature by
  Nielsen-type identities. This node stays **explicit in the DAG**, never
  hidden inside "flow is gauge-covariant".
- Candidate bridges from observables to a decomposition of the **measure**:
  the Lüscher–Weisz (4+1)-dimensional representation, stochastic
  quantization (rigorous today in 2D/3D only), and Lüscher's trivializing
  maps ("flow = change of variables with local Jacobian + remainder" — the
  ideal Lean interface shape, currently perturbative only).
- **Kill-test (cheap, mandatory before 4D YM):** "local Jacobian to order
  `g²` with background-uniform remainder" in a **hierarchical scalar
  marginal model** (Gawędzki–Kupiainen style). Note: "hierarchical YM" is
  itself a design problem (gauge symmetry does not hierarchize naturally) —
  it is **not** on the critical path.

---

## 5. Full DAG (two parallel branches, one fusion)

```
Measure branch:                       Kernel branch (scheme-agnostic):
FlowMeasureTransport                  DiamagneticKernelBound        (PR 1)
  → LocalJacobianAction                 → GaussianIBPFunctional     (2.75)
  → BackgroundIndep./Nielsen            → BK/BBF interpolation      (2.9)
  → MarginalExtraction                  → activity_le_tree_product  (2.5)
  → PostLocRemainder                    → tree_entropy_bound

Fusion:
PostLocRemainder + tree_entropy_bound
  → activity_metric_bound
  → RenormalizedHoleActivityDecay
  → SingleScaleUVDecay
  → marginal M3 assembly   (existing, oracle-clean; consumes Σ g_k^{κ₀}, κ₀>1
                            — PR 0's corollary shape)
```

**Strategic consequence of the two-branch shape:** the kernel branch is
agnostic to the producer. If the measure branch dies at the Nielsen node,
the same bricks feed a classical Balaban small-field step —
`PostLocRemainder` does not know who produced it. Kernel-branch budget is
therefore unconditional; the risky bet stays confined to the measure branch.

---

## 6. Go / no-go (signed)

- **PR 0 accepted iff:** invariant theorem + decay + `Summable (g ^ κ)` for
  all real `κ > 1` + the explicit witness `g k = 1/(k+4)` with the
  conclusion-consistency check and `g → 0`, all in Lean.
- **PR 1 accepted iff:** criteria 1–8 of §2.1, the three lemmas of §2.2 with
  L1 on the ambient regular graph under compression, the double-compressed
  kernel of §2.1(6), and the witnesses of §2.4.
- **Not one line of flow-YM before both are green.** If either fails, the
  route died early and cheap — which was the design.

## 7. What success buys, and what it does not

Both PRs green ⇒ the flow-diamagnetic route earns budget. Full campaign
success ⇒ a producer for `hRpoly` ⇒ **unconditional M3 lattice mass gap**
through the existing assembly. It does **not** produce the continuum limit,
OS/Wightman reconstruction, or the continuum mass gap. The Clay distance
stays ~0% (<0.1%), and this document is required to keep saying so.