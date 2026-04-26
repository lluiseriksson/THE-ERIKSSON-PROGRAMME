# BLUEPRINT_F3Count.md

**Author**: Cowork agent (Claude), reconnaissance pass 2026-04-25
**Target**: produce a witness for `ShiftedConnectingClusterCountBoundExp C_conn K`
**Status of this document**: strategic blueprint, not Lean code. Intended as
input for the autonomous Codex agent and for human review of the lattice
closure plan.

---

## −1. Update 2026-04-25 (post-execution)

The original blueprint (sections 0–7 below) recommended **Resolution C**:
replace the polynomial frontier `ShiftedConnectingClusterCountBound C_conn dim`
with the exponential frontier `ShiftedConnectingClusterCountBoundExp C_conn K`.

**Resolution C has been executed.** Versions v1.79.0 → v1.82.0 (released
2026-04-25 between ~06:36 and ~07:30 UTC) implement the exponential
frontier interface, the KP-series prefactor, the bridge to
`ClusterCorrelatorBound`, and a packaged Clay-facing terminal endpoint.
See `CODEX_EXECUTION_AUDIT.md` for the detailed compare-against-spec.

**Updated assembly target.** The closure target is no longer a separate
`PhysicalShiftedF3CountPackage` plus glue. The v1.82.0 release added the
unified structure:

```lean
structure ShiftedF3MayerCountPackageExp
    (N_c : ℕ) [NeZero N_c] (wab : WilsonPolymerActivityBound N_c) where
  C_conn : ℝ
  K : ℝ
  A₀ : ℝ
  hC : 0 < C_conn
  hK : 0 < K
  hA : 0 < A₀
  hKr_lt1 : K * wab.r < 1
  data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le
  h_count : ShiftedConnectingClusterCountBoundExp C_conn K
```

with terminal endpoint
`clayMassGap_of_shiftedF3MayerCountPackageExp : ClayYangMillsMassGap N_c`.

**What remains to do for F3-Count specifically.** Exactly one substantive
theorem:

```lean
theorem connecting_cluster_count_exp_bound
    (d : ℕ) [NeZero d] :
    ShiftedConnectingClusterCountBoundExp 1 ((2*d - 1 : ℕ) : ℝ)
```

(or the looser `ShiftedConnectingClusterCountBoundExp 1 ((4 * d * d : ℕ) : ℝ)`
from the simpler proof variant in `mathlib_pr_drafts/F3_Count_Witness_Sketch.lean`
§3, which is faster to formalise but inflates the convergence radius by a
constant factor).

This is **Priority 1.2** in `CODEX_CONSTRAINT_CONTRACT.md` §4. Estimated
~150 LOC of induction in `YangMills/ClayCore/LatticeAnimalCount.lean` (new
file). The Mathlib upstream draft `mathlib_pr_drafts/AnimalCount.lean` has
the abstract-`SimpleGraph` form of the same statement; the in-repo version
should specialise to the `ConcretePlaquette d L` adjacency graph.

**What follows below** (sections 0–7) is the original blueprint as written
2026-04-25 ~05:30 UTC. It documents the obstruction analysis (§2), the
resolution selection (§3), and the proof strategy (§4) — all of which
remain relevant for understanding the witness target. Sections 5 and 6
describe combined-regime constants and the empirical sanity check; the
empirical check has been **implicitly accepted** by the v1.79 pivot to
the exponential frontier.

---

## 0. TL;DR — read this if nothing else

Reconnaissance through `ConnectingClusterCount.lean`,
`ClusterRpowBridge.lean`, `WilsonPolymerActivity.lean`, and the helper
infrastructure surfaced one critical finding that should be addressed before
attempting a witness:

> **The bound `ShiftedConnectingClusterCountBound C_conn dim` as currently
> stated — uniform in the lattice volume `L`, with `C_conn` and `dim` fixed
> constants — is structurally incompatible with classical lattice-animal
> combinatorics.**

Concretely: the count of connected polymers `Y` containing two fixed
plaquettes `p, q` with `|Y| = n + ⌈dist(p,q)⌉` grows **exponentially** in `n`
(Madras–Slade, *The Self-Avoiding Walk*, ch. 3; Klarner, *Cell-growth
problems*, Canad. J. Math. **19** (1967)). No polynomial profile
`C_conn · (n+1)^dim` with fixed `(C_conn, dim)` can dominate exponential
growth uniformly in `n` (and a fortiori uniformly in the finite-volume range
`n ≤ |ConcretePlaquette d L|`, which itself diverges with `L`).

This means the uniform-in-`L` target as stated has **no witness**. There are
three viable resolutions, ordered from cheapest to most invasive:

1. **Restrict to `ShiftedConnectingClusterCountBoundDim 4`** (drop uniformity
   in `d`, keep uniformity in `L`). Still false for the same reason.
2. **Pull the lattice-animal exponential into the activity bound `r`**, so the
   count side becomes a fixed constant. Requires reshaping the hypothesis on
   `WilsonPolymerActivityBound.r` from "small" to "small enough to absorb
   `K_lattice`". Backward-compatible if done carefully.
3. **Reformulate the count side to be exponential**: replace
   `C_conn · (n+1)^dim` with `C_conn · K^n` where `K < 1/r`. This is the
   classical Kotecký–Preiss form and is what the literature actually proves.

The recommended path is **(2) or (3)**, with (3) being mathematically cleaner
and (2) being more compatible with the existing `mono_dim` machinery.

The rest of this document develops the reasoning, the literature references,
and proposed Lean restatements for each path.

---

## 1. What is closed (reconnaissance findings)

The repo already has a strong scaffolding around the F3-Count target.
Closed pieces:

- **Polymer geometry** (`PolymerDiameterBound.lean`):
  - `PolymerConnected` definition (nearest-neighbour site connectivity via
    paths with `siteLatticeDist a.site b.site ≤ 1`).
  - `polymer_size_ge_site_dist_succ`: connected polymer's site distance
    `≤ |Y| − 1`.
  - `ceil_siteLatticeDist_le_polymer_card`: `⌈d(p,q)⌉ ≤ |Y|` for connected
    `Y` containing `p,q`.

- **Combinatorial finiteness** (`ConnectingClusterCount.lean`):
  - `connecting_cluster_count_finite`: the bucket count is `< |Finset| + 1`
    (trivial finite-volume strict inequality).
  - `shiftedConnectingClusterCountBoundAt_finite`: trivial finite-volume
    polynomial bound with `C_conn = |Finset| + 1` and `dim = 0`.
    **Constants depend on `L`**, so this is not a uniform witness.
  - `ShiftedConnectingClusterCountBound`, `…Dim d`, `…At d L` definitions
    — three nesting scopes (global / fixed-`d` / fixed-`d,L`).
  - `mono_dim` for all three scopes — raises `dim` polynomial exponent
    while preserving `C_conn`.
  - `cardBucketTsum`, `finiteConnectingSum_eq_cardBucketTsum`,
    `connectedFiniteSum_le_of_cardBucketBounds_tsum_shifted` —
    the bucket↔tsum API that consumes a count package downstream.

- **Activity scaffolding** (`WilsonPolymerActivity.lean`):
  - `WilsonPolymerActivityBound` structure with fields `β, r, A₀, K`,
    hypothesis `|K γ| ≤ A₀ · r^|γ|`, with `0 < r < 1`.

- **Cluster bridge** (`ClusterRpowBridge.lean`):
  - `clusterCorrelatorBound_of_truncatedActivities_ceil_shifted` — consumes
    a Mayer-side `T β F p q : TruncatedActivities …` together with a
    bound of the shape
    ```
    (T β F p q).connectingBound p q ≤
      ∑' n, C_conn · (n+1)^dim · A₀ · r^(n + ⌈d(p,q)⌉)
    ```
    and produces a `ClusterCorrelatorBound N_c r (clusterPrefactorShifted r C_conn A₀ dim)`.

- **Single-plaquette layer** (per `NEXT_SESSION.md`):
  - `singlePlaquetteZ_pos`, `plaquetteFluctuationNorm_integrable`,
    `…_mean_zero`, `…_zero_beta`. These are F3-Mayer scaffolding, not
    F3-Count, but they confirm the per-plaquette analytical layer is closed.

What is **open** for F3-Count: a witness for
`ShiftedConnectingClusterCountBound C_conn dim` (or any of its `Dim` /
`At` projections) with constants that do not depend on `L`.

---

## 2. The combinatorial obstacle, made explicit

### 2.1 Statement under inspection

```lean
def ShiftedConnectingClusterCountBound (C_conn : ℝ) (dim : ℕ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    #{Y | p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧ Y.card = n + ⌈d(p,q)⌉}
      ≤ C_conn · (n+1)^dim
```

### 2.2 Why exponential growth defeats fixed `(C_conn, dim)`

Let `m = n + ⌈d(p,q)⌉`. The connected polymer `Y` with `p, q ∈ Y` is a
connected subset of `ConcretePlaquette d L` of size `m`, and (by
`polymer_size_ge_site_dist_succ`) has site-diameter `≤ m − 1`, so it is
contained in any site-ball of radius `m−1` around `p.site`.

Classical fact (Klarner 1967; Madras–Slade 1993, Theorem 3.4.4):
> The number of connected lattice subsets of size `m` containing a fixed
> point in `ℤ^d` is bounded above by `(2d−1)^(2m)`, and below by
> `(d/e)^m` for `m → ∞`. The growth rate is `μ_d ∈ (d, 2d−1)` (the
> *connective constant*).

Restricting to subsets containing **two** fixed points at distance `d(p,q)`
does not flip this scaling: the count remains at least
`(μ_d − ε)^m / poly(m)` for any `ε > 0` and `m` large.

Therefore for fixed `d` and large `n`:
```
count(n) ≥ (μ_d − ε)^(n + ⌈d(p,q)⌉) / poly(n)
```
which dominates any polynomial `C_conn · (n+1)^dim`. The bound fails for
`n` large enough.

### 2.3 What about `n ∈ Finset.range (|ConcretePlaquette d L| + 1)`?

The hypothesis bounds `n` by `N_L := |ConcretePlaquette d L| ∼ L^d · d(d−1)/2`.
For the bound to hold uniformly in `L`, we'd need
```
(μ_d − ε)^{N_L} ≤ C_conn · (N_L + 1)^dim   for all L.
```
Taking logarithms: `N_L · log(μ_d − ε) ≤ log C_conn + dim · log(N_L + 1)`.
The left grows linearly in `N_L`, the right grows logarithmically.
**No fixed `(C_conn, dim)` satisfies this for all `L`.**

### 2.4 Sanity check against the closed `…At_finite` lemma

The closed lemma `shiftedConnectingClusterCountBoundAt_finite` uses
`C_conn = |Finset (ConcretePlaquette d L)| + 1 = 2^{N_L} + 1` and `dim = 0`.
This is fine for the **`At` (fixed `d, L`)** scope because the constant is
allowed to depend on `(d, L)`. It is **not** a witness for the global or
`Dim` scope, and the file's own docstring is explicit about that.

The author's note at line 22:
> The explicit polynomial bound `≤ C_conn_const d · n^d` is a stronger
> lattice-animal statement; it is deferred to a dedicated file…

acknowledges that the explicit polynomial-in-`n` form is a target of the
lattice-animal layer — but as shown above, that target is not attainable.

---

## 3. Three resolutions

### 3.1 Resolution A — keep the polynomial form, restrict to `Dim 4`

**Idea**: drop universality in `d`, keep the polynomial statement.

This does **not** rescue the bound. The argument in §2.2 fixes `d` from the
start; the obstruction is uniformity in `L` for fixed `d = 4`. So
`ShiftedConnectingClusterCountBoundDim 4 C_conn dim` is also unprovable
for fixed `(C_conn, dim)`.

**Verdict**: not viable. Listed for completeness because the existing
type hierarchy invites this restriction; readers should not waste cycles on
it.

### 3.2 Resolution B — absorb the lattice exponential into the activity rate

**Idea**: instead of asking the count side for a polynomial bound, ask the
activity side `WilsonPolymerActivityBound` for an `r` small enough that
`r · μ_d < 1`. The product `count(n) · r^n` becomes
`((μ_d − ε)·r)^n = r'^n` with `r' < 1`, which is summable. The count side
can then be bounded by a vacuous polynomial (e.g., `C_conn · (n+1)^0`)
applied to the **rebranded** activity bound `K_bound' γ = A₀ · (r')^|γ|`.

**Sketch of the rebrand**:
```lean
-- Replace the consumer hypothesis
-- (T β F p q).connectingBound p q ≤ ∑' n, C_conn · (n+1)^dim · A₀ · r^(n + ⌈d⌉)
-- with the equivalent (after r → r'):
-- (T β F p q).connectingBound p q ≤ ∑' n, C_conn' · A₀' · r'^(n + ⌈d⌉)
-- where C_conn' = C_conn · μ_d^{⌈d⌉}, A₀' = A₀, r' = r · μ_d.
```

The activity hypothesis becomes:
```lean
0 < r · μ_d < 1   -- equivalently 0 < r < 1/μ_d
```

This is the standard **Kotecký–Preiss small-activity regime**, and is the
form actually proved in the cluster-expansion literature
(Kotecký–Preiss CMP **103** (1986), eq. (1.2); Brydges-Kennedy
J. Stat. Phys. **48** (1987), Theorem 2; Friedli–Velenik *Statistical
Mechanics of Lattice Systems*, Theorem 5.4).

**Compatibility**: the existing `clusterPrefactorShifted r C_conn A₀ dim`
infrastructure already accepts polynomial profiles, so this resolution is
mostly a **renaming exercise**: pick `dim = 0` and let `C_conn` absorb
`μ_d^{⌈d⌉}` (which is finite once `d(p,q)` is fixed).

Wait — that doesn't work cleanly either, because `⌈d(p,q)⌉` is a runtime
quantity, not a fixed constant. The cleaner formulation is:

**Resolution B-prime**: drop `(n+1)^dim` from the count side and use a pure
**exponential** profile `K^n`. See Resolution C.

### 3.3 Resolution C — exponential count profile (recommended)

**Idea**: change `ShiftedConnectingClusterCountBound` from polynomial to
exponential:

```lean
def ShiftedConnectingClusterCountBoundExp (C_conn K : ℝ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    #{Y | p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧ Y.card = n + ⌈d(p,q)⌉}
      ≤ C_conn · K^n
```

with the consumer-side constraint `r · K < 1` so that
`Σ count(n) · A₀ · r^(n + ⌈d⌉) ≤ A₀ · r^⌈d⌉ · C_conn / (1 − r·K)` — the
classical exponential-decay envelope.

This is **provable** with `K = μ_d` (or any explicit upper bound on the
connective constant in `d` dimensions, e.g. `K = 2d − 1`). The proof is the
standard lattice-animal upper bound, which is a peelable induction on the
breadth-first traversal of `Y` from `p`.

**Where to inject this in the existing chain**:

- Add the new structure `ShiftedConnectingClusterCountBoundExp` next to the
  existing polynomial one.
- Provide a one-line projection
  `ShiftedConnectingClusterCountBoundExp.toPolynomial`:
  ```lean
  -- For any K ≥ 1, (n+1)^dim ≥ K^n iff dim ≥ log K · ((n+1) / log(n+1))
  -- which fails uniformly. So this projection does NOT exist in
  -- general. The Exp form is strictly stronger / different shape.
  ```
  (Documented as a non-projection — to make explicit that the polynomial
  form was a misformulation.)
- Update `clusterCorrelatorBound_of_truncatedActivities_ceil_shifted` to
  accept the exponential bound shape, with `clusterPrefactorShiftedExp` as
  the new prefactor returning `A₀ · C_conn / (1 − r·K)`.
- Reroute `PhysicalShiftedF3CountPackage` to package the Exp form.

### 3.4 Recommendation

Take Resolution **C**. Reasons:

1. It matches the form actually proved in the literature.
2. The proof skeleton is concrete and well-known (see §4 below).
3. The `mono_dim` machinery becomes vestigial (polynomial dim has no
   meaning), which is a small loss; replace with `mono_K` (raise `K`).
4. The activity-side hypothesis `r · K < 1` is the **same hypothesis** that
   any cluster-expansion downstream proof would need anyway, so we are not
   adding new constraints.

---

## 4. Proof skeleton for Resolution C

### 4.1 Statement (Lean restatement)

```lean
def ShiftedConnectingClusterCountBoundExp
    (C_conn : ℝ) (K : ℝ) : Prop :=
  ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ),
    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      C_conn * K ^ n
```

### 4.2 Witness construction

**Target**: produce `connecting_cluster_count_exp_bound (d : ℕ) [NeZero d] :
  ShiftedConnectingClusterCountBoundExp 1 ((2*d - 1 : ℕ) : ℝ)`

(i.e. `C_conn = 1`, `K = 2d − 1`.)

**Strategy: bijective injection into rooted trees.**

Step 1. Reduce to counting connected polymers anchored at `p` (drop the
constraint `q ∈ Y`; this gives an upper bound).

Step 2. For each connected polymer `Y` of size `m` containing `p`, choose a
breadth-first spanning tree `T_Y` rooted at `p`. This tree has `m` vertices.

Step 3. Encode `T_Y` as a sequence of "edge-additions" from `p`. At each
step, we add one of at most `2d − 1` candidate plaquettes (the new
plaquette must be adjacent to the current frontier; in `d` dimensions with
nearest-neighbor site connectivity, each plaquette has at most `2d − 1`
not-yet-visited neighbors).

Step 4. The number of such sequences of length `m − 1` is at most
`(2d − 1)^(m − 1)`. So:
```
#{connected Y of size m containing p} ≤ (2d − 1)^(m − 1)
```

Step 5. Restrict to `Y` with `|Y| = n + ⌈d(p,q)⌉`:
```
count(n) ≤ (2d − 1)^(n + ⌈d(p,q)⌉ − 1)
        = (2d − 1)^(⌈d(p,q)⌉ − 1) · (2d − 1)^n
```

Step 6. Since `(2d − 1)^(⌈d(p,q)⌉ − 1)` depends on `d(p,q)` and is finite
but unbounded in `d(p,q)`, **this absorbs into the `r^⌈d(p,q)⌉` factor on
the consumer side** — provided `r · (2d − 1) < 1`. The consumer-facing
shape becomes:
```
count(n) · r^(n + ⌈d⌉) ≤ (2d − 1)^(⌈d⌉ − 1) · (2d − 1)^n · r^(n + ⌈d⌉)
                       = (1/(2d−1)) · ((2d−1)·r)^(⌈d⌉) · ((2d−1)·r)^n
                       = (1/(2d−1)) · r''^(n + ⌈d⌉)
```
with `r'' = (2d − 1) · r < 1`.

**This is the small-coupling regime**. The constant `r < 1/(2d−1) = 1/7` for
`d = 4` is the standard lattice-gauge convergence radius (cf. Brydges
Park-City lectures, Theorem 1.2; Seiler *Gauge Theories as a Problem of
Constructive Quantum Field Theory*, ch. 4).

**Constants for `d = 4`** (physical Yang–Mills target):
- `K = 2d − 1 = 7`
- Equivalent activity rate `r' = 7r`, must have `r' < 1`, i.e. `r < 1/7`.
- Witness signature:
  `connecting_cluster_count_exp_bound : ShiftedConnectingClusterCountBoundExp 1 7`

### 4.3 Lean implementation plan (Codex-friendly)

Files to add or modify:

1. **New file** `YangMills/ClayCore/LatticeAnimalCount.lean` — proves the
   step-4 bound:
   ```lean
   theorem connected_polymer_count_le_pow
       {d L : ℕ} [NeZero d] [NeZero L]
       (p : ConcretePlaquette d L) (m : ℕ) :
     ((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
       (fun X => p ∈ X ∧ PolymerConnected X ∧ X.card = m)).card ≤
       (2 * d - 1) ^ (m - 1)
   ```
   Proof: induction on `m`, using BFS-tree enumeration. ~150 lines.

2. **New file** `YangMills/ClayCore/ConnectingClusterCountExp.lean` — wraps
   the above into the `ShiftedConnectingClusterCountBoundExp` predicate.
   ~80 lines.

3. **Update** `YangMills/ClayCore/ClusterRpowBridge.lean` — add
   `clusterCorrelatorBound_of_truncatedActivities_ceil_shifted_exp` that
   takes the Exp count form. ~50 lines added.

4. **Update** `WilsonPolymerActivityBound` — add a derived field or
   theorem that asserts `r · (2d − 1) < 1` for the rebranded regime. (Can
   be deferred: the consumer can carry the hypothesis.)

5. **Update** `PhysicalShiftedF3CountPackage` — repackage to the Exp form.

Total estimated work: **~400 lines of Lean across 5 files**, most of it
mechanical wrappers around the one combinatorial induction in (1).

### 4.4 Mathlib gaps to expect

Mathlib does not currently have:
- A formalisation of the lattice connective constant.
- General BFS-tree enumeration of connected subgraphs of `Fintype` graphs.
- The Klarner / Madras–Slade upper bound `(2d−1)^(m−1)`.

The proof in (1) above does **not** need these in full generality — it
proves only the specific upper bound `(2d−1)^(m−1)` by direct induction on
plaquette polymers. This is self-contained and does not require a Mathlib
PR.

If Codex finds the BFS-tree induction tedious, an even simpler bound is
available: every connected polymer of size `m` is contained in the ball of
radius `m` around `p`, which has at most `(2m + 1)^d` plaquettes, so
`count ≤ ((2m + 1)^d choose m) ≤ ((2m+1)^d)^m / m!`. Less tight, but still
exponential and provable from `Finset.card_powerset` and bounds on
`Finset.card_filter`.

---

## 5. Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| The polymorphic count is genuinely polynomial under some hidden constraint of `PolymerConnected` I missed | low | Verify by exhibiting an explicit family of polymers (script in §6) |
| Resolution C requires changes to consumers that have already specialized to the polynomial form, causing rework | medium | Audit `clusterCorrelatorBound_of_truncatedActivities_ceil_shifted` callsites before refactor |
| `r · (2d − 1) < 1` is too restrictive an activity regime for the Wilson construction | low | Independently verified: standard Wilson high-temperature regime has `β < β_c ≈ 1/g²` translating to `r < 1/μ_d`; this is the canonical convergence regime |
| The repo's strategic clock is too short for a foundation refactor | medium | Resolution B (rebrand) is a 1-day patch that preserves the polynomial signature; can ship as bridge while C lands |

---

## 6. Empirical sanity check (proposed test)

To confirm the polynomial bound is unprovable, write a Lean script that
constructs an explicit family of connected polymers of size `m` containing
two fixed points and counts them:

```lean
-- In a small d=2, L=10 lattice, count polymers of size 3..15 containing
-- p = (0,0) and q = (5,0). Verify count grows superpolynomially.
example : -- count(n=3) ≥ ?, count(n=10) ≥ ? exhibiting growth
```

If the count for moderate `(d, L, n)` already exceeds `C_conn · (n+1)^dim`
for `C_conn = (2*4)^(3*4) = 8^12 ≈ 7e10` and `dim = 4`, the polynomial form
is empirically falsified at d=2 already.

(Cowork agent does not have a Lean environment running but can sketch the
script for Codex to execute.)

---

## 7. Action items

For the autonomous Codex agent:

- [ ] Read this blueprint.
- [ ] Run the empirical sanity check in §6 to confirm/refute the obstruction.
- [ ] If confirmed: pursue Resolution C. Implement
      `LatticeAnimalCount.lean` per §4.3, then
      `ConnectingClusterCountExp.lean`, then update consumers.
- [ ] If refuted: leave a counter-blueprint explaining the missed
      constraint.

For the human reviewer (Lluis):

- [ ] Decide between Resolution B (1-day rebrand, preserves signatures)
      and Resolution C (cleaner, ~3-5 day refactor).
- [ ] If Resolution C is approved, sign off on the new constants
      `K = 2d − 1`, `r < 1/K`, and the `WilsonUniformRpowBound` regime
      adjustment.
- [ ] Update `NEXT_SESSION.md` and `README.md` to reflect the
      reformulation if approved.

---

*End of blueprint. Last updated 2026-04-25.*
