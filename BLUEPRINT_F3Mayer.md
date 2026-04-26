# BLUEPRINT_F3Mayer.md

**Author**: Cowork agent (Claude), reconnaissance pass 2026-04-25
**Target**: produce a witness for `ConnectedCardDecayMayerData N_c r A₀ ...`
to populate the `data` field of `ShiftedF3MayerCountPackageExp` (v1.82.0).
**Companion document**: `BLUEPRINT_F3Count.md` (Resolution C, executed
2026-04-25 v1.79–v1.82)
**Status of this document**: strategic blueprint, not Lean code. Intended
as input for the autonomous Codex agent and for human review of the
analytic closure plan for L3.

---

## −1. Update 2026-04-25 (post-F3-Count execution)

When this blueprint was originally written (~06:30 UTC, 2026-04-25), the
F3-Count Resolution C was still a proposal. By v1.82.0 (~07:30 UTC) Codex
had executed Resolution C and packaged a **terminal Clay-facing assembly
object**:

```lean
structure ShiftedF3MayerCountPackageExp where
  ...
  data    : ConnectedCardDecayMayerData N_c wab.r A₀ ...   -- ← F3-Mayer fills this
  h_count : ShiftedConnectingClusterCountBoundExp C_conn K -- ← F3-Count fills this
```

with `clayMassGap_of_shiftedF3MayerCountPackageExp : ClayYangMillsMassGap N_c`
as the terminal endpoint.

This **simplifies the F3-Mayer target**. The closure deliverable is
exactly one Lean object:

```lean
def shiftedF3MayerPackage_witness
    {N_c : ℕ} [NeZero N_c] (wab : WilsonPolymerActivityBound N_c)
    (h_β_small : wab.β < Real.log 2 / N_c) :
    ShiftedF3MayerPackage N_c wab
```

(or directly the pair `(data : ConnectedCardDecayMayerData ...,
proof of K · wab.r < 1)` to feed into `ShiftedF3MayerCountPackageExp.ofSubpackages`).

The original blueprint §4 outlined four files:
1. `MayerInterpolation.lean` (~250 LOC, the BK polynomial)
2. `HaarFactorization.lean` (~150 LOC, disjoint-link factorisation)
3. `BrydgesKennedyEstimate.lean` (~250 LOC, the analytic boss)
4. `PhysicalConnectedCardDecayWitness.lean` (~100 LOC, the package)

**Files (1) (2) (3) remain accurate.** File (4) is now even smaller —
it just produces the `data` field above and the smallness proof
`K · wab.r < 1`, then leaves `ofSubpackages` to do the assembly. So
the total work shrinks from ~750 LOC to **~700 LOC**, with file (4)
reducing to ~50 LOC of glue.

**What follows below** (sections 0–8) is the original blueprint as
written. The strategy (BK random-walk cluster expansion), the constants
(`r = 4 N_c · β`, `A₀ = 1`, validity `β < log(2)/N_c`), and the
combined regime (`β < 1/(28 N_c)`) all remain accurate. Section 4.1
file numbering and LOC estimates can be lightly trimmed per the
discussion above.

This is **Priority 2.x** in `CODEX_CONSTRAINT_CONTRACT.md` §4
(specifically 2.1 → 2.2 → 2.3 → 3.1, sequential). The earliest start
date is when Priority 1 (the F3-Count witness in
`LatticeAnimalCount.lean`) lands, since the smallness proof
`K · wab.r < 1` requires a concrete value of `K` from the count side.

---

## 0. TL;DR

Reconnaissance through `MayerIdentity.lean`, `MayerExpansion.lean`,
`ZeroMeanCancellation.lean`, `ClusterRpowBridge.lean`, and
`WilsonPolymerActivity.lean` confirms that the F3-Mayer side has
**no structural infeasibility** — unlike F3-Count, the target structure
`ConnectedCardDecayMayerData` is provable in principle and the strategy
is well-understood in the literature (Brydges–Kennedy / Battle–Federbush
random-walk cluster expansion).

The closure path has three analytic steps:

1. **Define** the truncated activity `K(β, F, p, q, Y)` via the BK
   interpolation formula (random-walk on `Y`).
2. **Bound** `|K(Y)| ≤ A₀ · r^|Y|` using the zero-mean property of
   the normalised fluctuation `w̃` and the BK forest estimate.
3. **Identify** `wilsonConnectedCorr = (T β F p q).connectingSum p q` —
   this is the Mayer/Ursell identity, derivable from the algebraic
   cluster expansion already closed in `boltzmann_cluster_expansion_pointwise`.

Constants for the physical regime (`d = 4`, `N_c` arbitrary):

- `r = C(N_c) · β` for β small, with `C(N_c)` an explicit polynomial
  in `N_c` (see §3.3).
- `A₀ = 1` (after normalisation).
- For the chain `r · K_count < 1` from `BLUEPRINT_F3Count.md` to close
  with `K_count = 7` (d=4 connective constant bound), we need
  `r < 1/7`, i.e. **`β < 1/(7·C(N_c))`**.

This is the **standard Wilson high-temperature / strong-coupling regime**
and matches the convergence radius of the lattice-gauge cluster expansion
in the literature.

Estimated Lean implementation: **~600 lines across 4 new files**, plus
~100 lines of edits to existing modules. More work than F3-Count
because the analytic content is genuinely heavier (Möbius inversion and
random-walk interpolation are not currently in Mathlib).

---

## 1. What is closed

### 1.1 Algebraic layer (`MayerIdentity.lean`, 229 lines, oracle-clean)

- `plaquetteFluctuationRaw N_c β U := plaquetteWeight − 1`
- `plaquetteWeight_eq_one_add_raw`: `plaquetteWeight = 1 + w_raw`
- `plaquetteFluctuationRaw_zero_beta`: `w_raw|_{β=0} = 0`
- `wilsonClusterActivityRaw N_c β γ`: `∫ ∏_{p∈γ} w_raw(U) dHaar`
- `boltzmann_cluster_expansion_pointwise`: the algebraic identity
  `exp(−β · ∑_{p∈P} E(U)) = ∑_{S⊆P} ∏_{r∈S} w_raw(U)`
- `partition_function_cluster_expansion`: integrated form
- `yang_mills_from_mayer_expansion`: the end-to-end chain Mayer →
  Clay, **gated** on a pointwise rpow bound (the analytic input
  this blueprint addresses).

### 1.2 Single-plaquette layer (`ZeroMeanCancellation.lean`, 398 lines, oracle-clean)

The **critical** closed pieces — these are the single-plaquette inputs
the BK estimate needs:

- `singlePlaquetteZ N_c β := ∫ plaquetteWeight dHaar` and
  `singlePlaquetteZ_pos`.
- `plaquetteFluctuationRaw_integral`: `∫ w_raw = Z_p − 1` (NOT zero;
  acknowledged as why raw fluctuation cannot serve as the Mayer
  variable).
- **`plaquetteFluctuationNorm`**: `w̃ := plaquetteWeight/Z_p − 1`
  (the **normalised** fluctuation that DOES have zero mean).
- `plaquetteFluctuationNorm_integrable`: integrable.
- **`plaquetteFluctuationNorm_mean_zero`**: `∫ w̃ dHaar = 0`. **This
  is the keystone lemma** — it is the cancellation that makes Möbius
  inversion produce a useful truncation.
- `plaquetteFluctuationNorm_zero_beta`: `w̃|_{β=0} ≡ 0` (sanity).

### 1.3 Truncated-activity scaffolding (`MayerExpansion.lean`, 301 lines, oracle-clean)

- `TruncatedActivities` structure with fields `K, K_bound,
  K_bound_nonneg, K_abs_le, summable_K_bound`.
- `summable_abs_K`, `summable_K`, `connectingSum p q`,
  `connectingBound p q`, `two_point_decay_from_cluster_tsum`.

### 1.4 Activity bridge (`WilsonPolymerActivity.lean`, 236 lines, oracle-clean)

- `WilsonPolymerActivityBound N_c` structure with `β, r, A₀, K`,
  hypothesis `|K γ| ≤ A₀ · r^|γ|`.
- `smallFieldBound_of_wilsonActivity`: bridges Wilson activity to
  the Balaban small-field machinery (downstream consumer is happy).

### 1.5 Target structure (`ClusterRpowBridge.lean`)

```lean
structure ConnectedCardDecayMayerData
    (N_c : ℕ) [NeZero N_c]
    (r A₀ : ℝ) (hr_nonneg : 0 ≤ r) (hA_nonneg : 0 ≤ A₀) where
  K : ∀ {d L} [NeZero d] [NeZero L],
      ℝ → (G → ℝ) → ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ
  hK_abs_le : ∀ {d L} ..., |K β F p q Y| ≤
    if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r^|Y| else 0
  h_mayer : ∀ {d L} ..., wilsonConnectedCorr ... = (T_K).connectingSum p q
```

(where `G = SU(N_c)` and `T_K = TruncatedActivities.ofConnectedCardDecay K
p q r A₀ ...`).

What is **open**: a constructive witness for this structure with
constants `(r, A₀)` independent of `(d, L)`.

---

## 2. The Mayer/Ursell identity, made explicit

### 2.1 The starting point

From `boltzmann_cluster_expansion_pointwise` we have, pointwise in `U`:
```
exp(−β ∑_{p ∈ P} E_p(U)) = ∑_{S ⊆ P} ∏_{r ∈ S} w_raw(U)
```
Integrating against Haar and dividing by the normalisation:
```
⟨F_p · F_q⟩_β = (1/Z_P) · ∫ F_p F_q · ∑_S ∏_{r∈S} w_raw dHaar
```

Substituting `w̃ = w_raw + (1 − Z_p)/Z_p` (the renormalisation) gives an
expansion in the **normalised** fluctuation, which is the variable
amenable to KP / BK.

### 2.2 The connected-correlator extraction

The **connected** correlator is, by definition,
```
⟨F_p; F_q⟩ = ⟨F_p F_q⟩ − ⟨F_p⟩⟨F_q⟩
```
This is a difference of two polynomials in `w̃`. The Möbius inversion
on the partition lattice cancels all terms corresponding to partitions
where `p` and `q` are in different blocks, leaving the **truncated**
activity:
```
⟨F_p; F_q⟩ = ∑_{Y ⊆ P, p,q ∈ Y} K_truncated(Y)
```
where
```
K_truncated(Y) = ∑_{π ∈ Partitions(Y) connected through {p,q}}
                   (−1)^(|π|−1) (|π|−1)! ∏_{B ∈ π} ⟨F_p · F_q · ∏_{r∈B} w̃⟩
```

(the precise formula has `F_p, F_q` distributed into the blocks
containing `p, q`; the Möbius coefficient is the standard one.)

### 2.3 Connectedness in two senses

There are **two** notions of connectedness in play:

(a) **Algebraic connectedness** (Möbius / Ursell): a polymer `Y` such
    that the truncated K(Y) is non-zero. By zero-mean of w̃, this is
    automatic for `|Y| = 1`: K({r}) = ⟨w̃⟩ = 0.

(b) **Geometric connectedness** (`PolymerConnected`): a polymer such
    that for any two of its members, there is a path of plaquettes
    in `Y` whose consecutive sites are within Euclidean distance 1.

The bound in `ConnectedCardDecayMayerData.hK_abs_le` requires K(Y) = 0
for `Y` not in (a) ∩ (b) ∩ (contains p,q). This is **stronger than
needed** — algebraic connectedness alone (a) gives `|K(Y)| ≤ A₀ r^|Y|`
for all Y; the geometric restriction to (b) is enforced by the `if`
structure of the bound and is automatically satisfied by the BK
construction (see §3.4).

---

## 3. Strategy: BK random-walk construction of K

### 3.1 Brydges–Kennedy interpolation formula

**Reference**: Brydges & Kennedy, *Mayer expansions and the
Hamilton-Jacobi equation*, J. Stat. Phys. **48** (1987), 19–49.

Define the interpolated correlator
```
Φ(s_1, ..., s_{|Y|−1}) = ⟨F_p F_q · ∏_{r ∈ Y} (1 + s_r · w̃(U_r))⟩
```
parameterised by `s_r ∈ [0, 1]` for each `r ∈ Y \ {p, q}`. Then the
truncated activity is given by the BK formula:
```
K(Y) = ∫_0^1 ... ∫_0^1 (∏ ds_r) · ∂/∂s_{r_1} ∂/∂s_{r_2} ... Φ
```
with appropriate bookkeeping over **forests on Y**.

Equivalently (Battle–Federbush form):
```
K(Y) = ∑_{T tree on Y} (1/|T|) · ∫ (∏ over edges of T) ⟨...⟩
```

### 3.2 Why this avoids the |Y|! blowup

A naive Möbius inversion gives
```
|K(Y)| ≤ (number of partitions of Y) · ||w̃||_∞^|Y|
       ≤ Bell(|Y|) · ||w̃||_∞^|Y|
       ≤ |Y|! · ||w̃||_∞^|Y|
```
which is super-exponential and unsummable.

The BK construction reorganises the sum by **trees on Y** instead of
**partitions of Y**. Cayley's formula gives exactly `|Y|^(|Y|−2)`
trees, but with BK's `1/|T|` weight (and the zero-mean cancellation
of single-vertex blocks), the final estimate is:
```
|K(Y)| ≤ ||w̃||_∞^|Y|
```
**no factorial, no |Y|^|Y|**. This is the Brydges–Kennedy theorem
(BK 1987 §3, Thm 3.1).

### 3.3 Bounding ||w̃||_∞

The normalised fluctuation is
```
w̃(U) = exp(−β · Re tr(U)) / Z_p(β) − 1
```
where `Z_p(β) = ∫ exp(−β · Re tr(U)) dHaar`.

For `U ∈ SU(N_c)`: `|Re tr(U)| ≤ N_c`. So `exp(−β N_c) ≤ exp(−β · Re tr) ≤ exp(β N_c)`,
which gives `Z_p(β) ∈ [exp(−β N_c), exp(β N_c)]`.

For `β > 0` small enough that `exp(β N_c) − 1 < 1` (i.e.,
`β < log(2)/N_c`):
```
|w̃(U)| ≤ |exp(−β · Re tr) − Z_p| / Z_p
       ≤ (exp(β N_c) − exp(−β N_c)) / exp(−β N_c)
       = exp(2 β N_c) − 1
       ≤ 4 β N_c   (for β N_c < 1/2)
```

So **`||w̃||_∞ ≤ 4 N_c · β`** in the small-β regime.

### 3.4 Constants for the F3-Mayer package

Combining §3.2 and §3.3:
```
|K(Y)| ≤ (4 N_c β)^|Y|
```
which gives:
- **`r = 4 N_c · β`**
- **`A₀ = 1`**
- Validity regime: `β < log(2)/N_c` (the `||w̃||_∞ < 1` regime).

### 3.5 Geometric vanishing for non-connected Y

The BK construction sums over **trees on Y** weighted by integrals of
products of fluctuations. For the integral to be **non-zero**, the
gauge links touched by the plaquettes in the tree must be coupled —
i.e. the polymers must share gauge structure. For SU(N_c) Wilson, this
forces `Y` to be **gauge-connected**, which (via the geometry of
plaquettes-share-edges-iff-sites-are-adjacent) implies
`PolymerConnected Y` in the sense of `siteLatticeDist ≤ 1`.

**Lemma (formalisation target)**: If `Y` is not `PolymerConnected`,
then for every tree `T` on `Y`, at least one BK integrand vanishes
identically (because the disconnected part of `Y` integrates against
a zero-mean factor independently). Hence `K(Y) = 0`.

This is the geometric vanishing that justifies the `if` structure in
`hK_abs_le`. The proof is a Fubini argument: Haar measure factorises
across disjoint plaquette sets, and a disjoint factor with zero-mean
fluctuation contributes 0 to the product.

---

## 4. Lean implementation plan

### 4.1 New files

1. **`YangMills/ClayCore/MayerInterpolation.lean`** (~250 lines).
   - `def interpolatedClusterAverage (Y : Finset Plaquette) (s : Y → ℝ)`
     — the polynomial in `s_r ∈ [0,1]`.
   - `def truncatedKFromInterpolation (β F p q Y) : ℝ` — the BK formula.
   - `theorem truncatedK_zero_of_not_polymerConnected` — geometric
     vanishing (§3.5).
   - `theorem truncatedK_zero_of_card_one` — single-vertex K vanishes
     by `plaquetteFluctuationNorm_mean_zero`.

2. **`YangMills/ClayCore/HaarFactorization.lean`** (~150 lines).
   - The Fubini / independence lemma: if `Y₁, Y₂` are disjoint
     sets of plaquettes that share **no** gauge links, then
     `∫ ∏_{Y₁ ∪ Y₂} w̃ dHaar = ∫ ∏_{Y₁} w̃ · ∫ ∏_{Y₂} w̃ dHaar`.
   - **Mathlib gap**: this requires the product structure of Haar
     on `(SU(N_c))^E` for `E` a finite link set, and the projection
     to disjoint sublinks. Mathlib has `MeasureTheory.Measure.pi`
     but the explicit factorisation lemma may need to be added.

3. **`YangMills/ClayCore/BrydgesKennedyEstimate.lean`** (~250 lines).
   - `theorem truncatedK_abs_le_normSup_pow`:
     `|K(Y)| ≤ ||w̃||_∞^|Y|` (the BK bound).
   - Proof structure: trees-on-Y enumeration via
     `SimpleGraph.spanningTree`, BK weight bookkeeping, integral
     bound. **Heaviest piece** of the blueprint.

4. **`YangMills/ClayCore/PhysicalConnectedCardDecayWitness.lean`** (~100 lines).
   - Combine the above three to produce
     `physicalConnectedCardDecayMayerWitness`:
     for `β < log(2)/N_c`, gives a `PhysicalConnectedCardDecayMayerData
     N_c (4 N_c β) 1 ...`.

### 4.2 Edits to existing files

- `WilsonPolymerActivity.lean`: add a derived theorem
  `wilsonPolymerActivityBound_of_smallBeta β N_c (h : β < log(2)/N_c)
  : WilsonPolymerActivityBound N_c` that consumes the BK witness.
- `ZeroMeanCancellation.lean`: add `WilsonUniformRpowBound` witness
  via the F3 packages once both Mayer (this blueprint) and Count
  (companion blueprint, exponential frontier) are closed.

### 4.3 Mathlib gaps to expect

The BK construction relies on:

(a) **Cayley's formula** / counting of trees on a finite set.
    Mathlib has `SimpleGraph.spanningTree` but the cardinality
    estimate `|spanning_trees(K_n)| = n^(n-2)` is not formalised.
    **Workaround**: avoid the explicit tree count by bounding via
    the BK forest estimate directly (which only needs `tree_count ≤
    n^(n−2)`, not equality).

(b) **Haar product factorisation** on link products.
    Mathlib has `MeasureTheory.Measure.pi` and `IsHaarMeasure` for
    locally compact groups; `IsHaarMeasure (pi μ_i) = pi (IsHaarMeasure μ_i)`
    is in `MeasureTheory.Constructions.Pi`. The application to Wilson
    plaquettes needs a wrapper but no upstream PR.

(c) **L^∞ supremum of normalised fluctuation**.
    Mathlib has `essSup` for measure-theoretic supremum. For a
    continuous function on a compact group, `||f||_∞ = sup |f|`.
    SU(N_c) is compact; the fluctuation is continuous; so this is
    direct.

No upstream PR appears strictly necessary; all gaps are workable
locally.

---

## 5. Integration with F3-Count (Resolution C)

Once both blueprints close:

```
F3-Mayer:      ConnectedCardDecayMayerData N_c r A₀         with r = 4 N_c β,  A₀ = 1
F3-Count:      ShiftedConnectingClusterCountBoundExp 1 K    with K = 7 (for d=4)
Combined:      requires r · K < 1, i.e.  4 N_c β · 7 < 1
                                         β < 1 / (28 N_c)
```

This is **the convergence radius** of the SU(N_c) lattice-gauge
high-temperature cluster expansion. For N_c = 3 (physical QCD), this
gives `β < 1/84 ≈ 0.012`. For N_c = 2, `β < 1/56 ≈ 0.018`.

These are **small-coupling** regimes in lattice units — i.e. the
**weak-confinement / strong-coupling** phase, which is precisely
where the cluster expansion converges and where the mass gap can
be proved via this technique. Beyond this regime (intermediate /
strong confinement) the cluster expansion fails and other tools
(reflection positivity, RG, large-N) are needed, but those are NOT
the L3 closure target — the small-β rpow bound suffices for the Clay
mass-gap statement.

---

## 6. Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| BK forest estimate is too heavy to formalise in Lean directly | medium | Use the simpler Battle–Federbush variant or the explicit cluster-by-cluster bound (~50% slower constants but ~30% less Lean code) |
| Haar factorisation across disjoint plaquette link sets is more delicate than `MeasureTheory.Measure.pi` provides | medium | Develop a small `WilsonHaarFactorization` module (~150 lines) wrapping the pi structure for Wilson plaquettes specifically; do not attempt upstream |
| `||w̃||_∞ ≤ 4 N_c β` constant is loose; tighter constants needed for physical β-regimes | low | The constant only matters for the convergence radius, not for existence. A loose bound is acceptable; tightening can be deferred |
| `truncatedK_zero_of_not_polymerConnected` requires gauge-link factorisation that doesn't reduce cleanly to site connectivity | medium-high | Prove a slightly weaker geometric vanishing (e.g. for "edge-disjoint" rather than "site-distance > 1") and absorb the gap into the count side |
| Codex iterates on naming / canary scaffolding for the structures without ever attacking the BK estimate | medium | The scheduled audit (`COWORK_AUDIT.md`) flags canary spam after 10 consecutive same-prefix releases; this catches it within 24h |

---

## 7. Action items

For Codex (autonomous):

- [ ] Read this blueprint AND `BLUEPRINT_F3Count.md`.
- [ ] Decide order of attack: F3-Count Resolution C is mechanically
      smaller (~400 lines) and provides the constants `K_count = 7`
      that this blueprint depends on. **Recommendation: F3-Count
      first, then F3-Mayer**.
- [ ] Begin with file (1) `MayerInterpolation.lean`. Define the
      polynomial `interpolatedClusterAverage` and prove the trivial
      properties (linearity, vanishing at `s=0`, agreement with
      cluster average at `s=1`).
- [ ] After (1), proceed to (2) `HaarFactorization.lean`. Test the
      independence lemma on the simplest case (two single-plaquette
      polymers) before generalising.
- [ ] After (2), close (3) `BrydgesKennedyEstimate.lean`. **This is
      the analytic boss**. If stuck for more than 3 days, raise to
      Lluis with a minimum reproducible failure case.
- [ ] After (3), file (4) `PhysicalConnectedCardDecayWitness.lean`
      packages everything for `PhysicalShiftedF3MayerPackage`.

For Lluis (human review):

- [ ] Confirm the constants in §3.4 (`r = 4 N_c β`, `A₀ = 1`, regime
      `β < log(2)/N_c`) match the analytic regime intended by the
      project. Specifically: do you target N_c = 3 (physical QCD) or
      arbitrary N_c?
- [ ] Sign off on §5: combined regime `β < 1/(28 N_c)`. Confirm this
      is acceptable for the L3 / Clay statement and matches the
      `kpParameter β` used in `WilsonUniformRpowBound`.
- [ ] Decide whether the BK forest formalisation should be done
      in-repo (heavier, ~250 lines of analysis) or upstreamed to
      Mathlib as a `MeasureTheory.ClusterExpansion.BrydgesKennedy`
      module (much larger surface area, but reusable for future
      formalisations).

---

## 8. Connection to the larger Clay closure

Once both F3 packages close with the constants in §5:

```
(Mayer witness) ⊕ (Count witness)
    → ShiftedF3MayerCountPackage
    → PhysicalOnlyShiftedF3MayerCountPackage
    → WilsonUniformRpowBound N_c β C
    → clayMassGap_small_beta_of_uniformRpow N_c β C
    → ClayYangMillsMassGap N_c
```

with mass `m = kpParameter β` and prefactor `C = ⟨F⟩-bound · BK constant`.

This is the **authentic non-vacuous** Clay mass-gap target for
arbitrary N_c — substantially stronger than the `ClayYangMillsTheorem`
(vacuous existential) currently closed.

---

*End of blueprint. Last updated 2026-04-25.*
