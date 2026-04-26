# F3_MAYER_DEPENDENCY_MAP.md

**Cowork-authored mathematician-readable dependency map for the F3-MAYER closure path.**
**Filed: 2026-04-26T19:00:00Z, parallel to `F3_COUNT_DEPENDENCY_MAP.md`.**
**Status of `F3-MAYER` in `UNCONDITIONALITY_LEDGER.md`: `BLOCKED` (gated on F3-COUNT closure first).**
**Status of `F3-COUNT`: `CONDITIONAL_BRIDGE` (post-v2.54). F3-MAYER cannot be the active front until F3-COUNT row moves to `FORMAL_KERNEL`.**

This document is a planning blueprint, not a proof. It is the input
Codex will use to schedule v2.5n+ work on F3-MAYER once F3-COUNT closes.
It does not move any LEDGER row. It does not change the lattice 28% /
23–25% / Clay-as-stated 5% / named-frontier 50% headline numbers.

All file references are absolute paths in `YangMills/`; line numbers were
generated from live `Grep` output at filing time.

This map mirrors the structure of `F3_COUNT_DEPENDENCY_MAP.md` for
consistency:
- §(a) existing Lean artifacts;
- §(b) missing theorems with proposed Lean signatures;
- §(c) precise statement of the Brydges-Kennedy / Mayer-Ursell identity;
- §(d) cluster-series convergence argument;
- §(e) final assembly into the F3-COMBINED package.

---

## Goal restated

Prove a constructive witness for

```lean
ConnectedCardDecayMayerData N_c (4 N_c β) 1 hr_nonneg hA_nonneg
```

at small inverse coupling `β < log(2) / N_c` (the BK convergence regime).
This witness, combined with F3-COUNT's `ShiftedConnectingClusterCountBoundExp`
package and the smallness condition `K · r < 1` (i.e. `7 · 4 N_c β < 1`,
giving `β < 1/(28 N_c)` for d=4), bundles into

```lean
ShiftedF3MayerCountPackageExp N_c wab
```

which feeds `clayMassGap_of_shiftedF3MayerCountPackageExp` to produce a
`ClayYangMillsMassGap N_c` for `N_c ≥ 2` at small β.

The Mayer side and the Count side are **independent** analytic obligations
that compose only at the final assembly.

---

## (a) Lean theorems already proven

In topologically sorted order from algebraic foundation up through current
target structures.

### A.0 — Wilson connected correlator (`L4_WilsonLoops/WilsonLoop.lean`)

| Line | Identifier | Role |
|---:|---|---|
| 54 | `wilsonConnectedCorr` (`noncomputable def`) | The connected correlator `⟨F_p · F_q⟩ − ⟨F_p⟩⟨F_q⟩` whose decay the Mayer/Ursell identity packages |

### A.1 — Algebraic Mayer cluster expansion (`ClayCore/MayerIdentity.lean`, 229 lines, oracle-clean per BLUEPRINT_F3Mayer.md §1.1)

| Line | Identifier | Role |
|---:|---|---|
| 88 | `plaquetteFluctuationRaw` (`noncomputable def`) | Raw fluctuation `w_raw := plaquetteWeight − 1` |
| 94 | `plaquetteWeight_eq_one_add_raw` | Identity `plaquetteWeight = 1 + w_raw` |
| 101 | `plaquetteFluctuationRaw_zero_beta` | `w_raw|_{β=0} = 0` |
| 115 | `wilsonClusterActivityRaw` (`noncomputable def`) | `∫ ∏_{p∈γ} w_raw dHaar` |
| 138 | `boltzmann_cluster_expansion_pointwise` | The algebraic identity `exp(−β·∑_p E(U)) = ∑_{S⊆P} ∏_{r∈S} w_raw(U)` |
| 180 | `partition_function_cluster_expansion` | Integrated form of the cluster expansion |
| 210 | `yang_mills_from_mayer_expansion` | End-to-end chain Mayer → Clay, **gated** on a pointwise rpow bound (the analytic input §(b) addresses) |

### A.2 — Single-plaquette zero-mean cancellation (`ClayCore/ZeroMeanCancellation.lean`, 398 lines, oracle-clean)

The keystone — the single-plaquette inputs the BK estimate needs.

| Line | Identifier | Role |
|---:|---|---|
| 69 | `singlePlaquetteZ` (`noncomputable def`) | `Z_p(β) := ∫ plaquetteWeight dHaar` |
| 82 | `singlePlaquetteZ_pos` | `0 < Z_p(β)` |
| 126 | `plaquetteFluctuationNorm` (`noncomputable def`) | `w̃ := plaquetteWeight / Z_p − 1` (normalised fluctuation, **the variable amenable to BK**) |
| 142 | `plaquetteFluctuationNorm_mean_zero` | `∫ w̃ dHaar = 0`. **The keystone lemma** — this is the cancellation that makes Möbius inversion produce a useful truncation |
| 163 | `plaquetteFluctuationNorm_zero_beta` | `w̃|_{β=0} ≡ 0` (sanity) |

### A.3 — Truncated-activity scaffolding (`ClayCore/MayerExpansion.lean`, 301 lines, oracle-clean)

| Line | Identifier | Role |
|---:|---|---|
| 50 | `TruncatedActivities` (`structure`) | Carrier with fields `K`, `K_bound`, `K_bound_nonneg`, `K_abs_le`, `summable_K_bound` |
| 69 | `summable_abs_K` | `Summable |K|` from the bound |
| 76 | `summable_K` | `Summable K` |
| 103 | `connectingSum p q` (`noncomputable def`) | `∑_{Y connecting p,q} K(Y)` — the connected correlator target |
| 109 | `connectingBound p q` (`noncomputable def`) | `∑_{Y connecting p,q} K_bound(Y)` — the rpow majorant |
| 195 | `abs_connectingSum_le_connectingBound` | `|connectingSum p q| ≤ connectingBound p q` |
| 228 | `two_point_decay_from_truncated` | Translate truncated activity bound into two-point decay |
| 245 | `TruncatedActivities.ofBound` (`noncomputable def`) | Construct from a generic bound |
| 262 | `TruncatedActivities.ofCardDecay` (`noncomputable def`) | Construct from a card-decay bound `r^|Y|` |

### A.4 — Activity bridge to Bałaban small-field machinery (`ClayCore/WilsonPolymerActivity.lean`, oracle-clean)

| Line | Identifier | Role |
|---:|---|---|
| 91 | `WilsonPolymerActivityBound` (`structure`) | Activity bound: `β`, `r`, `A₀`, `K`, hypothesis `|K γ| ≤ A₀ · r^|γ|`, plus `hr_nonneg`, `hr_pos`, `hr_lt1` |

### A.5 — Card-decay → Mayer-data bridge (`ClayCore/ClusterRpowBridge.lean`, lines 1738–2330)

| Line | Identifier | Role |
|---:|---|---|
| 1738 | `TruncatedActivities.ofConnectedCardDecay` (`noncomputable def`) | Construct a TruncatedActivities from a card-decay-with-connectedness K function |
| 1761 | `TruncatedActivities.ofConnectedCardDecay_K` | Simp lemma for the K field |
| 1776 | `TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay` | The bound holds |
| 1795 | `TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected` | Geometric vanishing baked into the bound |
| 2229 | `ConnectedCardDecayMayerData` (`structure`) | **THE TARGET STRUCTURE.** Fields: `K` (raw activity); `hK_abs_le` (`|K(Y)| ≤ if connected then A₀ · r^|Y| else 0`); `h_mayer` (Wilson connected correlator = TruncatedActivities.connectingSum, the **Mayer/Ursell identity**) |

### A.6 — Cluster correlator consumer (`ClayCore/ClusterCorrelatorBound.lean`)

| Line | Identifier | Role |
|---:|---|---|
| 44 | `two_point_decay_from_cluster_tsum` | Two-point decay from a cluster series |
| 82 | `two_point_decay_from_cluster_tsum_exp` | Exponential variant |
| 142 | `clusterCorrelatorBound_of_truncatedActivities` | Apply TruncatedActivities to derive correlator decay |
| 401 | `clusterCorrelatorBound_of_truncatedActivities_ceil_exp` | Exponential ceil variant |
| 494 | `clusterCorrelatorBound_of_finiteConnectingBounds_ceil` | Connect to finite-volume bound |

### A.7 — Final F3-COMBINED assembly (`ClayCore/ClusterRpowBridge.lean`, lines 4355+)

| Line | Identifier | Role |
|---:|---|---|
| 4355 | `ShiftedF3MayerCountPackageExp` (`structure`) | The single Clay-facing assembly object: pairs `data : ConnectedCardDecayMayerData ...` with `h_count : ShiftedConnectingClusterCountBoundExp ...` plus smallness `K · wab.r < 1` |
| 4371 | `ShiftedF3MayerCountPackageExp.ofSubpackages` (`def`) | Combine independently-produced Mayer + Count packages |
| 4855 | `clayMassGap_of_shiftedF3MayerCountPackageExp` (`noncomputable def`) | **THE TERMINAL ENDPOINT.** Produces `ClayYangMillsMassGap N_c` from the package |

The terminal `clayMassGap_of_shiftedF3MayerCountPackageExp` at line 4855
is conditional on having an inhabitant of `ShiftedF3MayerCountPackageExp`,
which in turn requires:
- A `ConnectedCardDecayMayerData` (the F3-MAYER witness — what §(b) closes).
- A `ShiftedConnectingClusterCountBoundExp` (the F3-COUNT witness — gated on `F3_COUNT_DEPENDENCY_MAP.md` §(b)/B.1 + B.2).
- A smallness proof `K · r < 1` (concrete: `7 · 4 N_c β < 1`, i.e. `β < 1/(28 N_c)`).

---

## (b) Lean theorems still missing

Six theorems are required to close the F3-MAYER side. Together they
inhabit `ConnectedCardDecayMayerData N_c (4 N_c β) 1 hr_nonneg hA_nonneg`
for `β < log(2)/N_c`.

### B.1 — Truncated-activity vanishing on single-vertex polymers

**Proposed Lean signature**:

```lean
theorem truncatedK_zero_of_card_one
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ) (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L)) (hY : Y.card = 1) :
    truncatedK β F p q Y = 0
```

**Dependency**: A.2 line 142 (`plaquetteFluctuationNorm_mean_zero`).

**Difficulty**: **EASY.** Direct unfolding: `K({r}) = ⟨w̃⟩ = 0` by
zero-mean. ~30 LOC.

### B.2 — Truncated-activity vanishing on geometrically disconnected polymers

**Proposed Lean signature**:

```lean
theorem truncatedK_zero_of_not_polymerConnected
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ) (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L))
    (hY : ¬ PolymerConnected Y) :
    truncatedK β F p q Y = 0
```

**Dependency**: A.2 line 142 + Haar factorisation lemma (Mathlib's
`MeasureTheory.Measure.pi` + Wilson-specific wrapper).

**Difficulty**: **MEDIUM.** Fubini argument: Haar factorises across
disjoint plaquette sets, and a disjoint factor with zero-mean fluctuation
contributes 0 to the product. ~150 LOC, mostly Wilson-Haar wrapping.

### B.3 — BK polymer-bound `|K(Y)| ≤ ||w̃||_∞^|Y|` (the analytic boss)

**Proposed Lean signature**:

```lean
theorem truncatedK_abs_le_normSup_pow
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (F : G → ℝ) (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L))
    (hY_conn : PolymerConnected Y) :
    |truncatedK β F p q Y| ≤ ‖plaquetteFluctuationNorm N_c β‖_∞ ^ Y.card
```

**Dependency**: BK forest interpolation formula (or the Battle-Federbush
variant per BLUEPRINT_F3Mayer.md §3); Mathlib `SimpleGraph.spanningTree`;
explicit BK weight bookkeeping; `essSup` machinery.

**Difficulty**: **HIGH.** The heaviest piece: ~250 LOC, involves
random-walk interpolation and tree-on-Y enumeration. BLUEPRINT_F3Mayer
§4.1 file (3) (`BrydgesKennedyEstimate.lean`).

### B.4 — Sup bound on the normalised fluctuation: `||w̃||_∞ ≤ 4 N_c · β`

**Proposed Lean signature**:

```lean
theorem plaquetteFluctuationNorm_sup_le
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (hβ : β > 0) (hβ_small : β < Real.log 2 / N_c) :
    ‖plaquetteFluctuationNorm N_c β‖_∞ ≤ 4 * N_c * β
```

**Dependency**: A.2 lines 69 + 126 + the inequality `|Re tr U| ≤ N_c` for
`U ∈ SU(N_c)`; Mathlib `Real.exp` arithmetic.

**Difficulty**: **EASY-MEDIUM.** Algebra of exponentials per BLUEPRINT
§3.3:
`|w̃| ≤ exp(2 β N_c) − 1 ≤ 4 β N_c` for `β N_c < 1/2`. ~80 LOC.

### B.5 — Mayer/Ursell identity in the project's notation

**Proposed Lean signature**:

```lean
theorem truncatedK_satisfies_mayer_identity
    {N_c : ℕ} [NeZero N_c] (β : ℝ) (hβ : 0 < β) (F : G → ℝ) (hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L) (hpq : 1 ≤ siteLatticeDist p.site q.site) :
    wilsonConnectedCorr (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F p q
    = (TruncatedActivities.ofConnectedCardDecay
        (truncatedK β F p q) p q (4 * N_c * β) 1
        (by positivity) zero_le_one
        (truncatedK_abs_le_card_decay β F p q)).connectingSum p q
```

**Dependency**: A.1 line 138 (`boltzmann_cluster_expansion_pointwise`),
A.5 line 1738 (`TruncatedActivities.ofConnectedCardDecay`), B.1 + B.2 +
B.3 + B.4 (to construct the bound argument).

**Difficulty**: **MEDIUM-HIGH.** Möbius inversion to extract truncated
activity from the algebraic expansion + identification with the BK
formula. ~200 LOC.

### B.6 — The bundled witness

**Proposed Lean signature**:

```lean
def physicalConnectedCardDecayMayerWitness
    (N_c : ℕ) [NeZero N_c] (β : ℝ) (hβ : 0 < β) (hβ_small : β < Real.log 2 / N_c) :
    ConnectedCardDecayMayerData N_c (4 * N_c * β) 1
      (by positivity) zero_le_one
```

**Dependency**: B.1 + B.2 + B.3 + B.4 + B.5.

**Difficulty**: **EASY.** Glue: assemble fields from B.1–B.5. ~50 LOC.
This is the BLUEPRINT_F3Mayer §4.1 file (4) shrunken from ~100 to ~50 LOC
once `ofSubpackages` exists at A.7 line 4371.

### Summary of B.* difficulty + LOC

| Step | Difficulty | LOC | Mathlib helpers needed |
|---|---|---:|---|
| B.1 single-vertex K = 0 | EASY | ~30 | none (uses A.2 line 142) |
| B.2 disconnected K = 0 | MEDIUM | ~150 | `MeasureTheory.Measure.pi` + Wilson wrapper |
| B.3 BK bound `|K(Y)| ≤ ‖w̃‖^|Y|` | **HIGH** | ~250 | `SimpleGraph.spanningTree`, `essSup` |
| B.4 `‖w̃‖∞ ≤ 4 N_c β` | EASY-MEDIUM | ~80 | `Real.exp` algebra |
| B.5 Mayer/Ursell identity | MEDIUM-HIGH | ~200 | Möbius/Ursell formula bookkeeping |
| B.6 bundled witness | EASY | ~50 | none |
| **Total** | | **~760** | matches BLUEPRINT_F3Mayer ~700 LOC estimate |

---

## (c) Precise statement of the Brydges-Kennedy / Mayer-Ursell identity

The identity is encoded by `ConnectedCardDecayMayerData.h_mayer` at
`ClusterRpowBridge.lean:2245`:

```lean
h_mayer : ∀ {d L} ... (β : ℝ) (hβ : 0 < β) (F : G → ℝ) (hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L)
    (hpq : 1 ≤ siteLatticeDist p.site q.site),
  wilsonConnectedCorr (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F p q
  = (TruncatedActivities.ofConnectedCardDecay
      (K β F p q) p q r A₀ hr_nonneg hA_nonneg
      (hK_abs_le β F p q)).connectingSum p q
```

**Mathematical statement (informal)**:

> For SU(N_c) Wilson lattice gauge theory, the connected two-point Wilson
> correlator
> ```
> ⟨F_p ; F_q⟩_β := ⟨F_p · F_q⟩_β − ⟨F_p⟩_β · ⟨F_q⟩_β
> ```
> equals a sum over polymers `Y` containing both plaquettes `p, q`, where
> each polymer carries a truncated activity `K(β, F, p, q, Y)` defined by
> the Brydges-Kennedy random-walk / forest interpolation formula:
> ```
> ⟨F_p ; F_q⟩_β = ∑_{Y ⊆ Plaquettes, p,q ∈ Y, Y connected} K(β, F, p, q, Y).
> ```

**Why each ingredient appears**:

1. The truncated-activity vanishes on single-vertex polymers (B.1) because
   `⟨w̃⟩ = 0` (zero-mean cancellation, `plaquetteFluctuationNorm_mean_zero`).
2. The truncated-activity vanishes on geometrically disconnected polymers
   (B.2) because Haar factorises across disjoint links, and one
   zero-mean factor kills the integral.
3. The truncated-activity is bounded by `|K(Y)| ≤ ||w̃||_∞^|Y|` (B.3) by
   the Brydges-Kennedy forest estimate (no `|Y|!` blowup).
4. `||w̃||_∞ ≤ 4 N_c · β` (B.4) gives the activity bound `r = 4 N_c · β`,
   `A₀ = 1`.
5. The Mayer/Ursell identity itself (B.5) is the equality between
   the connected correlator and the truncated polymer sum, derivable
   from Möbius inversion on the partition lattice applied to
   `boltzmann_cluster_expansion_pointwise` (`MayerIdentity.lean:138`).

**Cross-check with project conventions**: The identity is stated in the
project's existing `wilsonConnectedCorr` / `TruncatedActivities` /
`ConnectedCardDecayMayerData` vocabulary at `ClusterRpowBridge.lean`
lines 2245–2255. No new infrastructure needed.

---

## (d) Cluster-series convergence argument

Once §(c)'s `ConnectedCardDecayMayerData` is built, the project's
existing consumer machinery (A.6 + A.7) gives the cluster-series bound
needed by `clayMassGap_of_shiftedF3MayerCountPackageExp` at line 4855.

The convergence argument is the standard Kotecký-Preiss criterion: with
`A₀ = 1`, `r = 4 N_c · β`, and the F3-COUNT side providing
`count(n) ≤ K^n` with `K = 7` (for d=4), the cluster series
```
∑_{n ≥ 1} count(n) · A₀ · r^n  =  ∑_{n ≥ 1} 7^n · 1 · (4 N_c β)^n
                                =  ∑_{n ≥ 1} (28 N_c β)^n
```
converges as a geometric series iff `28 N_c · β < 1`, i.e.

```
β < 1 / (28 N_c).
```

For physical QCD (`N_c = 3`): `β < 1/84 ≈ 0.012`. This is the convergence
radius of the SU(N_c) lattice-gauge high-temperature cluster expansion.

**Pseudocode for the assembly** (mathematician-grade):

```
def F3CombinedWitness
    (N_c : ℕ, hN : 2 ≤ N_c, β : ℝ, hβ : β < 1 / (28 N_c)) :
    ShiftedF3MayerCountPackageExp N_c (wabFromBeta β):
  let mayer  := physicalConnectedCardDecayMayerWitness N_c β ...           -- B.6
  let count  := physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296
                                                                          -- F3-COUNT B.2
  let hKr_lt1 : count.K * (4 * N_c * β) < 1 := by
    have : count.K = 7 := count.K_eq_seven                  -- F3-COUNT lemma
    simp [this]; nlinarith [hβ]
  ShiftedF3MayerCountPackageExp.ofSubpackages mayer count hKr_lt1
```

**Why this terminates and gives the Clay structure**: the consumer
`clayMassGap_of_shiftedF3MayerCountPackageExp` at line 4855 takes the
package as input and returns `ClayYangMillsMassGap N_c`. The smallness
condition `K · r < 1` is the Kotecký-Preiss convergence radius;
everything downstream is mechanical glue.

---

## (e) Final F3-COMBINED assembly

After §(b)/B.6 + F3-COUNT closure + §(d) glue, the consumer at line 4855
fires:

```lean
noncomputable def clayMassGap_of_shiftedF3MayerCountPackageExp
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackageExp N_c wab) :
    ClayYangMillsMassGap N_c
```

with `pkg` discharged unconditionally by §(d)'s F3CombinedWitness.

**Effect on `UNCONDITIONALITY_LEDGER.md`**:

| Row | Before | After §(b)/B.* + F3-COUNT B.1+B.2 + §(d) all land |
|---|---|---|
| `F3-COUNT` | `CONDITIONAL_BRIDGE` | `FORMAL_KERNEL` |
| `F3-MAYER` | `BLOCKED` | `FORMAL_KERNEL` |
| `F3-COMBINED` | `BLOCKED` | `FORMAL_KERNEL` |

**Effect on `registry/progress_metrics.yaml`**:

| Component | Current `contribution_percent` | After full F3 closure |
|---|---:|---:|
| F3-COUNT | 5 | **20** (full headline weight) |
| F3-MAYER | 0 | **20** (full headline weight) |
| F3-COMBINED | 0 | **10** (full headline weight) |

The `lattice_small_beta` headline would move ~28% → ~73% (assuming all
three F3-* component weights are realised). **This bound applies only
after §(b)/B.1–B.6 are proven AND F3-COUNT closes. Until both happen,
the headline 28% / 23–25% / 5% / 50% numbers stand unchanged.**

A jump to ~73% lattice would still leave Clay-as-stated at ~10–12% per
`CLAY_HORIZON.md` §(iii) honest growth ceiling — the OUT-* rows
(`OUT-CONTINUUM`, `OUT-OS-WIGHTMAN`, `OUT-STRONG-COUPLING`) remain
BLOCKED regardless of lattice progress, and they are the dominant Clay
obstacles.

---

## Honesty discipline

- This document is a **plan / honesty instrument**, not a proof. Filing
  it does not move any LEDGER row.
- F3-MAYER row remains `BLOCKED` (gated on F3-COUNT closure first).
- F3-COUNT row remains `CONDITIONAL_BRIDGE` (post-v2.54). The §(b)/B.*
  here will fire only after F3-COUNT moves to `FORMAL_KERNEL` (i.e.
  Codex lands the v2.55 root-avoiding strengthening + the v2.56 word
  decoder iteration per `F3_COUNT_DEPENDENCY_MAP.md`).
- The §(d) "after both close" effect on percentages is **conditional** on
  the actual Lean proofs landing. No infrastructure win, no
  documentation win, no blueprint quality alone moves the percentages.
- The §(e) `lattice_small_beta` jump from 28% → 73% is the asymptotic
  upper bound assuming ALL of B.1–B.6 + F3-COUNT B.1+B.2 close cleanly.
  It does NOT include any `OUT-*` (continuum / OS-Wightman / strong
  coupling) progress; Clay-as-stated remains capped at ~10-12% per
  CLAY_HORIZON.md.

---

## Cross-references

- `BLUEPRINT_F3Mayer.md` — original Cowork reconnaissance doc; this
  dependency map is its concrete, file-line-cited successor.
- `F3_COUNT_DEPENDENCY_MAP.md` — sibling dependency map for F3-COUNT;
  same structure (a)–(e). F3-MAYER cannot fire until F3-COUNT's §(b)/B.1
  + B.2 land.
- `UNCONDITIONALITY_LEDGER.md:98` — F3-MAYER row, status BLOCKED.
- `UNCONDITIONALITY_LEDGER.md:99` — F3-COMBINED row, status BLOCKED on
  both F3-COUNT + F3-MAYER.
- `JOINT_AGENT_PLANNER.md` critical path step 3 (`F3-MAYER-URSSELL`)
  matches §(b)/B.5 + B.6 one-to-one.
- `ConnectedCardDecayMayerData` at `ClusterRpowBridge.lean:2229` —
  the target structure §(b)/B.6 inhabits.
- `clayMassGap_of_shiftedF3MayerCountPackageExp` at
  `ClusterRpowBridge.lean:4855` — the terminal endpoint §(d) feeds.
- `CLAY_HORIZON.md` — explains why even full F3-* closure leaves
  Clay-as-stated capped at ~10-12% (continuum + OS/Wightman + strong
  coupling are out of scope).

---

## Suggested Codex schedule for after F3-COUNT closes

(F3-COUNT closure is required first; this schedule starts when Codex
lands v2.55 root-avoiding strengthening + v2.56 word decoder iteration.)

1. **v2.6N**: prove §(b)/B.1 + B.2 + B.4 in `MayerInterpolation.lean`
   + `HaarFactorization.lean`. ~260 LOC. The "easy + medium" Mayer
   ingredients. Uses `plaquetteFluctuationNorm_mean_zero` (A.2:142),
   `MeasureTheory.Measure.pi`, and basic exp arithmetic. Mathlib
   pre-check: search for explicit `Measure.pi.disjoint_factorise` or
   equivalent before writing the Wilson wrapper from scratch.

2. **v2.6N+1**: prove §(b)/B.3 in `BrydgesKennedyEstimate.lean`. ~250
   LOC. **The analytic boss.** Tree-on-Y enumeration; BK forest weight
   bookkeeping; bound combination. Mathlib pre-check: search for any
   Brydges-Kennedy / forest-formula content (likely none; this may be
   the only place a Mathlib PR is needed for an upstream contribution).

3. **v2.6N+2**: prove §(b)/B.5 + B.6 in
   `MayerInterpolationBridgeIdentity.lean` + `PhysicalConnectedCardDecayMayerWitness.lean`.
   ~250 LOC. The Mayer/Ursell identity + the bundled witness.

4. **v2.6N+3**: §(d) F3-COMBINED assembly via
   `ShiftedF3MayerCountPackageExp.ofSubpackages`. ~50 LOC of glue. Apply
   the consumer at line 4855 to produce `ClayYangMillsMassGap N_c`
   for `N_c ≥ 2` at `β < 1/(28 N_c)`. **F3-MAYER row moves to
   `FORMAL_KERNEL`; F3-COMBINED row moves to `FORMAL_KERNEL`; LEDGER
   percentages bump per §(e)'s table (Cowork audit required).**

After v2.6N+3: `F3-COUNT`, `F3-MAYER`, `F3-COMBINED` all closed. Lattice
small-β subgoal substantially complete (modulo the 5 Tier-2 axioms).
The next live front becomes Tier-2 axiom retirement (EXP-MATEXP-DET
Mathlib PR landing, EXP-LIEDERIVREG reformulation, etc.).

---

*End of F3-MAYER dependency map. Filed by Cowork as deliverable for
`COWORK-F3-MAYER-DEPENDENCY-MAP-001` per dispatcher instruction at
2026-04-26T18:50:00Z. F3-MAYER remains BLOCKED; F3-COUNT remains
CONDITIONAL_BRIDGE; no LEDGER row moved.*
