# F3_CHAIN_MAP.md

**Author**: Cowork agent (Claude), structural map pass 2026-04-25
**Subject**: definitive dependency graph of the F3 frontier chain from
raw inputs to `ClayYangMillsMassGap N_c` and `ClayYangMillsPhysicalStrong`
**Method**: trace declarations across `YangMills/ClayCore/`,
`YangMills/L8_Terminal/`, and `YangMills/L7_Continuum/` at v1.85.0.

This document is intended as a single-page (well, single-document)
overview that anyone — Codex, Cowork agent, Lluis, external reviewer —
can use to navigate the F3 chain without opening every Lean file.

---

## 0. Top-level diagram

```
  ┌─────────────────────────┐    ┌──────────────────────────┐
  │  F3-MAYER WITNESS       │    │  F3-COUNT WITNESS        │
  │  (Priority 2.x, OPEN)   │    │  (Priority 1.2, OPEN)    │
  │                         │    │                          │
  │  Brydges-Kennedy gives  │    │  Klarner BFS-tree gives  │
  │  ConnectedCardDecay     │    │  ShiftedConnecting       │
  │    MayerData N_c r A₀   │    │    ClusterCount          │
  │                         │    │    BoundExp C_conn K     │
  │  with r = 4·N_c·β,      │    │  with K = 2d-1 = 7       │
  │  A₀ = 1                 │    │  for d=4                 │
  └────────────┬────────────┘    └────────────┬─────────────┘
               │                              │
               │  (provided to)               │  (provided to)
               ▼                              ▼
  ┌─────────────────────────────────────────────────────────┐
  │  ShiftedF3MayerCountPackageExp.ofSubpackages            │
  │     mayer count hKr_lt1                                 │
  │  (LANDED: v1.82.0, oracle-clean)                        │
  │                                                         │
  │  Smallness: K · wab.r < 1 ⇔ β < 1/(28·N_c)              │
  │  For QCD N_c=3: β < 1/84 ≈ 0.012                        │
  └────────────────────────┬────────────────────────────────┘
                           │
                           ▼
  ┌─────────────────────────────────────────────────────────┐
  │  ShiftedF3MayerCountPackageExp N_c wab                  │
  │  (LANDED: v1.82.0, structure with all necessary fields) │
  └────────────────────────┬────────────────────────────────┘
                           │
              ┌────────────┴─────────────┐
              ▼                          ▼
  ┌──────────────────────┐    ┌────────────────────────────────┐
  │  Cluster correlator  │    │  Direct Clay endpoints         │
  │  bound               │    │  (LANDED: v1.82.0+)            │
  │  (LANDED: v1.81.0)   │    │                                │
  │                      │    │  clayMassGap_of_*  →           │
  │  cluster             │    │    ClayYangMillsMassGap N_c    │
  │   CorrelatorBound_   │    │                                │
  │   of_shiftedF3Mayer  │    │  clay_theorem_of_*  →          │
  │   CountPackageExp    │    │    ClayYangMillsTheorem        │
  └──────────────────────┘    │  (vacuous, audited)            │
                              │                                │
                              │  clayConnectedCorrDecay_of_* → │
                              │    ClayConnectedCorrDecay N_c  │
                              └────────────┬───────────────────┘
                                           │
                                           ▼
                              ┌────────────────────────────────┐
                              │  L8 Terminal endpoints         │
                              │  (LANDED: v1.84.0)             │
                              │                                │
                              │  physicalStrong_of_*  →        │
                              │    ClayYangMillsPhysicalStrong │
                              │  (with Finding 004 caveat)     │
                              │                                │
                              │  connectedCorrDecayBundle_of_* │
                              │    → bundles for further use   │
                              └────────────────────────────────┘
```

---

## 1. The two open inputs (Priority 1.2 and 2.x)

### 1.1 F3-Count witness (Priority 1.2)

**Target**:
```lean
connecting_cluster_count_exp_bound
    (d : ℕ) [NeZero d] :
  ShiftedConnectingClusterCountBoundExp 1 ((2*d - 1 : ℕ) : ℝ)
```

(Or with looser `(4 * d * d : ℕ)` from
`mathlib_pr_drafts/F3_Count_Witness_Sketch.lean` §3.)

**Status**: scaffolding landed v1.85.0 (`LatticeAnimalCount.lean`).
~99 LOC done out of ~410 LOC estimated. See `AUDIT_v185_LATTICEANIMAL.md`.

**Mathematical content**: connected polymers in the plaquette graph
of size `m` containing a fixed root are at most `Δ^(m-1)` in number,
where `Δ ≤ 2d - 1` is the maximum degree.

**Reference**: Klarner 1967 (cell-growth problems), Madras-Slade 1993
(self-avoiding walk).

### 1.2 F3-Mayer witness (Priority 2.1 → 2.4)

**Target**:
```lean
physicalConnectedCardDecayMayerWitness
    {N_c : ℕ} [NeZero N_c]
    (β : ℝ) (h_β_small : β < Real.log 2 / N_c) :
  PhysicalConnectedCardDecayMayerData N_c (4 * N_c * β) 1 ...
```

**Status**: not started. Will produce 4 files per `BLUEPRINT_F3Mayer.md`
§4.1:
- `MayerInterpolation.lean` (~250 LOC)
- `HaarFactorization.lean` (~150 LOC)
- `BrydgesKennedyEstimate.lean` (~250 LOC) — **the analytic boss**
- `PhysicalConnectedCardDecayWitness.lean` (~50 LOC, glue per
  `BLUEPRINT_F3Mayer.md` §−1 update)

**Mathematical content**: the Brydges-Kennedy random-walk cluster
expansion gives a truncated activity `K(Y)` for the Wilson connected
correlator with `|K(Y)| ≤ ‖w̃‖_∞^|Y|`, where `w̃` is the normalised
plaquette fluctuation.

**Reference**: Brydges-Kennedy 1987, Battle-Federbush 1984,
Seiler 1982 (ch. 4).

---

## 2. Closed plumbing (v1.79.0 - v1.84.0)

### 2.1 Frontier interfaces (v1.79.0)

In `YangMills/ClayCore/ConnectingClusterCountExp.lean` (~360 LOC):

| Declaration | Purpose |
|---|---|
| `ShiftedConnectingClusterCountBoundExp` | global frontier predicate |
| `ShiftedConnectingClusterCountBoundDimExp d` | fixed-d projection |
| `ShiftedConnectingClusterCountBoundAtExp d L` | fixed-d-L projection |
| `ShiftedF3CountPackageExp` | packaged form |
| `ShiftedF3CountPackageDimExp d` | dim-fixed package |
| `ShiftedF3CountPackageAtExp d L` | volume-fixed package |
| `PhysicalShiftedConnectingClusterCountBoundExp` | d=4 specialised |
| `PhysicalShiftedF3CountPackageExp` | d=4 packaged |
| `*.apply`, `*.toDim`, `*.toAt` | direct application + scope projections |
| `*.ofBound`, `*.ofAtFamily` | constructor variants |
| `shiftedConnectingClusterCountBoundAtExp_finite` | trivial volume-local witness (not the uniform target) |

### 2.2 KP-series prefactor (v1.80.0)

In `YangMills/ClayCore/ClusterSeriesBound.lean`:

| Declaration | Purpose |
|---|---|
| `clusterPrefactorExp r K C_conn A₀` | the prefactor `C_conn · A₀ · ∑' n, K^n · r^n` |
| `connecting_cluster_tsum_summable_exp` | summability of the profile under `K·r < 1` |
| `connecting_cluster_tsum_eq_factored_exp` | the factoring identity `∑' n, ... = clusterPrefactorExp · r^dist` |
| `clusterPrefactorExp_pos` | positivity |
| `connecting_cluster_tsum_le_exp` | the bound theorem |
| (4 more supporting theorems) | (intermediate plumbing) |

### 2.3 Bridge to ClusterCorrelatorBound (v1.81.0)

In `YangMills/ClayCore/ClusterRpowBridge.lean`:

| Declaration | Purpose |
|---|---|
| `TruncatedActivities.two_point_decay_from_cluster_tsum_exp` | fundamental two-point bound |
| `clusterPrefactorExp_rpow_ceil_le_exp` | rpow → exp conversion |
| `clusterCorrelatorBound_of_truncatedActivities_ceil_exp` | bridge endpoint |
| `clusterCorrelatorBound_of_cardBucketBounds_ceil_exp` | bucket-bounds variant |
| `clusterCorrelatorBound_of_count_cardDecayBounds_ceil_exp` | count + cardDecay variant |
| `finiteConnectingSum_le_of_cardBucketBounds_tsum_exp` | intermediate plumbing |
| `cardBucketSum_le_of_count_and_pointwise_exp` | intermediate plumbing |

### 2.4 Packaged Clay route (v1.82.0)

In `YangMills/ClayCore/ClusterRpowBridge.lean`:

| Declaration | Purpose |
|---|---|
| `ShiftedF3MayerCountPackageExp N_c wab` | unified Mayer + Count + smallness package |
| `ShiftedF3MayerCountPackageExp.ofSubpackages` | combine independently-produced halves |
| `clusterCorrelatorBound_of_shiftedF3MayerCountPackageExp` | terminal cluster bound |
| `clayWitnessHyp_of_shiftedF3MayerCountPackageExp` | Clay witness hypothesis |
| **`clayMassGap_of_shiftedF3MayerCountPackageExp`** | **terminal: `→ ClayYangMillsMassGap N_c`** |
| `clayConnectedCorrDecay_of_shiftedF3MayerCountPackageExp` | Connected-corr-decay variant |
| `clay_theorem_of_shiftedF3MayerCountPackageExp` | weak Clay theorem variant |

### 2.5 Physical d = 4 endpoint (v1.83.0)

In `YangMills/ClayCore/ClusterRpowBridge.lean`:

| Declaration | Purpose |
|---|---|
| `physicalClusterCorrelatorBound_of_expCountBound_mayerData_ceil` | d=4 specialised cluster bound |
| `physicalClusterCorrelatorBound_of_physicalMayerData_expCount_ceil` | d=4 from physical Mayer data |

### 2.6 L8 terminal endpoints (v1.84.0)

In `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

| Declaration | Purpose |
|---|---|
| `connectedCorrDecayBundle_of_expCountBound_mayerData_siteDist_measurableF` | bundles correlator decay + measure inputs |
| `connectedCorrDecayBundle_of_physicalMayerData_expCount_siteDist_measurableF` | physical-Mayer variant |
| **`physicalStrong_of_expCountBound_mayerData_siteDist_measurableF`** | **terminal: `→ ClayYangMillsPhysicalStrong`** |
| **`physicalStrong_of_physicalMayerData_expCount_siteDist_measurableF`** | physical-Mayer variant |

**Caveat**: `ClayYangMillsPhysicalStrong` includes
`HasContinuumMassGap m_lat`, which is satisfied via the
coordinated-scaling convention. See `COWORK_FINDINGS.md` Finding 004
and `GENUINE_CONTINUUM_DESIGN.md`.

---

## 3. Convergence regime (the smallness condition)

The chain depends on `K · wab.r < 1` where:
- `K` is the F3-Count constant (e.g. `2d - 1 = 7` for d=4 tight, or
  `4d² = 64` for d=4 loose).
- `wab.r = 4 · N_c · β` is the activity rate from F3-Mayer.

So the regime is `4 · N_c · β · K < 1`, i.e. `β < 1 / (4 · N_c · K)`.

| `K` choice | Regime for N_c = 3 (QCD) |
|---|---|
| Tight `2d - 1 = 7` | `β < 1/84 ≈ 0.012` |
| Loose `4d² = 64` | `β < 1/768 ≈ 0.0013` |

Both are within the high-temperature / weak-coupling cluster
expansion regime. The tight constant gives more physical β coverage;
the loose constant is faster to formalise.

---

## 4. The chain visualised as theorem composition

```
F3-Mayer witness
   ⨯ F3-Count witness
   ⨯ smallness (K · r < 1)
   ───────────────────────────────────
   = ShiftedF3MayerCountPackageExp.ofSubpackages
   ───────────────────────────────────
   = ShiftedF3MayerCountPackageExp N_c wab

ShiftedF3MayerCountPackageExp N_c wab
   ───────────────────────────────────
   = clayMassGap_of_shiftedF3MayerCountPackageExp
   ───────────────────────────────────
   = ClayYangMillsMassGap N_c
       with m = kpParameter wab.r = -log(4·N_c·β)/2 > 0
       and  C = clusterPrefactorExp wab.r K mayer.A₀ count.C_conn

OR via L8:

ShiftedF3MayerCountPackageExp N_c wab
   ⨯ Measurable F, 0 < β, |F| ≤ 1
   ───────────────────────────────────
   = physicalStrong_of_expCountBound_mayerData_siteDist_measurableF
   ───────────────────────────────────
   = ClayYangMillsPhysicalStrong (with Finding 004 caveat)
```

---

## 5. What an external reviewer should know

If you are evaluating this project, the chain above tells you:

1. **All the plumbing is in place.** From v1.85.0, the only
   substantive open theorems are the F3-Mayer witness (BK estimate)
   and the F3-Count witness (Klarner BFS-tree).
2. **Both are classical mathematics** with well-known proofs in the
   literature (citations in §1).
3. **The combined regime is high-temperature / weak-coupling**, not
   the full physical regime.
4. **The Clay-Millennium continuum extension** (continuum limit,
   Wightman / Osterwalder-Schrader) is not in scope; the v1.84.0
   `ClayYangMillsPhysicalStrong` reaches a coordinated-scaling
   formal version, not the genuine continuum statement.

What this project **will** establish on closure: a fully checked
machine proof of the lattice mass gap of SU(N_c) Yang-Mills at
small-β, via the standard cluster expansion technique. This is a
well-defined and non-trivial mathematical theorem.

What it will **not** establish: the Clay Millennium statement.

---

*Map complete 2026-04-25 by Cowork agent.*
