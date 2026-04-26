# THE ERIKSSON PROGRAMME — ROADMAP
## Estado: 2026-04-25 (versión repo: v1.83.0)

> **Refresh note (2026-04-25)**: this document was refreshed to reflect
> the F3 frontier reformulation that now drives Phase 5. The high-level
> phase structure (Phases 1-7) is unchanged. The Phase 5 mechanism has
> shifted from a generic "ConnectedCorrDecay via KP / Balaban
> bootstrap" framing to the F3-Mayer + F3-Count package decomposition
> documented in `BLUEPRINT_F3Count.md` and `BLUEPRINT_F3Mayer.md`.
> Older entries are preserved in git history.

## Arquitectura formal completa

### Explicit discharged hypotheses (Phases 1-4)
- `LatticeMassProfile.IsPositive`   ← Phase 3 (Balaban RG)
- `∃ m_inf : ℝ, 0 < m_inf`         ← Phase 2 (MaxEnt + Petz + Fawzi-Renner)
- `HasContinuumMassGap` (interfaz)  ← Phase 4 (UV scaling limit)

### Concrete non-vacuous endpoint witnesses (new in 2026-04)
- `u1_clay_yangMills_mass_gap_unconditional : ClayYangMillsMassGap 1` ← AbelianU1
  unconditional case (commit `AbelianU1Unconditional.lean`, 2026-04-23). First
  authentic inhabitant of `ClayYangMillsMassGap`.

### Active explicit hypotheses
1. `ConnectedCorrDecay` / `ClusterCorrelatorBound` ← PRIORITY: Phase 5
2. `HasAsymptoticFreedomControl`                   ← Phase 6

### Terminal
- `clay_millennium_yangMills`     ← L8 (compilado, espera active hypotheses)
- `eriksson_phase4_clay_yangMills` ← ClayYangMillsTheorem (compilado;
  audited as vacuous in `L8_Terminal/ClayTrivialityAudit.lean`)
- `clayMassGap_small_beta_of_uniformRpow` ← non-vacuous Clay mass-gap target,
  gated on F3 packages (Phase 5)

---

## Phase 5: Discharge ConnectedCorrDecay / ClusterCorrelatorBound (F3 frontier)

### Reformulated dependency chain (F3 decomposition)

The Phase 5 target is now structured around two named analytic packages.
The combined chain produces `WilsonUniformRpowBound N_c β C` from which
`clayMassGap_small_beta_of_uniformRpow N_c β C : ClayYangMillsMassGap N_c`
follows mechanically.

```
F3-Mayer:  Brydges-Kennedy interpolation gives PhysicalShiftedF3MayerPackage
              with |K(Y)| ≤ A₀ · r^|Y|, r = 4 N_c · β, A₀ = 1
              [BLUEPRINT_F3Mayer.md]
   ⊕
F3-Count:  Klarner BFS-tree gives PhysicalShiftedF3CountPackage (exponential
              frontier `ShiftedConnectingClusterCountBoundExp`)
              with count(n) ≤ C_conn · K^n, K ≤ 2d - 1 = 7 for d = 4
              [BLUEPRINT_F3Count.md]
   ↓
PhysicalShiftedF3MayerCountPackage
   ↓ (KP convergence with constraint r·K < 1, i.e. β < 1/(28 N_c))
ClusterCorrelatorBound N_c r (clusterPrefactorShiftedExp r C_conn A₀)
   ↓
WilsonUniformRpowBound N_c β C
   ↓
clayMassGap_small_beta_of_uniformRpow → ClayYangMillsMassGap N_c
```

### Nodes (current)
- **F5.1** `BLUEPRINT_F3Count.md` (strategy) → `LatticeAnimalCount.lean`
  (witness, ~150 LOC, open) → `ConnectingClusterCountExp.lean` (frontier
  declared, witness open).
- **F5.2** `BLUEPRINT_F3Mayer.md` (strategy) →
  `MayerInterpolation.lean` + `HaarFactorization.lean` +
  `BrydgesKennedyEstimate.lean` + `PhysicalConnectedCardDecayWitness.lean`
  (~600 LOC, open).
- **F5.3** `ClusterRpowBridge.lean` (already in repo, 4264 lines, packaged
  consumers ready) — terminal: explicit packages → `ClusterCorrelatorBound`
  → `ClayYangMillsMassGap N_c`.

### Combined regime constraint
`r · K_count < 1` ⇔ `β < 1 / (28 N_c)`. For physical N_c = 3 (QCD),
`β < 1/84 ≈ 0.012` — the standard weak-coupling cluster-expansion regime.

---

## Phase 6: Discharge HasAsymptoticFreedomControl (UV flow + asymptotic freedom)

### Dependency chain (Papers 86-90, UV-Flow, LSI)
```
b0 = 11N/(48π²) > 0  (asymptotic freedom)
g^-2_{k+1} = g^-2_k + b0 + r_k  (Balaban beta-function recursion)
  ↓
g_k → 0 as k → k_*
  ↓
renormalizedMass m_lat N = m_lat N / a(N) → m_phys
  ↓
HasAsymptoticFreedomControl m_lat
```

### Nodes
- F6.1 `BetaFunction.lean`         — discrete beta-function recursion, g_k ≤ g_0
- F6.2 `CouplingConvergence.lean`  — g_k → 0, renormalized mass convergence
- F6.3 `AsymptoticFreedomDischarge.lean` — terminal: HasAsymptoticFreedomControl

---

## Phase 7: Full assembly (no remaining explicit hypotheses)

### Terminal
```
Phase5: ConnectedCorrDecay
Phase6: HasAsymptoticFreedomControl
  ↓
phase4_continuum_bridge → clay_millennium_yangMills
  ↓
ClayYangMillsTheorem (no remaining sorry, no remaining explicit hypotheses)
```

---

## Build status

`lake build YangMills` succeeds. The non-Experimental Lean tree contains
**zero declared axioms** (verified via `git grep -n -E "^axiom " -- "*.lean"
| grep -v Experimental` returning empty) and **zero live `sorry`** (per
`SORRY_FRONTIER.md`). For the live commit-by-commit progress log see
`AXIOM_FRONTIER.md` (currently at v1.83.0, 2026-04-25). For per-version
release notes see `git log` and the `README.md` "Last closed" field.

## L1/L2 progress bars (per README, oracle-clean closed artifacts)

```
L1    Haar + Schur scaffolding on SU(N)         98 %
L2.4  Structural Schur / Haar scaffolding      100 %
L2.5  Frobenius trace bound  (∑ ∫ |U_ii|² ≤ N) 100 %
L2.6  Character inner product on SU(N)         100 %
L2    Character expansion + cluster decay       50 %
L3    Mass-gap conclusion (with hypotheses)     22 %
                                                ──────
      OVERALL unconditionality                  50 %
```

## Explicit hypotheses remaining
1. `ClusterCorrelatorBound N_c r C` (Phase 5) — gated on F3-Mayer + F3-Count
   packages. See `BLUEPRINT_F3Mayer.md` and `BLUEPRINT_F3Count.md`.
2. `HasAsymptoticFreedomControl` (Phase 6) — unchanged from earlier roadmap;
   route via beta-function recursion is intact.

## External mathematics (declared black boxes)
- Brydges-Kennedy / Battle-Federbush cluster expansion [BK87]
- Klarner / Madras-Slade lattice-animal counting [Klarner67, MS93]
- Kotecky-Preiss polymer convergence [KP86]
- Osterwalder-Schrader reconstruction [OS75]
- Lattice reflection positivity [OS78]
- Balaban CMP primary sources [CMP 116, 119, 122, 109]

## Reclassified out of critical path
- **Peter–Weyl theorem** for compact Lie groups (reclassified 2026-04-22 as
  aspirational / Mathlib-PR; not Clay-blocking via the F3 path which uses
  only the scalar trace subalgebra). See `PETER_WEYL_AUDIT.md` for the
  consumer-driven rationale.

## Companion documents
- `STATE_OF_THE_PROJECT.md` — current snapshot (v1.83.0, 2026-04-25)
- `UNCONDITIONALITY_ROADMAP.md` — version-by-version axiom census
- `BLUEPRINT_F3Count.md` — F3-Count strategy + Resolution C
- `BLUEPRINT_F3Mayer.md` — F3-Mayer strategy + BK estimate
- `MATHLIB_GAPS.md` — upstream PR candidates ordered by value/effort
- `PETER_WEYL_AUDIT.md` — reclassification + downstream deadweight
- `ROADMAP_AUDIT.md` — staleness audit of strategic docs
- `mathlib_pr_drafts/` — concrete PR drafts ready for upstream
