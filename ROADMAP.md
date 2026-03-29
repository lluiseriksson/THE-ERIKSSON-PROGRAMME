# THE ERIKSSON PROGRAMME — ROADMAP
## Estado: 2026-03-13

## Arquitectura formal completa

### Explicit discharged hypotheses (Phases 1-4)
- `LatticeMassProfile.IsPositive`   ← Phase 3 (Balaban RG)
- `∃ m_inf : ℝ, 0 < m_inf`         ← Phase 2 (MaxEnt + Petz + Fawzi-Renner)
- `HasContinuumMassGap` (interfaz)  ← Phase 4 (UV scaling limit)

### Active explicit hypotheses
1. `ConnectedCorrDecay`           ← PRIORITY: Phase 5
2. `HasAsymptoticFreedomControl`  ← Phase 6

### Terminal
- `clay_millennium_yangMills`     ← L8 (compilado, espera active hypotheses)
- `eriksson_phase4_clay_yangMills` ← ClayYangMillsTheorem (compilado)

---

## Phase 5: Discharge ConnectedCorrDecay (Balaban RG + KP)

### Dependency chain (Papers 86-89)
```
(H1) Small-field: ||R^sf_*(X)||_∞ ≤ E0 g²_bar exp(-κ d(X))   [Balaban CMP 116, Lem. 3]
(H2) Large-field: ||R^lf_*(X)||_∞ ≤ exp(-p0(g)) exp(-κ d(X)) [Balaban CMP 122, Eq. 1.98-1.100]
(H3) Local dependence / hard-core                               [Balaban CMP 116, CMP 122]
  ↓ KP convergence (Kotecky-Preiss)
Terminal clustering: |Cov_μ(O(0),O(x))| ≤ C exp(-m|x|/a_*)
  ↓
ConnectedCorrDecay μ pe β F distP
```

### Nodes
- F5.1 `KPHypotheses.lean`      — (H1)-(H3) as formal predicates + KP sufficient criterion
- F5.2 `BalabanBootstrap.lean`  — RGStepContraction + seed decay → iterated decay
- F5.3 `DecayFromRG.lean`       — terminal: explicit hypotheses → ConnectedCorrDecay

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

## Build status (all FORMALIZED_KERNEL)

| Node | Commit | Terminal theorem |
|------|--------|-----------------|
| L0-L8.1 | 529ec9f | clay_millennium_yangMills |
| P2.1-P2.5 | 7ed016a | eriksson_phase2_infiniteVolume_massGap |
| P3.1-P3.5 | cb64793 | eriksson_phase3_balaban_massProfile |
| P4.1-P4.2 | 6261867 | eriksson_phase4_clay_yangMills |

## Explicit hypotheses remaining
1. ConnectedCorrDecay (Phase 5)
2. HasAsymptoticFreedomControl (Phase 6)

## External mathematics (declared black boxes)
- Kotecky-Preiss cluster expansion [KP86]
- Osterwalder-Schrader reconstruction [OS75]  
- Lattice reflection positivity [OS78]
- Balaban CMP primary sources [CMP 116, 119, 122, 109]
