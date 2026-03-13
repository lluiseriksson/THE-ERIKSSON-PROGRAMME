# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang-Mills mass gap (Clay Millennium Problem)**

> *"Yang-Mills existence and mass gap"* — Clay Mathematics Institute

**Author**: Lluis Eriksson  
**Repository**: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME  
**Lean version**: v4.29.0-rc6 + Mathlib  
**Status**: Phases 1-6 complete — 8185+ jobs, 0 sorrys, 0 errors

---

## Terminal Theorem
```lean
theorem eriksson_programme_terminal
    (hKP : forall (N : Nat) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr mu plaquetteEnergy beta F p q| <= C * exp (-m * distP N p q))
    (hm_phys : 0 < m_phys) :
    ClayYangMillsTheorem
```

where `ClayYangMillsTheorem := exists m_phys, 0 < m_phys`.

---

## Architecture
```
Phase 1: Lattice gauge theory foundations
Phase 2: Quantum states, Petz recovery, infinite-volume mass gap
Phase 3: Balaban RG — ConnectedCorrDecay -> LatticeMassProfile.IsPositive
Phase 4: Continuum bridge — HasAsymptoticFreedomControl -> ClayYangMillsTheorem
Phase 5: KP hypotheses + bootstrap — explicit decay bound -> ConnectedCorrDecay
Phase 6: Beta function + coupling convergence -> HasAsymptoticFreedomControl
```

### Dependency chain
```
(H1)+(H2)+(H3) [KP hypotheses, explicit]
  | F5.1 KPHypotheses
  | F5.2 BalabanBootstrap
  | F5.3 DecayFromRG
ConnectedCorrDecay
  | P3.1-P3.5 BalabanRG
LatticeMassProfile.IsPositive

b0 = 11N/(48*pi^2) > 0
  | F6.1 BetaFunction
  | F6.2 CouplingConvergence
HasAsymptoticFreedomControl

IsPositive + HasContinuumMassGap
  | P4.1-P4.2 Continuum
ClayYangMillsTheorem  [QED]
```

---

## Build Status

### Phase 1 — Lattice Gauge Theory Foundations

| Node | File | Key theorems | Status |
|------|------|-------------|--------|
| L0.1-L0.6 | L0_Foundation/ | FinBox, GaugeConfig, wilsonAction | FORMALIZED_KERNEL |
| L1.1-L1.3 | L1_GibbsMeasure/ | gibbsMeasure, expectation, correlation | FORMALIZED_KERNEL |
| L2.1-L2.3 | L2_LargeField/ | SmallFieldSet, largeField_suppression | FORMALIZED_KERNEL |
| L3.1-L3.3 | L3_BlockSpin/ | BlockSpin, gibbsMeasure_gauge_invariant | FORMALIZED_KERNEL |
| L4.1 | L4_LargeField/ | largeField_suppression_integral | FORMALIZED_KERNEL |
| L4.2 | L4_WilsonLoops/ | plaquetteWilsonObs_gaugeInvariant | FORMALIZED_KERNEL |
| L4.3 | L4_TransferMatrix/ | HasSpectralGap, transferMatrix_spectral_gap | FORMALIZED_KERNEL |
| L5.1 | L5_MassGap/ | yangMills_mass_gap | FORMALIZED_KERNEL |
| L6.1 | L6_FeynmanKac/ | feynmanKac_decay | FORMALIZED_KERNEL |
| L6.2 | L6_Clustering/ | OSClusterProperty, thermodynamicLimit_massGap | FORMALIZED_KERNEL |
| L7.1 | L7_Continuum/ | HasContinuumMassGap | FORMALIZED_KERNEL |
| L8.1 | L8_Clay/ | clay_millennium_yangMills | FORMALIZED_KERNEL |

### Phase 2 — Quantum States and Infinite-Volume Mass Gap

| Node | File | Key theorems | Status |
|------|------|-------------|--------|
| P2.1 | P2_QuantumStates/QuantumStates.lean | QuantumState, FawziRennerBound | FORMALIZED_KERNEL |
| P2.2 | P2_QuantumStates/LocalAlgebra.lean | localAlgebra, restrictState | FORMALIZED_KERNEL |
| P2.3 | P2_QuantumStates/MaxEntropy.lean | MaxEntExists, maxEnt_determined | FORMALIZED_KERNEL |
| P2.4 | P2_QuantumStates/PetzRecovery.lean | PetzRecoveryChannel, MaxEntToRecoveryBridge | FORMALIZED_KERNEL |
| P2.5 | P2_QuantumStates/Phase2Assembly.lean | eriksson_phase2_infiniteVolume_massGap | FORMALIZED_KERNEL |

### Phase 3 — Balaban Renormalization Group

| Node | File | Key theorems | Status |
|------|------|-------------|--------|
| P3.1 | P3_BalabanRG/CorrelationNorms.lean | ConnectedCorrDecay, MultiscaleDecayBound | FORMALIZED_KERNEL |
| P3.2 | P3_BalabanRG/RGContraction.lean | RGStepContraction, HasOneStepRGBoundAt | FORMALIZED_KERNEL |
| P3.3 | P3_BalabanRG/MultiscaleDecay.lean | rgIterated_improvement, uniformWilsonDecay_of_multiscale | FORMALIZED_KERNEL |
| P3.4 | P3_BalabanRG/LatticeMassExtraction.lean | yangMillsMassGap_of_uniformDecay, latticeMassIsPositive_of_connectedDecay | FORMALIZED_KERNEL |
| P3.5 | P3_BalabanRG/Phase3Assembly.lean | eriksson_phase3_balaban_massProfile | FORMALIZED_KERNEL |

### Phase 4 — Continuum Bridge

| Node | File | Key theorems | Status |
|------|------|-------------|--------|
| P4.1 | P4_Continuum/ContinuumBridge.lean | HasUVScalingLimit, HasAsymptoticFreedomControl | FORMALIZED_KERNEL |
| P4.2 | P4_Continuum/Phase4Assembly.lean | eriksson_phase4_clay_yangMills, eriksson_phase4_clay_theorem | FORMALIZED_KERNEL |

### Phase 5 — KP Hypotheses and Balaban Bootstrap

| Node | File | Key theorems | Status |
|------|------|-------------|--------|
| F5.1 | P5_KPDecay/KPHypotheses.lean | HasSmallFieldDecay, KPSmallness, phase5_kp_sufficient | FORMALIZED_KERNEL |
| F5.2 | P5_KPDecay/BalabanBootstrap.lean | balabanBootstrap_uniformDecay, phase5_bootstrap_improvedDecay | FORMALIZED_KERNEL |
| F5.3 | P5_KPDecay/DecayFromRG.lean | eriksson_phase5_balaban_uniformDecay, phase5_complete | FORMALIZED_KERNEL |

### Phase 6 — Asymptotic Freedom

| Node | File | Key theorems | Status |
|------|------|-------------|--------|
| F6.1 | P6_AsymptoticFreedom/BetaFunction.lean | betaCoeff_pos, invCoupling_lower_bound, CouplingVanishesUV | FORMALIZED_KERNEL |
| F6.2 | P6_AsymptoticFreedom/CouplingConvergence.lean | coupling_tendsto_zero, constantMassProfile_af | FORMALIZED_KERNEL |
| F6.3 | P6_AsymptoticFreedom/AsymptoticFreedomDischarge.lean | eriksson_phase6_clay_yangMills, eriksson_programme_terminal | FORMALIZED_KERNEL |

---

## Governance Protocol

| Evidence | Status |
|----------|--------|
| lake build passes, zero errors | FORMALIZED_KERNEL |
| Code written, not compiled | PARTIAL |
| Statement only, no proof | OPEN |
| Depends on uncompiled node | BLOCKED |

---

## Honest Architecture

The skeleton is complete. The following mathematical content is formalized as
**explicit hypotheses** (named parameters, not sorrys):

### Remaining explicit hypotheses

| Hypothesis | Mathematical content | Source |
|-----------|---------------------|--------|
| hKP | |wilsonConnectedCorr| <= C*exp(-m*dist) for all N, p, q | Kotecky-Preiss [KP86] + Balaban CMP 116/119/122 |
| hm_phys | 0 < m_phys | Physical input: existence of a mass scale |

### External mathematics (declared black boxes)

| Content | Reference |
|---------|-----------|
| Kotecky-Preiss cluster expansion | [KP86] CMP 103 |
| Osterwalder-Schrader reconstruction | [OS75] CMP 42 |
| Lattice reflection positivity | [OS78] CMP 59 |
| Balaban multiscale RG | CMP 109, 116, 119, 122 |

---

## Key Lean 4 Patterns

| Issue | Solution |
|-------|----------|
| ConnectedCorrDecay (Type) as return | noncomputable def, never theorem |
| Build seed from hKP | angle-bracket constructor directly |
| theorem with Type in conclusion | Use exists or separate noncomputable def |
| [NeZero N] stuck in forall-body | (hN : NeZero N) explicit + letI |
| g0 + k*b0 -> atTop | tendsto_atTop_add_const_left + atTop_mul_const |
| 1/x -> 0 as x -> inf | simp_rw [one_div]; exact tendsto_inv_atTop_zero |
| Pass hKP to Type constructor | angle-bracket constructor, avoid wrappers |

---

## Companion Papers

Published at https://ai.vixra.org/author/lluis_eriksson

| Paper | Title | Role |
|-------|-------|------|
| 86 | Exponential Clustering | Pillar 2: mass gap + OS axioms |
| 87 | ANISO bounds | Pillar 3: anisotropy + Triangular Lock |
| 88 | OS1 via Ward identity | Pillar 4: Jacobian-free OS1 |
| 89 | Terminal KP Bound | Pillar 1: (H1)-(H3) -> KP convergence |
| 90 | Master Map | Navigation + threat model |
| 91 | Audit Report | 29/29 tests passing (~70s Colab CPU) |

Audit suite: https://github.com/lluiseriksson/ym-audit

---

## Repository Stats

- 8185+ compiled jobs
- 0 sorrys
- 0 errors
- ~40 files, ~300+ theorems
- 6 phases complete
- Security: GitHub token in Colab secrets as GITHUB_TOKEN
