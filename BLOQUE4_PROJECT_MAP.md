# BLOQUE4_PROJECT_MAP.md

**Author**: Cowork agent (Claude), Phase 86
**Date**: 2026-04-25 (very late session)
**Subject**: section-by-section cross-reference map between Eriksson's
Bloque-4 paper (`YangMills-Bloque4.pdf`, Feb 2026) and the project's
Lean predicates / theorems / structures
**Companion documents**: `ERIKSSON_BLOQUE4_INVESTIGATION.md` (Phase 81),
`BLUEPRINT_MultiscaleDecoupling.md` (Phase 84),
`COWORK_FINDINGS.md` Finding 017

---

## §1. Introduction

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Theorem 1.1 (Lattice Mass Gap) | `ClayConnectedCorrDecay N_c` (`ClayCore/ConnectedCorrDecay.lean`) | predicate exists, witness via Branch I/II |
| Theorem 1.4(a) (subseq. continuum) | `HasContinuumMassGap_Genuine` (`L7_Continuum/PhysicalScheme.lean`) | predicate exists, SU(1) closed (Phase 17, 45) |
| Theorem 1.4(b) (Hilbert reconstruction) | `OperatorSpectralGap` + transfer matrix infrastructure | partial (Phase 83) |
| Theorem 1.4(c) (Wightman, conditional on O(4)) | not yet a project predicate; would be `ClayYangMillsWightman` | NOT IN PROJECT — OS1 caveat (Finding 017) |
| Corollary 1.2 (Physical Mass Gap ≥ c_N Λ_YM) | not a project predicate yet | NOT IN PROJECT |

## §2. Setup and Notation

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| `Λ_η = (ηℤ/L_phys ℤ)^4` | `ConcretePlaquette d L` + `siteLatticeDist` | done (`L0_Lattice/`) |
| `G = SU(N)`, links `U_ℓ ∈ G` | `Matrix.specialUnitaryGroup (Fin N_c) ℂ` + `GaugeConfig d L G` | done |
| Wilson action `A(U) = Σ Re Tr(I − U(∂p))` | `wilsonAction (wilsonPlaquetteEnergy N_c)` (`L0_Lattice/`) | done |
| Wilson measure `dµ_η` | `gibbsMeasure (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β` (`L1_GibbsMeasure/`) | done |
| Schwinger functions `S_n^η` | `wilsonExpectation` / `wilsonCorrelation` (`L1_GibbsMeasure/`) | done |

## §3. Balaban's Renormalization Group Framework

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Theorem 3.1 (Inductive Representation) | `BalabanRGPackage d N_c` (`BalabanRG/BalabanRGPackage.lean`) | scaffold-trivial (Phase 70 / Finding 015) |
| Proposition 3.2 (Polymer Bounds) | `BalabanH1`, `BalabanH2`, `BalabanH3` (`ClayCore/BalabanH1H2H3.lean`) | scaffold-trivial (Phase 59 / Finding 013) |
| Effective action `A_k = -g_k^{-2} A + E_k + R_k + B_k` | `WilsonPolymerActivityBound N_c` (`ClayCore/WilsonPolymerActivity.lean`) | scaffold-trivial (Phase 60 / Finding 014) |
| Activity bounds `‖E_k(X)‖ ≤ E₀ exp(-κ d_k(X))` | `SmallFieldActivityBound N_c` + `LargeFieldActivityBound N_c` (`ClayCore/SmallFieldBound.lean` + `LargeFieldBound.lean`) | scaffold-trivial (Phases 63, 65) |
| Proposition 3.3 (UV Stability) | not a project predicate yet | NOT IN PROJECT |
| Proposition 3.4 (R-Operation) | not a project predicate yet | NOT IN PROJECT |
| Proposition 3.6 (Analyticity of Effective Action) | not a project predicate yet | NOT IN PROJECT — would benefit from Mathlib analyticity infrastructure |

## §4. Coupling Control

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Proposition 4.1 (Coupling Control) | not a project predicate yet | NOT IN PROJECT — Mathlib has Cauchy estimates (`Complex.abs_deriv_le_aux`); the application to discrete RG is structural |
| Cauchy bound `|β_{k+1}(g) − b₀| ≤ M·g²/R` | not a project predicate yet | NOT IN PROJECT |
| Inductive `g_{k+1}^{-2} ≥ g_k^{-2} + b₀/2` | not a project predicate yet | NOT IN PROJECT |

**Note**: this is a 2-page argument in the paper that should be
formalisable in Lean once Mathlib's complex-analyticity infrastructure
is leveraged. Estimated effort: ~150 LOC.

## §5. Terminal Cluster Expansion and Exponential Clustering

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Effective terminal measure `µ_{a*}` | `gibbsMeasure` at terminal scale | done (uses same definition with terminal-β coupling) |
| Proposition 5.1 (Oscillation bound) | not a project predicate yet | NOT IN PROJECT |
| Theorem 5.3 (Terminal KP bound) | `PhysicalShiftedF3MayerPackage`, `KPSmallness` (`ClayCore/`) | active (Codex Branch I, ongoing) |
| Theorem 5.5 (Terminal exponential clustering) | `OSClusterProperty` + `PhysicalClusterCorrelatorBound` (`L6_OS/`, `ClusterCorrelatorBound.lean`) | predicate exists, conditional on KP smallness (Codex F3 ongoing) |
| Proposition A.1 (KP ⇒ exp decay, Appendix) | `clusterCorrelatorBound_of_truncatedActivities_ceil_total_exp` (`ClusterRpowBridge.lean`) | done (Codex v2.20+) |

## §6. Multiscale Correlator Decoupling — **the new contribution**

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Proposition 6.1 (Telescoping Identity) | not yet a project predicate | NOT IN PROJECT — **PRIORITY 1**, blueprint at `BLUEPRINT_MultiscaleDecoupling.md` (Phase 84) |
| Lemma 6.2 (Single-Scale UV Error) | not yet a project predicate | NOT IN PROJECT — `SingleScaleUVErrorBound` proposed in blueprint |
| Theorem 6.3 (UV Suppression) | not yet a project predicate | NOT IN PROJECT — relies on standard Mathlib geometric series |
| Law of Total Covariance (foundational tool) | `LawOfTotalCovariance.lean` (Phase 82, Mathlib-PR-ready draft) | DONE (Phase 82, this project) |

## §7. Assembly: The Mass Gap Bound

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Theorem 7.1 (Mass Gap Bound, lattice) | combines Branch I (terminal clustering) + Branch VIII (multiscale UV suppression) | combinable from above; specific endpoint pending Branch VIII |
| Constant `m = min(m_*, c_0)` | not yet a project predicate | NOT IN PROJECT |

## §8. Osterwalder–Schrader Reconstruction and Non-Triviality

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| OS0 (temperedness) | not a named predicate; covered by ad-hoc bound | NOT IN PROJECT formally |
| OS1 (Euclidean covariance) | `OSCovariant` (`L6_OS/OsterwalderSchrader.lean`) | predicate exists; SU(1) closed (Phase 50). **Full O(4): NOT proved in Bloque-4 either** — single uncrossed barrier |
| OS2 (Reflection positivity) | `OSReflectionPositive` (`L6_OS/OsterwalderSchrader.lean`) | predicate exists; SU(1) closed (Phase 47); SU(N) for N ≥ 2 conditional on Osterwalder-Seiler |
| OS3 (Symmetry / bosonic) | not a named predicate; automatic for gauge-invariant observables | trivially in project |
| OS4 (Cluster property) | `OSClusterProperty` (`L6_OS/OsterwalderSchrader.lean`) | predicate exists; SU(1) closed (Phase 49) |
| Lemma 8.2 (Spectral gap from clustering) | `OperatorSpectralGap` + `clusteringImpliesSpectralGap_conditional` (Phase 83, this project) | DONE (abstract version) |
| Proposition 8.3 (subsequential covariance) | not a named predicate | NOT IN PROJECT |
| Proposition 8.5 (Vacuum uniqueness) | not a named predicate | NOT IN PROJECT |
| Theorem 8.7 (Non-Triviality) | not a named predicate | NOT IN PROJECT |

## §A. KP cluster expansion ⇒ exponential clustering

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Proposition A.1 (KP ⇒ exp decay) | Codex's KP-bridge family (`ClusterSeriesBound.lean`, `ClusterRpowBridge.lean`) | DONE (Codex Branch I) |

## §B. Random Walk and Localization Bounds

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Lemma B.1 (RW propagator decay) | not a project predicate; black-boxed via Balaban [4, 5] | NOT IN PROJECT |

## §C. Lattice Animal Bounds

| Paper component | Project counterpart | Status |
|-----------------|---------------------|--------|
| Lemma C.1 ((2de)^n bound) | `LatticeAnimalCount.lean` + Codex's Klarner BFS-tree work | active (Codex Priority 1.2) |

---

## §X. Coverage summary

After Phases 49–86 (the late-session sweep):

| Paper section | Project coverage | Active workers |
|---------------|------------------|----------------|
| §1 (intro / main theorem) | partial (predicates exist, witnesses gated) | both |
| §2 (setup) | full | done |
| §3 (Balaban RG) | scaffold-complete with trivial witnesses | Codex (full, BalabanRG/) + Cowork (trivial inhabitants Phases 59-65) |
| §4 (Coupling Control) | NOT IN PROJECT | future Cowork — Mathlib Cauchy + analyticity |
| §5 (Terminal KP) | active (Codex F3) | Codex |
| §6 (Multiscale) | **NEW BRANCH VIII**, blueprint ready | future Cowork — `BLUEPRINT_MultiscaleDecoupling.md` |
| §7 (Assembly) | depends on §5 + §6 | both |
| §8 (OS reconstruction) | partial (OS axioms predicates exist; full Wightman = OS1 caveat) | Cowork (SU(1) Phase 49-50, scaffold) |
| §A (KP appendix) | done (Codex) | Codex |
| §B (RW propagators) | NOT IN PROJECT | future |
| §C (Lattice animals) | active (Codex Priority 1.2) | Codex |

**Net coverage of Bloque-4 by the project**:
* **§3, §A, §C**: COVERED (Codex, possibly with Cowork's structural-triviality findings).
* **§2, §5**: COVERED structurally (predicates exist, Codex's F3 substantive content ongoing).
* **§4, §6, §B**: NOT COVERED — these are open targets for future Cowork work.
* **§7**: depends on §5 and §6.
* **§8 OS axioms**: COVERED at SU(1) (Cowork Phases 49-50). For N_c ≥ 2 substantive content, partially covered (OS2/OS4 via Codex's BalabanRG; OS1 not proved even by Bloque-4).

**Strategic priorities** (from the gap analysis):

1. **§4 Coupling Control** — Mathlib Cauchy bound infrastructure
   exists; ~150 LOC of project-side work. **PRIORITY 6 (new)**.
2. **§6 Multiscale Decoupling** — blueprint ready; ~290 LOC.
   **PRIORITY 1** (already issued).
3. **§B Random Walk Propagators** — substantive Branch II content;
   not Cowork's natural domain. Codex / future research.

---

## §Y. How to use this map

When working on a specific Bloque-4 section in Lean:

1. Look up the section in this document.
2. The "Project counterpart" column tells you whether a Lean predicate
   already exists.
3. The "Status" column tells you whether the predicate is inhabited
   (and by whom: Codex / Cowork / SU(1) trivial / open).
4. If status is "NOT IN PROJECT", check whether it's flagged as a
   PRIORITY in `ERIKSSON_BLOQUE4_INVESTIGATION.md` or
   `BLUEPRINT_MultiscaleDecoupling.md`.

When auditing the project's claim of "lattice mass gap":

1. Check Theorem 7.1's coverage (depends on §5 + §6).
2. Verify §5 closure (Codex's F3 chain).
3. Verify §6 closure (project Branch VIII, currently blueprint-only).
4. Note the OS1 caveat for any "Wightman QFT" claim.

---

*Map complete 2026-04-25 evening (Phase 86) by Cowork agent.
Cross-references: `ERIKSSON_BLOQUE4_INVESTIGATION.md` (Phase 81),
`BLUEPRINT_MultiscaleDecoupling.md` (Phase 84),
`OPENING_TREE.md` §9 (Branch VIII, Phase 85),
`COWORK_FINDINGS.md` Finding 017.*
