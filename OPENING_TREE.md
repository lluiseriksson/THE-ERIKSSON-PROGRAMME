# OPENING_TREE.md — Cowork strategy for Clay-Millennium-grade Yang–Mills

**Author**: Cowork agent (Claude), strategic master plan 2026-04-25
**Subject**: parallel mathematical strategies toward an unconditional
Clay-grade closure of Yang–Mills, complementary to Codex's current
F3-Count work
**Audience**: Lluis (project lead), future Cowork agents, anyone
evaluating the project's full attack surface

---

## 0. Premise (per Lluis, 2026-04-25)

> "Bajo la premisa de conseguir Yang-Mills incondicional en sentido
> Clay, márcate plan, pasos a seguir, y empieza a ejecutar sin pisar
> el trabajo a Codex. ... Desarrolla una especie de árbol de
> aperturas, donde vas probando jugadas para descubrir matemática
> nueva y dar jaque mate al problema."

This document is the **master plan** for the Cowork agent's parallel
work. It treats the Clay problem like a chess game: enumerate
opening branches, evaluate each, commit to lines of attack,
prepare moves in advance.

**Codex's main line** (the F3 cluster expansion) is documented in
`BLUEPRINT_F3Count.md` and `BLUEPRINT_F3Mayer.md`. **My role** is to
develop **parallel branches** that Codex isn't (yet) attacking,
with the long-term goal of completing the Clay statement when all
branches converge.

---

## 1. The actual Clay target — full statement

Per Jaffe & Witten (2000), the Clay Millennium problem requires:

1. **Existence**: Construction of a quantum Yang–Mills theory on
   ℝ⁴ with gauge group SU(N) (canonically N = 3).
2. **Wightman axioms** (or equivalently OS axioms in the Euclidean
   framework): the constructed theory must satisfy the standard
   Wightman / Osterwalder–Schrader reconstruction axioms.
3. **Mass gap**: positive infimum of the spectrum of the
   Hamiltonian above zero.

Equivalently in the Euclidean setting:
- Construct Euclidean correlation functions on ℝ⁴
- Satisfying OS axioms (regularity, Euclidean invariance,
  reflection positivity, symmetry, cluster property)
- With exponential clustering at strictly positive rate

**What the project currently has** (after the F3 chain closes):
- A lattice mass gap at small β.
- An algebraic continuum predicate `HasContinuumMassGap` that is
  satisfied via a coordinated scaling trick (Finding 004), NOT
  via genuine continuum analysis.

**Gap from current to Clay**:
- A. Extend lattice mass gap from "small β" to "all physical β"
  (or at least β past deconfinement for the relevant N).
- B. Take genuine continuum limit a → 0 with proper RG running.
- C. Verify OS / Wightman axioms in the continuum.

Codex is working on a sub-piece of A (the small-β lattice mass
gap). My role is to develop the strategy for B and C, plus
alternative strategies for A.

---

## 2. The opening tree — 7 candidate branches

Each branch is a distinct mathematical strategy. For each: name,
status, mathematical content, known references, expected difficulty,
recommended action.

### Branch I — F3 cluster expansion (Codex's main line)

- **Strategy**: Brydges–Kennedy / Klarner cluster expansion at
  small β. Yields lattice mass gap at small β.
- **Status**: Codex actively working (Priority 1.2 = LatticeAnimalCount,
  ~70% complete; Priority 2.x = F3-Mayer, not started).
- **References**: Brydges-Kennedy 1987, Kotecký-Preiss 1986,
  Osterwalder-Seiler 1978, Klarner 1967.
- **Expected closure**: 1-3 weeks (small-β lattice mass gap).
- **Sufficient for Clay?**: **NO**. Only gives small-β; no
  continuum limit; no OS verification.
- **Recommended action**: continue Codex's path. Cowork should not
  duplicate.

### Branch II — Bałaban renormalisation group (the historical Clay candidate)

- **Strategy**: Multi-scale RG with large-field/small-field
  decomposition. Inductive control of the RG flow over scales,
  yielding uniform-in-a lattice mass gap that survives the
  continuum limit. **This is the closest known approach to Clay**.
- **Status**: Project has skeletal infrastructure:
  `YangMills/P3_BalabanRG/`, `YangMills/ClayCore/BalabanRG/` (~50
  files). Many declared axioms. The hardest step (the inductive
  RG step) is not closed.
- **References**: Bałaban CMP 109 (1986), 116 (1987), 119 (1988),
  122 (1989), 167 (1995); Magnen-Rivasseau-Sénéor (1993).
- **Expected difficulty**: extreme. Bałaban's series is ~500
  pages of analysis. Formalising even a single inductive step
  would be on the order of `BrydgesKennedyEstimate.lean` ×10.
- **Sufficient for Clay?**: **MAYBE**. Bałaban himself argued his
  framework completes the Clay statement modulo standard
  reconstruction. Critics (e.g. Jaffe) note open issues at the
  large-field control step.
- **Recommended action**: develop blueprint
  `BLUEPRINT_BalabanRG.md` for the inductive step. Identify
  which existing project axioms can be retired and which are
  still needed. **Most strategically important parallel
  branch.**

### Branch III — Reflection positivity + transfer matrix

- **Strategy**: Prove reflection positivity (RP) of the lattice
  Wilson-Gibbs measure. Then the transfer matrix is positive and
  has a Hilbert-space interpretation. Spectral gap of the
  transfer matrix gives the mass gap.
- **Status**: Project has `YangMills/L4_TransferMatrix/` and
  `YangMills/L6_OS/OsterwalderSchrader.lean` as stubs. RP for
  Wilson SU(N) Gibbs is **classical** (Osterwalder-Seiler 1978
  prove it).
- **References**: Osterwalder-Seiler 1978, Seiler 1982 ch. 5,
  Glimm-Jaffe ch. 6.
- **Expected difficulty**: medium-high. RP itself is provable.
  Spectral gap of transfer matrix needs spectral analysis of a
  positive trace-class operator on L²(SU(N)^edges).
- **Sufficient for Clay?**: **PARTIAL**. RP + spectral gap give
  lattice mass gap; need to combine with Branch II for continuum
  limit.
- **Recommended action**: develop blueprint
  `BLUEPRINT_ReflectionPositivity.md`. Lower mathematical
  difficulty than Branch II; partial path forward.

### Branch IV — Stochastic quantization (Parisi-Wu / Hairer-style)

- **Strategy**: Construct YM measure as stationary distribution
  of stochastic PDE (Langevin-type) on the loop space. Use
  Hairer's regularity-structures (or paracontrolled calculus) to
  make sense of the SPDE in d = 4.
- **Status**: Not in the project. Hairer's work on Φ⁴_3 (2014)
  and on YM in 2D (Chevyrev 2019, Chandra-Chevyrev-Hairer-Shen
  2022) shows the strategy works in lower dimensions. **The
  4D YM case is open in this approach too**.
- **References**: Parisi-Wu 1981 (original), Hairer 2014
  (regularity structures), CCHS 2022 (2D stochastic YM).
- **Expected difficulty**: extreme. Hairer's 2D YM construction
  is ~100 pages of advanced analysis; 4D scaling makes it
  significantly harder.
- **Sufficient for Clay?**: **YES** in principle, IF the
  construction works in d=4 (open problem in math physics).
- **Recommended action**: defer. Too speculative for current
  phase. Note the strategy exists; revisit if 4D stochastic YM
  becomes literature-rigorous.

### Branch V — Direct constructive (Glimm-Jaffe / polymer gas)

- **Strategy**: Construct the YM measure directly in continuum
  via polymer-gas representation. Verify OS axioms term-by-term.
  This is the original 1970s constructive QFT program.
- **Status**: Not currently in project beyond the stubs in
  `L6_OS`. Worked for Φ²_2, Φ⁴_2, Φ⁴_3 (Glimm-Jaffe). YM has
  never been done this way.
- **References**: Glimm-Jaffe (multiple monographs), Magnen-Sénéor
  (1976) for related work.
- **Expected difficulty**: extreme. The YM measure in continuum
  is ill-defined without a regulator; constructing it directly
  bypasses the lattice approach.
- **Sufficient for Clay?**: **YES** if the construction works.
- **Recommended action**: defer. Equivalent in difficulty to
  Branch II but less mature in the mathematical literature.

### Branch VI — Asymptotic freedom + RG bootstrap

- **Strategy**: Use asymptotic freedom (g → 0 at high energy /
  small a) to argue that the RG flow is in the perturbative
  regime at small lattice spacing. Combine with cluster
  expansion at small g to get continuum mass gap.
- **Status**: Project has `YangMills/P6_AsymptoticFreedom/` (3
  files). The β-function recursion (one-loop b₀ = 11N/(48π²) > 0
  for SU(N)) is partly formalised.
- **References**: Wilson 1971-1974 (lattice gauge theory + RG),
  Bałaban CMP 122 (1989).
- **Expected difficulty**: high. The one-loop AF is provable;
  the rigorous extension to a full RG flow with mass-gap
  preservation is part of Branch II.
- **Sufficient for Clay?**: **NO** standalone — provides the
  scaling but not the OS reconstruction.
- **Recommended action**: develop alongside Branch II (they're
  intertwined).

### Branch VII — Continuum limit specifically (genuine HasContinuumMassGap)

- **Strategy**: Replace the project's coordinated-scaling
  `HasContinuumMassGap` (Finding 004) with a genuine continuum
  predicate using a physical lattice-spacing scheme (per
  `GENUINE_CONTINUUM_DESIGN.md`). Provide the reconstruction
  framework that any of Branches II, V, VI feed into.
- **Status**: design spec exists (`GENUINE_CONTINUUM_DESIGN.md`),
  no Lean code. Option C of Finding 004 was deferred.
- **References**: Osterwalder-Schrader 1973-1975, Glimm-Jaffe
  ch. 6.
- **Expected difficulty**: medium. Mainly definitional + a few
  reconstruction theorems. Mathlib has measure-theory support
  but no OS-reconstruction-specific machinery.
- **Sufficient for Clay?**: **NO** standalone — provides the
  framework into which lattice work plugs.
- **Recommended action**: **execute now**. This is the most
  tractable parallel work and complements every other branch.

---

## 3. Cowork's selected lines of attack

After analysis, the recommended Cowork branches in priority
order:

1. **Branch VII (continuum limit framework)** — start now.
   Lowest mathematical difficulty, highest leverage (every other
   branch outputs into it). Addresses Finding 004 directly.
   Estimated: ~600 LOC across 2-3 new files.

2. **Branch III (reflection positivity)** — second priority.
   Classical mathematics (RP for SU(N) Wilson is well-known),
   complements Codex's small-β work by giving an independent
   path to mass gap.
   Estimated: ~800 LOC across 3-4 new files.

3. **Branch II (Bałaban RG)** — long-horizon. Most strategically
   important. Cowork can produce strategic blueprint and identify
   the inductive-step content; full formalisation will take many
   sessions.

Branches I, IV, V, VI either belong to Codex (I) or are deferred
(IV, V, VI).

---

## 4. Files Cowork will create (without colliding with Codex)

Codex's active area: `YangMills/ClayCore/LatticeAnimalCount.lean`.
Cowork commits to **NOT** touch:
- `YangMills/ClayCore/LatticeAnimalCount.lean`
- `YangMills/ClayCore/MayerInterpolation.lean` (when created)
- `YangMills/ClayCore/HaarFactorization.lean` (when created)
- `YangMills/ClayCore/BrydgesKennedyEstimate.lean` (when created)
- `YangMills/ClayCore/PhysicalConnectedCardDecayWitness.lean`
  (when created)

Cowork will work in:
- `YangMills/L7_Continuum/` (Branch VII — extend
  `ContinuumLimit.lean`, add new files)
- `YangMills/L6_OS/` (Branch III — extend
  `OsterwalderSchrader.lean`, add new files)
- `YangMills/L4_TransferMatrix/` (Branch III — extend the stub)
- `YangMills/P3_BalabanRG/` (Branch II — strategic
  blueprints + scaffold, no full proofs)

Strategic blueprints (markdown, repo root):
- `BLUEPRINT_ContinuumLimit.md` (Branch VII strategy)
- `BLUEPRINT_ReflectionPositivity.md` (Branch III strategy)
- `BLUEPRINT_BalabanRG.md` (Branch II strategy)

---

## 5. The chess-opening analogy made precise

Like chess opening preparation:

- **Branch I (F3)** is the main line being played by Codex —
  well-known, well-prepared, mostly forced moves.
- **Branch VII (continuum framework)** is a quiet positional
  move — low risk, high value if played early.
- **Branch III (RP + transfer)** is a tactical sideline — known
  classical pattern, can deliver mass gap by a different route.
- **Branch II (Bałaban RG)** is the deep theoretical preparation
  — like preparing a novelty in a closed Sicilian, costly but
  potentially decisive.
- **Branches IV, V, VI** are speculative variations — kept in
  the prep file for future, not played in this game.

The "checkmate" is the convergence of:
- Lattice mass gap at small β (Branch I, Codex)
- Reflection positivity (Branch III, Cowork)
- Transfer matrix spectral gap (Branch III, Cowork)
- Continuum limit framework (Branch VII, Cowork)
- Bałaban RG control across scales (Branch II, future)

When all four converge, the Clay statement closes.

---

## 6. Move order (concrete next actions)

Phase 1 (this session):
1. **Write `BLUEPRINT_ContinuumLimit.md`** (~400 lines).
   Strategic blueprint for Branch VII.
2. **Write `BLUEPRINT_ReflectionPositivity.md`** (~400 lines).
   Strategic blueprint for Branch III.
3. **Start `YangMills/L7_Continuum/PhysicalScheme.lean`**
   (~150 LOC scaffold). Implements `PhysicalLatticeScheme`
   structure from `GENUINE_CONTINUUM_DESIGN.md`. Predicates +
   sorries + `#print axioms`.

Phase 2 (next sessions):
4. Write `BLUEPRINT_BalabanRG.md`.
5. Continue Branch VII Lean scaffold.
6. Start Branch III Lean scaffold (extend
   `YangMills/L6_OS/OsterwalderSchrader.lean`).

Phase 3 (longer horizon):
7. Convergence analysis: how do the branches combine?
8. Open Mathlib PRs for any infrastructure gaps (extend
   `MATHLIB_GAPS.md`).
9. Audit cycle: like the F3 audit cycles, but for the parallel
   branches.

---

## 7. Coordination with Codex

The autonomous Codex daemon will continue executing
`CODEX_CONSTRAINT_CONTRACT.md` priority queue (Priority 1.2 →
2.x → 3.x → 4.x). The new Cowork branches **do not change** the
Codex priority queue; they create a parallel deliverable stream.

If at any point Codex finishes Priority 4.x (terminal Clay
endpoint via F3), Cowork's parallel work should already have
the continuum framework + RP infrastructure ready, so the
combined chain can produce a stronger statement.

If Codex hits an obstruction (e.g., the BK estimate is harder
than expected), Cowork's parallel branches still progress
toward their independent contributions.

---

## 8. Honest limitations

- **My mathematical depth on Bałaban RG is decent but not
  expert**. Branch II blueprints will be at the level of
  "identify the inductive step + cite literature", not novel
  contribution.
- **My Lean depth is limited**. Scaffolds will be predicate
  definitions + sorries + `#print axioms`. Full proofs are
  Codex's domain.
- **The Clay problem is genuinely hard**. No Cowork session can
  realistically close it. The realistic outcome of this work is:
  - 3 substantive blueprints
  - 2-3 Lean scaffolds with predicates and sorries
  - Identification of the precise mathematical contributions
    needed for each branch
  - Setup so a future agent (human or AI) can pick up exactly
    where I left off

I will not claim closure I cannot deliver. I will mark every
sorry, every "this needs Mathlib X", every literature gap.

---

## 9. Late-session update — Branch VIII added (2026-04-25 evening, Phase 84)

After Phase 81's investigation of Eriksson's Bloque-4 paper
(`YangMills-Bloque4.pdf`), a new branch is identified:

### Branch VIII — Multiscale correlator decoupling (Bloque-4 §6)

The third pillar of Bloque-4's mass gap argument, complementary to
Branch I (F3) and Branch II (Bałaban). Telescoping identity:

```
Cov_{µ_η}(F, G) = Cov_{µ_a*}(F̃, G̃) + Σ_k R_k(F, G)
```

where `R_k(F, G) = E[Cov(F, G | σ_{a_{k+1}}) | σ_{a_k}]` is a
conditional covariance term. Combined with the single-scale UV
error bound (Lemma 6.2) and geometric summation (Theorem 6.3),
this gives the lattice mass gap once terminal-scale clustering is
supplied (from Branch I or Branch II).

* **Strategic position**: independent of Branch II — only requires
  terminal-scale clustering, which can come from F3 (Branch I), or
  BalabanRG + `ClayCoreLSIToSUNDLRTransfer` (Branch II), or
  another future source.
* **Mathlib gap**: **Law of Total Covariance** (Mathlib PR draft in
  `YangMills/MathlibUpstream/LawOfTotalCovariance.lean`, Phase 82).
* **Blueprint**: `BLUEPRINT_MultiscaleDecoupling.md` (Phase 84).
* **Estimated effort**: ~290 LOC across 4–5 files in
  `YangMills/L7_Multiscale/`. Comparable to Phase 17 (dimensional
  transmutation witness).
* **Tractability**: HIGH for Cowork — probability-theoretic, fits
  Mathlib's existing `condExp` / `covariance` infrastructure
  cleanly.

### The OS1 caveat — single uncrossed barrier

Even Eriksson's Bloque-4 paper does **not** prove OS1 (full O(4)
Euclidean covariance). Theorem 1.4(c) is conditional on O(4)
holding in the continuum limit. This is the **single uncrossed
barrier** between the lattice mass gap and the literal Wightman QFT
of the Clay statement.

This justifies the project's `~12 %` literal-Clay estimate: even
if Branches I, II, III, VII, AND VIII all close, OS1 remains.

### Updated branch count

The opening tree now has **8 branches**:

| # | Branch | Status (post-late-session) |
|---|--------|---------------------------|
| I | F3 cluster expansion | active (Codex) |
| II | Bałaban RG | scaffold-complete (Codex BalabanRG/), 1 substantive obligation |
| III | Reflection positivity + TM | scaffold + SU(1) closed |
| IV | Stochastic quantization | not active |
| V | Direct constructive | not active |
| VI | Asymptotic freedom RG bootstrap | partially active via P6_AsymptoticFreedom |
| VII | Continuum limit specifically | analytical closure achieved (Phase 17) |
| **VIII** | **Multiscale correlator decoupling** | **NEW, blueprint stage (Phase 84)** |

Cross-references for Branch VIII:
- `BLUEPRINT_MultiscaleDecoupling.md` (Phase 84).
- `YangMills/MathlibUpstream/LawOfTotalCovariance.lean` (Phase 82).
- `YangMills/L6_OS/ClusteringImpliesSpectralGap.lean` (Phase 83).
- `ERIKSSON_BLOQUE4_INVESTIGATION.md` (Phase 81).
- `COWORK_FINDINGS.md` Finding 017.

---

*§9 added 2026-04-25 evening (Phase 84) by Cowork agent.*

---

*Master plan committed 2026-04-25 by Cowork agent. Execution
begins immediately.*
