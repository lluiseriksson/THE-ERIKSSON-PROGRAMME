# GLOSSARY.md

**Author**: Cowork agent (Claude), terminology compendium 2026-04-25
**Audience**: new contributors, external reviewers, future Cowork
agents, Lluis when needing to remember a name

This glossary covers two domains:

1. **Project-specific Lean terminology** (structures, predicates,
   theorems used in `YangMills/`).
2. **Mathematical-physics terminology** (cluster expansion,
   Brydges-Kennedy, Wilson loops, etc.) used throughout the
   strategic documents.

Entries are alphabetical within each section. Cross-references in
backticks point to other glossary entries (`like this`).

---

## A. Project-specific Lean terminology

### `AbelianU1Unconditional`

File: `YangMills/ClayCore/AbelianU1Unconditional.lean`. Contains the
N_c=1 unconditional witness `u1_clay_yangMills_mass_gap_unconditional :
ClayYangMillsMassGap 1`. **Caveat**: name is misleading — N_c=1 means
`SU(1) = {1}` (the trivial group), NOT the abelian QED-like U(1)
gauge theory. See `COWORK_FINDINGS.md` Finding 003. The bound is
satisfied trivially because the connected correlator vanishes
identically on the trivial group.

### `b0`

One-loop β-function coefficient for SU(N_c). In the
`GENUINE_CONTINUUM_DESIGN.md` design proposal, `b_0 = 11 N_c / (48 π²)`
governs the asymptotic-freedom flow `g(a) → 0`.

### `BalabanRG`

Subdirectory `YangMills/ClayCore/BalabanRG/` containing the most
heavily-used Bałaban renormalization-group infrastructure. Many
ClayCore files import from here.

### `ClayConnectedCorrDecay N_c`

Lean structure capturing the exponential decay of Wilson connected
correlators with positive mass gap. Companion to
`ClayYangMillsMassGap`. Constructed by
`clayConnectedCorrDecay_of_shiftedF3MayerCountPackageExp` (v1.82.0).

### `ClayYangMillsMassGap N_c`

The terminal **non-vacuous** lattice mass-gap structure defined in
`YangMills/ClayCore/ClayAuthentic.lean`. Contains:
- `m, hm`: the mass `m > 0`
- `C, hC`: the prefactor `C > 0`
- `hbound`: universal quantifier producing the exponential decay
  bound on the Wilson connected correlator

Currently inhabited only for `N_c = 1` via `AbelianU1Unconditional`
(with caveats). The N_c ≥ 2 case is the F3 frontier target.

### `ClayYangMillsPhysicalStrong`

Stronger Clay-grade predicate combining `IsYangMillsMassProfile m_lat`
(physical grounding) with `HasContinuumMassGap m_lat` (continuum
limit). Located in `YangMills/L8_Terminal/ClayPhysical.lean`.
**Caveat**: the continuum half is satisfied via the
`latticeSpacing` / `constantMassProfile` coordination, not via
genuine continuum analysis. See `COWORK_FINDINGS.md` Finding 004.

### `ClayYangMillsStrong`

Older strong predicate `∃ m_lat, HasContinuumMassGap m_lat`. Audited
as vacuous in `YangMills/L8_Terminal/ClayTrivialityAudit.lean` (any
constant mass profile satisfies it via the scaling trick).

### `ClayYangMillsTheorem`

The weakest endpoint: `∃ m_phys : ℝ, 0 < m_phys`. Logically
equivalent to `True`. Audited as vacuous in
`ClayTrivialityAudit.lean`.

### `clayMassGap_of_shiftedF3MayerCountPackageExp`

The terminal Clay-facing endpoint added in v1.82.0. Takes a
`ShiftedF3MayerCountPackageExp` and produces `ClayYangMillsMassGap N_c`.

### `ClusterCorrelatorBound N_c r C`

Lean predicate stating that the Wilson connected correlator is
bounded by `C · r^dist(p, q)`. Intermediate target on the F3 chain.

### `clusterPrefactorExp r K C_conn A₀`

The KP-series prefactor added in v1.80.0. Equals
`C_conn · A₀ · ∑' n, K^n · r^n` (= `C_conn · A₀ / (1 − K·r)` under
`K·r < 1`). Bridges the cluster-count + activity-decay to the
correlator bound.

### `ConnectedCardDecayMayerData N_c r A₀ ...`

Lean structure capturing the F3-Mayer side: a truncated activity
function `K` with bound `|K(Y)| ≤ A₀ · r^|Y|` for connected polymers,
plus the Mayer/Ursell identity tying it to `wilsonConnectedCorr`.
**Open**: the witness for SU(N_c) Wilson is the F3-Mayer Priority 2.x
work.

### `ConcretePlaquette d L`

Type of plaquettes in the finite lattice `(Fin L)^d`. Each plaquette
has a base site and two axis directions.

### `ConnectingClusterCount.lean`

File defining `ShiftedConnectingClusterCountBound` (the polynomial
frontier, structurally infeasible per Finding 001) plus all helpers.
970 lines.

### `ConnectingClusterCountExp.lean`

File defining `ShiftedConnectingClusterCountBoundExp` (the
exponential frontier from Resolution C, v1.79.0). The actively-used
F3-Count interface.

### `constantMassProfile m`

Lattice mass profile `m_lat N := m / (N+1)`. Despite the name, NOT
constant in `N`; rather, it scales as `1/(N+1)` to match
`latticeSpacing N = 1/(N+1)`. This is the artifact that satisfies
`HasContinuumMassGap` trivially. (Finding 004.)

### `eriksson-daily-audit`

Scheduled task created by Cowork agent that fires daily at 09:04
local time. Runs the contract evaluation per
`CODEX_CONSTRAINT_CONTRACT.md` §5 detection rules and writes
output to `COWORK_AUDIT.md`.

### `Experimental` (folder)

`YangMills/Experimental/` houses 14 declared axioms (per
`EXPERIMENTAL_AXIOMS_AUDIT.md`) representing the project's honest
remaining infrastructure gaps. The 0-axiom invariant says zero
axioms exist **outside** this folder.

### `gibbsMeasure`

The Wilson-Gibbs probability measure on gauge configurations,
defined in `YangMills/L1_GibbsMeasure/GibbsMeasure.lean` as
`(Measure.pi μ).tilted (-β · wilsonAction)`.

### `HasContinuumMassGap m_lat`

`∃ m_phys, 0 < m_phys ∧ Tendsto (renormalizedMass m_lat) atTop (𝓝 m_phys)`.
Defined in `YangMills/L7_Continuum/ContinuumLimit.lean`. **Caveat**
in Finding 004: structurally satisfiable via the
`constantMassProfile` / `latticeSpacing` coordination.

### `HR1` to `HR5` and `SR1` to `SR4`

Hard rules and soft rules from `CODEX_CONSTRAINT_CONTRACT.md` §2-§3.
HR = absolute (no violation tolerated). SR = soft (warning, not
escalation).

### `IsYangMillsMassProfile μ pe β F distP m_lat`

Predicate stating that the lattice mass profile `m_lat` actually
bounds the Wilson connected correlators of the Yang-Mills measure
`μ`. The **physical** (genuine, non-vacuous) half of
`ClayYangMillsPhysicalStrong`.

### `kpParameter r`

`-Real.log r / 2`. Converts the geometric decay rate `r < 1` into the
exponential decay constant `m`. The Clay mass gap from the F3
chain is `m = kpParameter wab.r = -log(4 N_c β) / 2 > 0`.

### `LatticeAnimalCount.lean`

File created in v1.85.0 containing the `plaquetteGraph`
SimpleGraph and the chain bridge to `PolymerConnected`. Priority 1.2
work-in-progress (Klarner BFS-tree count not yet proved).

### `LatticeMassProfile`

Type `ℕ → ℝ`. A function from lattice resolution to mass.
Consumed by `IsYangMillsMassProfile` and `HasContinuumMassGap`.

### `latticeSpacing N`

`1 / (N + 1)`. The repository's choice of lattice-spacing scheme
in `L7_Continuum/ContinuumLimit.lean`. Coordinated with
`constantMassProfile` to satisfy `HasContinuumMassGap` trivially.

### `lieDerivReg_all`

Axiom in `YangMills/Experimental/LieSUN/LieDerivReg_v4.lean`. Asserts
that **every** function `f : SU(N_c) → ℝ` satisfies the regularity
bundle. **Mathematically false** (per `EXPERIMENTAL_AXIOMS_AUDIT.md`
§3) — needs reformulation with a regularity hypothesis.

### `mono_count_dim`, `mono_dim`

Monotonicity lemmas raising the polynomial dimension exponent in
`ShiftedConnectingClusterCountBound`. Used by API ergonomics. The
v1.73-v1.78 release sequence was largely `mono_dim_apply` /
`mono_count_dim_apply` ergonomic canaries.

### `NEXT_SESSION.md`

File at `YangMills/ClayCore/NEXT_SESSION.md`. Codex-facing
working state. Auto-maintained by the daemon. Documents the
preferred F3 endpoints and packaging targets at any given time.

### `physicalClayDimension`

`= 4`. The physical lattice dimension for Yang-Mills.

### `PhysicalShiftedConnectingClusterCountBoundExp`

The d=4 specialisation of `ShiftedConnectingClusterCountBoundExp`.

### `PhysicalShiftedF3CountPackageExp`

The d=4 packaged version of the F3-Count side. Field of
`ShiftedF3MayerCountPackageExp.ofSubpackages`.

### `physicalStrong_of_expCountBound_mayerData_siteDist_measurableF`

L8 terminal endpoint added in v1.84.0. Produces
`ClayYangMillsPhysicalStrong` (with Finding 004 caveat) from the
F3 packages plus standard observable inputs.

### `PolymerConnected Y`

Predicate on `Finset (ConcretePlaquette d L)`: there is a path of
plaquettes in `Y` whose successive base sites are within Euclidean
distance 1. Defined in `YangMills/ClayCore/PolymerDiameterBound.lean`.

### `plaquetteFluctuationNorm` (`w̃`)

The normalized plaquette fluctuation
`exp(-β · Re tr U) / Z_p(β) - 1`. **Has zero mean** under Haar
(`plaquetteFluctuationNorm_mean_zero`, the keystone of the F3
chain).

### `plaquetteGraph d L`

The SimpleGraph on `ConcretePlaquette d L` whose adjacency is
"distinct plaquettes with site-distance ≤ 1". Added in v1.85.0
(`LatticeAnimalCount.lean`). The graph form of `PolymerConnected`.

### `ShiftedConnectingClusterCountBound C_conn dim`

Polynomial F3-Count frontier predicate. **Structurally infeasible**
(Finding 001). Replaced by the exponential frontier in v1.79.0,
but kept in code for backwards compatibility.

### `ShiftedConnectingClusterCountBoundExp C_conn K`

Exponential F3-Count frontier predicate. The actively-targeted
witness goal for Priority 1.2.

### `ShiftedF3MayerCountPackageExp N_c wab`

The unified F3 assembly object added in v1.82.0. Contains:
- `data : ConnectedCardDecayMayerData N_c wab.r ...` (Mayer side)
- `h_count : ShiftedConnectingClusterCountBoundExp C_conn K`
  (Count side)
- Smallness `hKr_lt1 : K * wab.r < 1`

When both witnesses land, this becomes inhabited and the chain
closes via `clayMassGap_of_shiftedF3MayerCountPackageExp`.

### `siteLatticeDist`

Euclidean distance between two lattice sites in `(Fin L)^d`.
Defined in `YangMills/ClayCore/ClayAuthentic.lean`.

### `sunHaarProb N_c`

Haar probability measure on `Matrix.specialUnitaryGroup (Fin N_c) ℂ`.
Defined via `MeasureTheory.Measure.haarMeasure (sunPositiveCompacts N_c)`.

### `WilsonPolymerActivityBound N_c`

Lean structure with fields `β, r, A₀, K` and the hypothesis
`|K γ| ≤ A₀ · r^|γ|`. The activity-side input to the F3 chain;
provided as data when constructing the Mayer witness.

### `WilsonUniformRpowBound N_c β C`

Predicate that the Wilson correlator obeys an `r^dist` bound
uniformly. Intermediate target leading to
`clayMassGap_small_beta_of_uniformRpow`.

### `wilsonConnectedCorr`

The connected two-plaquette correlator
`⟨W_p · W_q⟩ - ⟨W_p⟩ · ⟨W_q⟩` defined in
`YangMills/L4_WilsonLoops/WilsonLoop.lean`. The central quantity
the F3 chain bounds.

### `wilsonPlaquetteEnergy N_c`

`fun U => Re(tr U)`. The plaquette energy in the Wilson action.

---

## B. Mathematical-physics terminology

### Bałaban (renormalization group)

Tadeusz Bałaban's series of CMP papers (1989-1995) developing a
rigorous block-spin RG for lattice Yang-Mills. The project's
`P3_BalabanRG` and `ClayCore/BalabanRG/` directories formalise
parts of this framework.

### Battle-Federbush

A 1980s alternative formulation of cluster-expansion estimates
using random walks / tree graphs. Equivalent to Brydges-Kennedy
in spirit. Reference: G. Battle, P. Federbush 1984. Pinned-down
citation per `REFERENCES_AUDIT.md` §1.4.

### Brydges-Kennedy interpolation

A 1987 reformulation of the Mayer-Ursell truncated activity that
expresses `K(Y)` as an integral over interpolation parameters,
weighted by trees on `Y` (Cayley-style) rather than partitions.
Avoids the factorial blowup of naive Möbius inversion. Reference:
Brydges & Kennedy, JSP 48 (1987).

### cluster expansion

A standard technique in classical statistical mechanics for the
high-temperature regime: express the partition function (or
correlator) as a sum over "polymers" (connected sets of basic
units), with Möbius inversion / random-walk reorganisation to
control convergence. The F3 chain is a cluster expansion of the
Wilson connected correlator.

### connective constant

The exponential growth rate `μ_d` of the number of self-avoiding
walks of length n in `ℤ^d`. Equivalent to the asymptotic growth
rate of the connected animal count. For `d = 4`, classical
estimates give `μ_4 ∈ (4, 7)` (with `2d - 1 = 7` as the
Klarner upper bound).

### dimensional transmutation

The phenomenon in asymptotically-free gauge theories where a
dimensionless coupling `g(a)` introduces a dimensionful scale `Λ`
via the RG running: `Λ = a · exp(-1/(2 b_0 g²))`. This is what
makes the continuum mass gap finite even though both `m_lat(N)`
and `latticeSpacing(N)` go to zero. (Discussed in
`GENUINE_CONTINUUM_DESIGN.md`.)

### Dirichlet form

A bilinear form on `L²(μ)` that captures "energy" for a Markov
process. The `sunDirichletForm` in `P8_PhysicalGap` is the SU(N)
version. Generates a semigroup via Hille-Yosida (one of the open
Experimental axioms).

### finest partition

The set partition into singletons. The bottom of the partition
lattice. Mathematical context for `Finpartition.singletonsPartition`
in `mathlib_pr_drafts/PartitionLatticeMobius.lean`.

### Haar measure

The unique left-translation-invariant probability measure on a
compact group. For SU(N_c), `MeasureTheory.Measure.haarMeasure`
with the project's choice `sunHaarProb`.

### Hille-Yosida theorem

Classical operator-theory result: a closed densely-defined
dissipative operator with the right resolvent properties generates
a strongly continuous semigroup. The project axiomatises a
Markov-chain version (`hille_yosida_core` in
`Experimental/Semigroup`).

### Klarner / lattice-animal counting

The 1967 Klarner paper *Cell-growth problems* introduced systematic
upper bounds on the number of connected polyominoes / lattice
animals. The bound `count(m) ≤ (2d-1)^(m-1)` (or looser variants)
is the "Klarner bound" used in Priority 1.2.

### Kotecký-Preiss criterion

A 1986 paper by Kotecký and Preiss giving a clean smallness
condition for cluster expansion convergence: if the activity bound
is `r^|Y|` and the count bound is `K^|Y|`, then `r · K < 1`
suffices for convergence. The F3 chain uses this regime.

### Mayer-Ursell expansion

The classical statistical-mechanics decomposition expressing the
log of the partition function (or correlator) as a sum over
"truncated" polymer activities. The truncation is what makes
disconnected polymers contribute zero, leaving only connected
polymers in the sum.

### Möbius inversion (partition lattice)

The inversion theorem for the lattice of set-partitions ordered
by refinement. Yields `μ(⊥, π) = ∏ B (-1)^(|B|-1) (|B|-1)!` per
Stanley 2012 §3.10. The algebraic content of the Mayer-Ursell
truncation. (Mathlib gap, draft in `mathlib_pr_drafts/PartitionLatticeMobius.lean`.)

### Osterwalder-Schrader (OS) reconstruction

The procedure for constructing a continuum quantum field theory
from a lattice model satisfying reflection positivity. Required
to bridge the lattice mass gap to the continuum Clay statement.
**Outside the project's scope** — the formalisation targets the
lattice mass gap only.

### Peter-Weyl theorem

The decomposition `L²(G) = ⊕ V_ρ ⊗ V_ρ*` for compact groups `G`,
where the sum is over isomorphism classes of irreducible
representations. The original Peter-Weyl roadmap targeted this
for Mathlib formalisation; **reclassified as aspirational**
(Decision 002).

### plaquette

A unit square on the lattice, with two axis directions. The
elementary face of the lattice gauge theory. Holonomy around a
plaquette gives the field strength.

### Stroock-Zegarliński

A 1992 paper bridging logarithmic Sobolev inequalities to
exponential decay of correlations in lattice systems. Was on the
project's earlier critical path; superseded by F3 cluster
expansion approach.

### tilted measure

A measure of the form `dν = exp(-βH) dμ` where `μ` is a base
measure and `H` is a Hamiltonian. The Wilson-Gibbs measure is the
tilt of the product Haar measure by `-β · wilsonAction`.

### Wightman axioms

The standard axioms for relativistic quantum field theory in the
Garding-Wightman framework. Required by the Clay Millennium
statement; **outside this project's scope**.

### Wilson action

`S(U) = ∑_p Re(tr U_p)` where the sum is over plaquettes and `U_p`
is the holonomy. Defined in `YangMills/L0_Lattice/WilsonAction.lean`.

### Wilson connected correlator

`⟨F(U_p) · F(U_q)⟩ - ⟨F(U_p)⟩ · ⟨F(U_q)⟩` for class observables
`F`. The central quantity the lattice mass gap bounds.

### Wilson loop

The trace of a holonomy around a closed loop on the lattice. The
gauge-invariant observable in lattice gauge theory.

---

## C. Cross-document references

For names not in this glossary, see:

- `STATE_OF_THE_PROJECT.md` — current state with named structures
  in context.
- `MATHEMATICAL_REVIEWERS_COMPANION.md` — full mathematical
  exposition with cross-references.
- `F3_CHAIN_MAP.md` — every theorem in the F3 chain with its
  purpose.
- `CONTRIBUTING_FOR_AGENTS.md` and `CODEX_CONSTRAINT_CONTRACT.md`
  for governance terms.
- `REFERENCES_AUDIT.md` for primary-source citations.

---

## D. Post-Phase 463 additions (terms introduced 2026-04-25 in late-session arcs)

### D.1 Physics-anchoring terminology (L42-L44 blocks)

**β₀ (one-loop beta function coefficient)**
For pure Yang-Mills with gauge group SU(N_c), `β₀ = (11/3) · N_c`. The foundational coefficient governing asymptotic freedom: at fixed coupling, the renormalisation group flow is `μ · dg/dμ = -β₀ · g³` at one loop. Defined in `YangMills/L42_LatticeQCDAnchors/BetaCoefficients.lean`.

**β₁ (two-loop beta function coefficient)**
For pure Yang-Mills, `β₁ = (34/3) · N_c²`. Together with β₀ governs the two-loop running. The ratio `β₁ / β₀² = 102/121` is **scheme-independent** and N_c-independent.

**Λ_QCD (QCD scale)**
The unique dimensional scale of pure Yang-Mills, generated by **dimensional transmutation**:
  `Λ_QCD = μ · exp(-1 / (2 · β₀ · g²(μ)))`,
where μ is any renormalisation scale and g²(μ) the coupling at that scale. Every dimensional observable is proportional to a power of Λ_QCD.

**c_Y (mass-gap dimensionless constant)**
The dimensionless ratio `m_gap / Λ_QCD`. In pure Yang-Mills, `m_gap = c_Y · Λ_QCD`. **NOT derived from first principles** — accepted as anchor input in `MassGapAnchor` of L42. Numerical lattice QCD measures `c_Y ≈ 1.5-1.7` for SU(3).

**c_σ (string-tension dimensionless constant)**
The dimensionless ratio `σ / Λ_QCD²`. In pure Yang-Mills, `σ = c_σ · Λ_QCD²`. NOT derived from first principles — accepted as anchor input in `StringTensionAnchor` of L42.

**Wilson area law**
Statement that the Wilson loop expectation `⟨W(C)⟩ ≤ K · exp(-σ · A(C))` for closed loop C bounding minimal surface of area `A(C)`. The **Holy Grail of Confinement** for SU(N) Yang-Mills. Open since Wilson 1974.

**Z_N center subgroup**
The center of SU(N) is `{ω·I : ω^N = 1} ≅ Z_N`. For SU(2): `Z_2 = {±1}`. For SU(3): `Z_3 = {1, e^(2πi/3), e^(4πi/3)}`. Defined in `YangMills/L43_CenterSymmetry/CenterGroup.lean`.

**Polyakov loop expectation `⟨P⟩`**
The expectation value of the trace of the holonomy around a non-contractible time circle. Transforms under center as `⟨P⟩ ↦ ω · ⟨P⟩`. **Order parameter for deconfinement**: confined phase has `⟨P⟩ = 0`; deconfined phase has `⟨P⟩ ≠ 0`.

**'t Hooft coupling λ**
`λ = g² · N_c`, held fixed in the **large-N limit** `N_c → ∞`. Foundational organising parameter of the 1/N expansion. Defined in `YangMills/L44_LargeNLimit/HooftCoupling.lean`.

**Planar dominance**
In the limit `N_c → ∞`, only **planar (genus-0) Feynman diagrams** contribute at leading order. Non-planar (genus-`g ≥ 1`) diagrams are suppressed by `(1/N²)^g`. Encoded as `genusSuppressionFactor` in L44.

**Triple-view confinement characterisation**
The complete structural characterisation of pure Yang-Mills confinement via three complementary views:
- **L42 (continuous view)**: area law + string tension + dimensional transmutation.
- **L43 (discrete view)**: `Z_N` center + Polyakov loop + symmetry breaking.
- **L44 (asymptotic view)**: 't Hooft coupling + planar dominance.

See `TRIPLE_VIEW_CONFINEMENT.md` for the synthesis.

### D.2 Governance / process terminology

**Sorry-catch**
A governance event where a Lean proof's first version reaches for unproved high-level machinery and admits a `sorry`. The project's 0-sorry discipline catches this immediately. **Resolution**: rewrite the theorem to take the unproved fact as an explicit hypothesis-conditioned input rather than admit it inline. Two sorry-catches occurred in this session (Phase 437 + Phase 444), both resolved.

**Hypothesis-conditioning**
The signature governance pattern of the project: when a Lean proof reaches for unproved facts, **rewrite the theorem to take those facts as explicit hypotheses** rather than admit them inline. Preserves the physical content; surfaces the unproved subgoal for future closure. Validated twice in 2026-04-25 session.

**P0 closure mini-arc**
A short post-bookend arc (Phases 458-462 in 2026-04-25) where 3 of 5 P0 questions from `OPEN_QUESTIONS.md` were addressed in single phases each. Demonstrates that some P0-tier work is tractable in sub-multi-week timescales when the underlying machinery is elementary. Documented in Finding 024.

**Two-stage pattern**
A consequence of the hypothesis-conditioning + P0 closure mini-arc pattern: hypothesis-condition first (immediate, when proof over-reaches), close later (in a dedicated phase, when machinery is tractable). Validated by Phase 437 → Phase 458 closure of `centerElement N 1 ≠ 1`.

**Triple discipline**
The project's combined discipline: **0 sorries** + **0 axioms outside `Experimental/`** + **`#print axioms` only `[propext, Classical.choice, Quot.sound]`**. Maintained throughout the 2026-04-25 session despite 2 sorry-catches.

### D.3 Mathlib upstream terminology

**PR-ready file**
A Lean file in `mathlib_pr_drafts/` factored from project consumers, designed for upstream Mathlib submission. Self-contained, with copyright Apache-2.0 header, proof strategy docstring, PR submission notes, and closing `#print axioms`. **18 such files exist in 2026-04-25 session**, none yet built with `lake build`.

**Tactic-name drift**
The phenomenon where Lean tactics or lemma names change between Mathlib versions. Real risk for the 18 PR-ready files: e.g., `pow_le_pow_left` → `pow_le_pow_left₀`, `lt_div_iff` → `lt_div_iff₀`, `Real.log_div` argument order, etc. Documented in `MATHLIB_SUBMISSION_PLAYBOOK.md` §2.3.1.

**Sandwich pair**
A coordinated PR submission of two complementary Mathlib lemmas that together produce a two-sided bound. Example: `ExpNegLeOneDivAddOne_PR.lean` + `ExpLeOneDivOneSub_PR.lean` produce the sandwich `1+x ≤ exp(x) ≤ 1/(1-x)` and `1-x ≤ exp(-x) ≤ 1/(1+x)` on `[0, 1)`. Recommended as single coordinated PR in `INDEX.md`.

**Bidirectional Mathlib relationship**
The project consumes from Mathlib (documented in `MATHLIB_GAPS.md`, 5 inward gaps) and contributes to Mathlib (documented in `MATHLIB_PRS_OVERVIEW.md`, 18 outward PR-ready). The two directions are explicitly cross-referenced (Phase 422 audit).

---

*Glossary prepared 2026-04-25 by Cowork agent. Section D added Phase 464 (terms introduced in arcs L42-L44 + Mathlib upstream + sorry-catch governance). Update when new terminology appears in the strategic docs or in the Lean code.*
