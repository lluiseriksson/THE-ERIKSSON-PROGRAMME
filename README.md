# The Eriksson Programme

**Machine-checked lattice gauge theory, with an active hRpoly research programme.**

[![Lean](https://img.shields.io/badge/Lean-4.29.0--rc6-blue)](lean-toolchain)
[![Source scan](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-AGPL--3.0-lightgrey)](LICENSE)

[Explore YangMills](YangMills/README.md) · [What's new](NEWS.md) · [hRpoly status](docs/HRPOLY-STATUS.md) · [Documentation](docs/README.md) · [Reproduce](REPRODUCIBILITY.md)

The Eriksson Programme develops Lean 4 / Mathlib proofs for SU(N) lattice
Yang–Mills theory: polymer cluster expansions, Wilson-loop area laws,
exponential clustering and source-specific renormalization-group estimates.
The verified core and the active research frontier each have explicit scope,
hypotheses and evidence.

> **5 September 2026 · Research update**
>
> hRpoly work continues in [draft PR #29](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/29),
> with new recorded checks for source-flow full-Green identities and a sharper
> map of the remaining physical bounds. The public documentation now connects
> that work to `main`. [Read the update →](NEWS.md)

## Progress Dashboard

| Track | Status | Explore |
|---|---|---|
| KP/Mayer cluster-expansion engine | Recorded core results | [KP source](YangMills/KP/) |
| Strong-coupling area laws and IR clustering | Recorded core results, with explicit parameter windows | [Headline results](#headline-results-all-oracle-clean-all-in-the-core) |
| Concrete physical activity bound `hRpoly` | **Open · research branch** | [20/41 terminal producers; `TermSource = 0`](docs/HRPOLY-STATUS.md) |
| Physical scalar window 15 | **Compatible; not attained** | [Remaining milestones](docs/HRPOLY-STATUS.md#what-comes-next) |
| Four-dimensional continuum limit and reconstruction | **Open mathematics** | [Hypothesis frontier](HYPOTHESIS_FRONTIER.md) |

**The counts are construction milestones, not a percentage of a Millennium
Problem solved.** No four-dimensional continuum mass gap is claimed. The
project's historical Clay-distance shorthand remains **~0% (<0.1%)**.

The [hRpoly status page](docs/HRPOLY-STATUS.md) is a dated, commit-linked guide
to the active branch. The [dependency dashboard](https://lluiseriksson.github.io/THE-ERIKSSON-PROGRAMME/dashboard/)
describes the curated main programme. The canonical recorded main proof
checkpoint remains [`project-state.json`](project-state.json); neither the
new documentation date nor a branch build count updates that contract.

## Start with a result, then follow its evidence

- **New to the project:** [YangMills introduction and source map](YangMills/README.md).
- **Returning after a few weeks:** [research news](NEWS.md) and [current hRpoly obstacles](docs/HRPOLY-STATUS.md).
- **Checking a claim:** its exact source revision, [verification ledger](docs/VERIFICATION-LEDGER.md), and [reproduction instructions](REPRODUCIBILITY.md).
- **Looking to help:** [contribution guide](CONTRIBUTING.md) and [documentation index](docs/README.md).

The source-scan badge reports the repository's textual checks, not a Lean
compilation. Mathematical verification is scoped to the exact source and
build/oracle evidence. Hard open inputs remain theorem hypotheses; the core
does not silently assume them as project axioms.

---

## Headline results (all oracle-clean, all in the core)

### 0. The volume-uniform area law — *the current flagship*

For the **normalized** Wilson-loop expectation at conjugate-pair linearized
activities (the physical `Re tr` weight, ‖c<sub>p</sub>‖ ≤ δ) in an explicit
strong-coupling window, and any rate σ ∈ [0,1] with (16d+1)²σ < 1 and
2δN<sub>c</sub>·e<sup>16d·K</sup> ≤ σ²:

$$\Bigl\lVert \frac{\int \mathrm{tr}(W_C)\cdot\prod_p (1+f_p)}{Z} \Bigr\rVert \;\le\; N_c \cdot e^{|\mathrm{loopSupp}|\cdot 4d\cdot K} \cdot \sigma^{\mathrm{Area}(C)} \cdot e^{|\mathrm{loopSupp}|\cdot 4d\cdot S(\sigma)}$$

`theorem normalized_wilson_loop_area_law` — [`YangMills/L1_GibbsMeasure/RestrictedGate.lean`](YangMills/L1_GibbsMeasure/RestrictedGate.lean)

**Every constant is volume-free** — area-law decay with a perimeter-only
prefactor, uniformly over all finite lattices. The partition function is
cancelled through a fully formalized volume-restricted cluster expansion
(loop-tagged factorization, restricted Mayer inversion, Z-ratio bounds, pinned
gas resummation — [`docs/AREA-LAW-VU-PLAN.md`](docs/AREA-LAW-VU-PLAN.md), all
bricks closed). The hypothesis window is non-empty (ledger Addendum 17t), and
the integrability inputs are theorems, not hypotheses
(`normalized_wilson_loop_area_law_unconditional`, Addendum 17u): every
remaining hypothesis is an explicit smallness or geometry condition.

The **exact-activity** version `normalized_exp_wilson_loop_area_law`
([`RestrictedGate.lean`](YangMills/L1_GibbsMeasure/RestrictedGate.lean), ledger
Addenda 18–18d) extends the same volume-uniform bound to the **true Wilson
Boltzmann factor** ∏<sub>p</sub> exp(z<sub>p</sub>) — area decay σ<sup>Area(C)</sup>
with a perimeter-only prefactor and rate (e<sup>2δN<sub>c</sub></sup>−1), again with
no integrability hypotheses. Because the volume-restricted cluster machinery is
activity-agnostic, the exact version is the linearized proof with the single
substitution 2δN<sub>c</sub> → e<sup>2δN<sub>c</sub></sup>−1. **The area-law
programme is thus complete in all four variants** (finite-volume and
volume-uniform, each linearized and exact).

**Paper.** The flagship and its formalized cluster expansion are written up in:

> *A Machine-Checked Volume-Uniform Wilson-Loop Area Law via a Formalized
> Cluster Expansion*, L. Eriksson, 2026 —
> [`paper/area-law/paper.pdf`](paper/area-law/paper.pdf).
> The repository PDF is linked above; this entry records no external preprint identifier.

A reusable repackaging `area_law_to_exp_area_decay` turns either headline into
**manifest exponential area decay** N<sub>c</sub>·e<sup>−τ·Area(C)</sup> with a
strictly positive string tension τ = (−log σ) − λ, on any loop family whose
perimeter charge is area-subdominant — making the confinement physics explicit.
Its non-vacuity is itself machine-checked
(`area_law_to_exp_area_decay_window_nonempty`: an explicit witness with positive
tension log 2 − ½, ledger Addendum 20).

### 1. The exact-activity Wilson-loop area law

For SU(N<sub>c</sub>) lattice gauge theory with the **true Wilson Boltzmann
factor** ∏<sub>p</sub> exp(z<sub>p</sub>), where
z<sub>p</sub> = c<sub>p</sub>·tr H<sub>p</sub> + c′<sub>p</sub>·conj tr H<sub>p</sub>
and ‖c<sub>p</sub>‖, ‖c′<sub>p</sub>‖ ≤ δ — with **no smallness hypothesis** (any δ ≥ 0):

$$\Bigl\lVert \int \mathrm{tr}(W_C)\cdot\prod_p e^{z_p}\, d\mu_{\mathrm{Haar}} \Bigr\rVert \;\le\; N_c \cdot 2^{|P|} \cdot \bigl(e^{2\delta N_c}-1\bigr)^{\mathrm{Area}(C)} \cdot e^{2\delta N_c\,|P|}$$

`theorem finite_volume_area_law_exp` — [`YangMills/ClayCore/WilsonLoopMonomial.lean`](YangMills/ClayCore/WilsonLoopMonomial.lean)

Here `Area(C)` is the **N-ality area** — the minimal number of plaquettes any
ℤ/N<sub>c</sub> 2-chain needs to span the loop `C`, built from a formalized
lattice chain complex ([`L0_Lattice/ChainComplex.lean`](YangMills/L0_Lattice/ChainComplex.lean)).
At Wilson coupling (2δN<sub>c</sub> = β) the bound decays exponentially in the
area for β < ln 2. Non-vacuity is itself a theorem: concrete plaquette loops
have `Area ≥ 1` (`one_le_chainAreaA_plaquette`). The linearized-activity
versions `finite_volume_area_law` / `finite_volume_area_law_re` (the physical
`Re tr` observable) bound the same integral by `N_c·2^{#P}·(2δN_c)^{Area}`.

*Honest caveat:* the constant here is finite-volume (`2^{#P}`); the
volume-uniform refinement — for both this exact factor and the linearized one —
is result 0 above (now closed).

### 2. The unconditional IR clustering bound

`theorem gibbs_truncated_correlation_bound` — exponential decay of truncated
plaquette correlations for the lattice Gibbs measure at strong coupling, with an
explicit non-empty coupling window (`clustering_window_nonempty`), proved end to
end through the weighted-gas covariance identity and the pinned-cluster
Kotecký–Preiss bound. The SU(N)-specific form is
`sun_two_plaquette_correlator_bound` ([`TwoPlaquetteCorrelator.lean`](YangMills/L1_GibbsMeasure/TwoPlaquetteCorrelator.lean)),
proved **without Peter–Weyl**.

### 3. The conditional lattice mass gap (M3 assembly)

`theorem lattice_mass_gap_of_exp_clustering_uniform`
([`Paper/ClusteringToGap.lean`](YangMills/Paper/ClusteringToGap.lean)) assembles
the lattice mass gap from (i) an IR clustering bound — **now theorem-fed** by
result 2 — and (ii) the §6.3 Balaban single-scale UV bound, which is the
**sole remaining carried hypothesis** of the whole assembly. It is a named
hypothesis of a theorem, never an axiom. See
[`HYPOTHESIS_FRONTIER.md`](HYPOTHESIS_FRONTIER.md).

`theorem lattice_mass_gap_of_per_scale_uv` (same file, ledger Addendum 19)
sharpens that carried hypothesis to the renormalization-group level: the UV
covariance is the finite sum of per-scale RG remainders, and a **single
geometric per-scale contraction** |R<sub>t,k</sub>| ≤ (C₂·e<sup>−c₀t</sup>)·rᵏ —
exactly the form Balaban's Lemma 6.2 supplies — already yields the mass gap, via
the proved §6.3 summation mechanism (`uv_geometric_summation`).

The gauge-RG branch then refines the UV obligation into a source-grounded,
oracle-clean conditional. `lattice_mass_gap_of_cluster_and_coupling`
([`YangMills/RG/UVMassGap.lean`](YangMills/RG/UVMassGap.lean), ledger
Addendum 52) handles the geometric-profile version; the later marginal-coupling
branch (`YangMills/RG/MarginalUVMassGap.lean`, Addenda 62–65) records the honest
4D correction: the Yang-Mills coupling is marginal/asymptotically free, so the
scale profile is summable rather than geometrically decaying. Around this sit
the verified RG substrates in `YangMills/RG/**`: block-spin geometry, the
averaging operator with gauge covariance and explicit l²-contraction,
near-identity logarithm estimates, Gaussian pushforward and finite-dimensional
Gaussian construction, exponential-decay kernel calculus, Schur bounds, PSD
kernel interface, animal counting, cube summability, and shell-growth
summability.

**Honest caveat.** The §6.3 branch is still conditional on the concrete
Yang-Mills **activity-decay** input `hRpoly`: the Dimock/Balaban cluster
expansion with holes plus the fluctuation-integral estimate for the actual
gauge RG operator. The scaffolding around that input is theorem-fed; the
model-specific constructive-QFT estimate is genuine, months-scale mathematics
with no Mathlib primitive. None of this is a continuum result; the Clay
distance is unchanged at ~0%.

### 4. The cluster-expansion layer

The Mayer–Ursell inversion `Ξ = exp(clusterSum)`
(`partition_eq_exp_clusterSum`, [`KP/MayerInversion.lean`](YangMills/KP/MayerInversion.lean)),
the `Z = Ξ` polymer reconstruction, a sharp Kotecký–Preiss convergence bound
with BFS-Penrose tree counting, and pinned-cluster tails — the reusable
constructive-QFT engine behind results 2 and (planned) the volume-uniform area law.

### 5. The SU(N) Haar selection-rule programme

The ℤ<sub>N</sub> grading of Haar integration, Peter–Weyl-free, from characters
up to matrix coefficients: ∫ tr U = 0, ∫ (tr U)<sup>a</sup>(conj tr U)<sup>b</sup> = 0
for N ∤ (a−b), the decorated-entry monomial kill, ∫ |tr U|² ≤ N
([`ClayCore/Schur*.lean`](YangMills/ClayCore)). These are the algebraic engine
of the area law's "kill" mechanism.

The complete machine-checked record — verbatim oracle outputs for every result
above, thirty-plus addenda — is [`docs/VERIFICATION-LEDGER.md`](docs/VERIFICATION-LEDGER.md).

---

## What is **not** proved (read this before citing anything)

* **No continuum limit, no OS/Wightman reconstruction, no continuum mass gap.**
  These are the Clay problem's actual content and they are open mathematics.
  Distance to the Clay prize: **~0% (<0.1%)** — and every status document in
  this repo is required to say so.
* **The §6.3 Balaban UV single-scale bound is a carried hypothesis** of the M3
  assembly (deliberately: it is real mathematics that we have not formalized,
  so it appears as a theorem hypothesis, not an axiom).
* Everything proved is **lattice, strong-coupling
  (Osterwalder–Seiler regime)** — the regime where confinement is classical
  physics lore; the achievement here is the *machine-checked* mathematics, not
  new physics.

<details>
<summary><b>Legacy disclaimer: the vacuous theorem this repo once advertised</b></summary>

An earlier era of this repository exposed a terminal theorem
`clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys` — which is **vacuous**
(closed by `⟨1, one_pos⟩`; nothing about gauge theory is needed). The 2026-05-29
cleanup ([`CLEANUP_PLAN.md`](CLEANUP_PLAN.md), [`FOUNDATIONS.md`](FOUNDATIONS.md))
carved the sound core out of that sprawl: `YangMillsCore`'s import closure
contains **none** of the vacuous-target chain, none of the legacy axioms, and
zero `sorry`. The legacy status documents are archived in
[`docs/legacy/`](docs/legacy/) as a historical record of what over-claiming
looks like and how it was corrected. The legacy Lean modules still present in
the tree outside the core are scheduled for staged removal and are **not**
part of any claim this README makes.

</details>

---

## Architecture

```mermaid
graph TD
    subgraph core["YangMillsCore  (8463 jobs, oracle-clean)"]
        L0["L0_Lattice<br/>geometry, gauge fields, Wilson action,<br/>chain complex + N-ality area"]
        L1["L1_GibbsMeasure<br/>Gibbs measure, polymer representation,<br/>weighted gas, exp-activity expansion"]
        KP["KP layer<br/>Ursell, Penrose-BFS, sharp KP bound,<br/>Mayer inversion Ξ = exp(clusterSum),<br/>pinned clusters"]
        SCHUR["ClayCore / Schur*<br/>SU(N) Haar selection rules,<br/>Z_N grading, entry monomials"]
        WLM["ClayCore / WilsonLoopMonomial<br/>the join + AREA LAWS"]
        PAPER["Paper layer<br/>clustering → mass gap assembly<br/>(UV bound = carried hypothesis)"]
        P8["P8_PhysicalGap<br/>SU(N) compactness, Haar states,<br/>L log L envelope"]
    end
    L0 --> L1 --> KP
    L0 --> SCHUR --> WLM
    L1 --> WLM
    L1 --> PAPER
    KP --> PAPER
    P8 --> SCHUR
    style WLM fill:#1a7f37,color:#fff
    style PAPER fill:#9a6700,color:#fff
```

Green: unconditional flagship. Amber: conditional on the named UV hypothesis.

---

## Build & verify

Maintainer Lean/Lake builds and sustained computation run in dedicated Colab
Pro+ Linux runtimes under [repository governance](docs/OPERATIONAL-GOVERNANCE-CHARTER.md).
The commands below describe verification, not a new build performed for this
documentation update.

| Step | Command | Expected |
|---|---|---|
| Toolchain | `elan` picks up [`lean-toolchain`](lean-toolchain) | `leanprover/lean4:v4.29.0-rc6` |
| Mathlib cache | `lake exe cache get` | downloads the pinned-commit `.olean` cache |
| Build the core | `lake build YangMillsCore` | Exit zero; compare the job count with evidence for the exact source revision |
| Axiom oracle | `lake env lean oracle_check.lean` | Only allowed standard axioms: `propext`, `Classical.choice`, `Quot.sound` (axiom-free declarations are allowed) |
| Sorry scan | `python scripts/check_consistency.py` | `0` forbidden tokens |
| Source citation lookup | `python scripts/source_citations.py show cmp116.eq231.p-bond-sum` | compact primary-source locator |
| Source excerpt lookup | `python scripts/source_citations.py excerpt cmp116.eq231.p-family-carrier-source-target` | line-numbered local source text |
| Source DB lookup | `python scripts/source_db.py frontier --term eq231` | source-linked frontier cards and open questions |

The default `lake build` target (`YangMills.lean`) is just an alias for the core.
**Mathlib is pinned to an exact commit** (lakefile + manifest agree), so the
verified state rebuilds exactly — see [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md).

---

## Documentation map

Start with the [documentation index](docs/README.md), [research news](NEWS.md)
and [current hRpoly status](docs/HRPOLY-STATUS.md). The table below is the
established main reference collection; older campaign entries retain their
original checkpoint scope.

| Document | What it is |
|---|---|
| [`docs/dashboard/`](docs/dashboard/) | The static public "Distance to the Mass Gap" dashboard: curated DAG data, linked evidence, and a no-dependency GitHub Pages front end. |
| [`docs/VERIFICATION-LEDGER.md`](docs/VERIFICATION-LEDGER.md) | **The record.** Verbatim oracle outputs for every headline, earlier Addenda 1-444, date-stamped checkpoints, the 2026-07-03 Catalan/Schur series through Addendum 465, and the 2026-07-04 diamagnetic bridge Addendum 466. Start here to check any claim. |
| [`docs/M3-FRONTIER-DEPENDENCIES.md`](docs/M3-FRONTIER-DEPENDENCIES.md) | The executable M3 frontier dependency graph, mirrored for humans. |
| [`docs/SOURCE-CITATIONS.md`](docs/SOURCE-CITATIONS.md) | The compact primary-source lookup for CMP116 Lemma 3: visual anchors, blockers, and source targets without repeated OCR hunting. |
| [`docs/source-db/README.md`](docs/source-db/README.md) | The broader source-spine database: coverage, crosswalks, artifact manifests, proof obligations, and frontier queues. |
| [`HYPOTHESIS_FRONTIER.md`](HYPOTHESIS_FRONTIER.md) | The carried hypotheses, audited. Currently exactly one (§6.3 UV), now sharpened to a per-scale RG contraction. |
| [`FOUNDATIONS.md`](FOUNDATIONS.md) | What "proved" means here; the vacuity audit doctrine. |
| [`CLEANUP_PLAN.md`](CLEANUP_PLAN.md) | How the sound core was carved out of the legacy sprawl. |
| [`HORIZON.md`](HORIZON.md) | The formal dependency DAG to a real mass gap, as fill-in-the-blank Lean signatures. |
| [`ROADMAP.md`](ROADMAP.md) | The measurable plan, written against reality rather than a vacuous target. |
| [`docs/AREA-LAW-PLAN.md`](docs/AREA-LAW-PLAN.md) · [`AREA-LAW-EXACT-PLAN.md`](docs/AREA-LAW-EXACT-PLAN.md) · [`AREA-LAW-VU-PLAN.md`](docs/AREA-LAW-VU-PLAN.md) | The area-law campaigns — all **complete**: linearized, exact-activity, and volume-uniform (V0–V4 closed, both linearized and exact). |
| [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) | How to rebuild the exact verified state (pinned Mathlib commit) and re-run the oracle checks. |
| [`CURRENT-STATE.md`](CURRENT-STATE.md) | Accumulated dated programme snapshots; follow its opening link for the current hRpoly research summary. |
| [`docs/BALABAN-RG-PLAN.md`](docs/BALABAN-RG-PLAN.md) · [`UV-S2-GAUSSIAN-PLAN.md`](docs/UV-S2-GAUSSIAN-PLAN.md) · [`UV-U1-SMALL-FIELD-PLAN.md`](docs/UV-U1-SMALL-FIELD-PLAN.md) · [`BALABAN-SOURCE-BOUNDS.md`](docs/BALABAN-SOURCE-BOUNDS.md) · [`docs/FLOW-DIAMAGNETIC-PLAN.md`](docs/FLOW-DIAMAGNETIC-PLAN.md) | The **gauge-RG continuum-facing track** (`YangMills/RG/**`): the averaging/Gaussian/kernel/animal-count substrate, the flow-diamagnetic UV branch, and the faithful Balaban/Dimock source bounds; the open input is the concrete YM activity-decay bound `hRpoly`. |
| [`docs/PHYSICAL-OPERATOR-VERTICAL-SLICE.md`](docs/PHYSICAL-OPERATOR-VERTICAL-SLICE.md) | The P4 physical-operator route from Wilson action to covariance to localized activities. Deterministic bricks, source dictionaries, and component boundaries are closed; the physical Hessian/source estimates remain open. |
| [`docs/UV-SINGLE-SCALE-PLAN.md`](docs/UV-SINGLE-SCALE-PLAN.md) | The §6.3 UV-bound campaign. The logical/summability/coupling scaffolding is oracle-clean; the remaining months-scale work is the model-specific cluster-expansion-with-holes activity estimate. |
| [`docs/SHARP-KP-PLAN.md`](docs/SHARP-KP-PLAN.md) · [`kp-cluster-expansion-plan.md`](docs/kp-cluster-expansion-plan.md) · [`CLUSTER-CORRELATION-PLAN.md`](docs/CLUSTER-CORRELATION-PLAN.md) | The cluster-expansion campaigns (complete). |
| [`PETER_WEYL_ROADMAP.md`](PETER_WEYL_ROADMAP.md) | The standalone Peter–Weyl formalization plan (off the critical path). |
| [`docs/legacy/`](docs/legacy/) | Pre-cleanup era, kept as history. Nothing in it is current. |

**For AI agents:** [`CLAUDE.md`](CLAUDE.md) (hard rules, build mechanics) →
[`README-FOR-NEXT-MODEL.md`](README-FOR-NEXT-MODEL.md) (the live frontier) →
[`AGENT-ONBOARDING.md`](AGENT-ONBOARDING.md) (full brief).

---

## Recorded manuscript submission (2026-08-03)

**Submitted 2026-08-03 as a v2 replacement; moderation outcome not yet
recorded.**  The 20-page v5.5 edition of *The Row Sums Were the Method, Not the
Theorem: a Machine-Checked Chain from a Positive Weight to Exponential Decay
of Correlations, and a Misattributed Uniformity Wall* was sent to viXra.  The
exact PDF is pinned at paper commit [`e68b821f7`](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/e68b821f7b5a766551c7e249706aaf7dc4d0eb66/papers/dobrushin-matrix/dobrushin_matrix.pdf)
and has SHA-256
`3A0DDBCDB60E7E5A2EAA33E1A5D458312FEBE0B46F3A5481FA5287BF09E21888`.
See the [submission record](docs/DOBRUSHIN-MATRIX-V2-SUBMISSION-20260803.md)
for the clean-clone build, oracle evidence, superseded edition, and exact scope.

The paper/source commits remain on remote branch `d3-closure`; this notice does
not claim that the lane is integrated into `main`, and it does not alter the
canonical proof-state DAG or the recorded distance to the Clay problem.

---

## Method

The project advances in **campaigns**: a design document with a brick ladder
(`docs/*-PLAN.md`), one brick proved per session, every brick oracle-checked
before the next, the ledger updated at every green checkpoint. Hard-won
Lean/Mathlib engineering notes (heartbeat hangs, elaboration-order traps,
instance seams) are recorded in the plan of the campaign that hit them, so they
are never paid for twice.


---

## The notes series (July 2026): the Bessel/surface track

Four short, adversarially-reviewed notes, each with completed Lean verification
(standard axiom oracle, zero `sorry`), live in [`papers/`](papers/):

| Note | Folder | Core result |
|---|---|---|
| Bessel-Amos / F-H 2D | [`papers/bessel-amos-fh`](papers/bessel-amos-fh) | unit-step order-monotonicity of (log I_nu)' via the exactly calibrated Amos bound; all 2D Wilson sector gaps strictly decreasing in beta |
| Parity Barriers | [`papers/parity-barriers`](papers/parity-barriers) | no certifying bounded-order comparison inequality exists (parametric-in-r Lean) |
| phi-lemma | [`papers/phi-lemma`](papers/phi-lemma) | weighted Turan-type monotonicity => determinant ordering c_mn < 0 of the pi-local surface expansion |
| Wronskian reduction | [`papers/wronskian-reduction`](papers/wronskian-reduction) | the surface double sum IS a Wronskian; the asterisk = global sine-series ratio monotonicity; naive route provably dead |

**Closed theorem (2026-07-28).**  The definitive 33-page manuscript
[`papers/surface-complete/surface_theorem_complete.pdf`](papers/surface-complete/surface_theorem_complete.pdf)
proves the global ratio-monotonicity statement
`F_B(t)>0` and `(F_A/F_B)'(t)<0` for every `beta>0` and `0<t<pi`.
Its exact bridge identities, interval certificates, production/replay
transcripts, and executable terminal seal are archived in this repository.
The executable gate state is summarized in
[`docs/SURFACE-CLOSURE-GATES.md`](docs/SURFACE-CLOSURE-GATES.md).
The T1 zero-scan incident and its permanent executable repair are recorded in
[`docs/incidents/INC-T1-ZERO-SCAN.md`](docs/incidents/INC-T1-ZERO-SCAN.md).
The older [`surface-theorem/`](surface-theorem/) material is the historical
partial-stage record and is superseded for theorem status by
[`papers/surface-complete/`](papers/surface-complete/).  This is a
two-dimensional Bessel/surface result; it is not a claim of a
four-dimensional continuum Yang--Mills mass gap.

Warning for numerical work: the parity-mirror cancellation is approximately
`exp(-2.1 beta)`; use at least `2.2 beta + 20` working digits or the sign is
rounding noise.
## License

GNU Affero General Public License v3.0 — see [`LICENSE`](LICENSE). © 2026 Lluis Eriksson.
