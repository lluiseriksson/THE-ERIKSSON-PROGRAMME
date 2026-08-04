# OS-R PRIORITY COLLATION (2026-08-04, four independent web sweeps)

Charter step: collate the external-priority claim BEFORE any abstract
says "first" (HANDOFF-OS-R.md section 4 item 5; Add. 607/608).  Four
independent search agents ran in parallel (Lean ecosystem; Isabelle/
Coq; literature+own trace; adjacent-work referee sweep).  Raw reports
are appended verbatim as evidence.  Synthesis and claim rulings below
are this desk's; the conservative reading across agents governs.

## RULINGS ON CLAIM LANGUAGE

DEAD -- do not print, a referee kills each in one citation:
* "first machine-checked OS reconstruction" (unqualified).
  mrdouglasny/reflection-positivity (sorry-free ~2026-06) already
  machine-checks the abstract construction: RP data -> physical
  Hilbert space (completion/quotient) -> self-adjoint contractive
  transfer operator, with trace formulas.  xiyin137/OSreconstruction
  attempts the full OS<->Wightman theorem (incomplete: 53 sorries +
  12 axioms at last README snapshot).
* "first machine-checked reflection positivity / OS axioms".
  OSforGFF (arXiv:2603.15770, 2026-03): all five GJ/OS axioms for the
  d=4 Gaussian free field, 0 sorries after community forks.
* "first formalized Dobrushin uniqueness".  mrdouglasny/lgt
  (complete 2026-05-04, 0 sorries): Chatterjee-style Dobrushin
  uniqueness for lattice Yang-Mills on a periodic torus, U(n), d>=2,
  with exponential clustering ym_mass_gap_rate_exists (constants
  depend only on (n,d,beta), N fixed outside the exists -- de facto
  volume-uniform clustering, NOT an operator gap, no reconstruction).
  NOTE: our dobrushin-matrix paper is SAFE -- its prior-work section
  already declines the first-formalisation claim (line ~1381) -- but
  any revision should cite lgt explicitly.

ALIVE -- the wording that survives today's evidence:
* "first machine-checked VOLUME-UNIFORM spectral gap of a concrete,
  reconstructed transfer operator": the gap PROVED (not carried as a
  hypothesis) for a concrete interacting model, ONE m > 0 for every
  spatial extent, identified through the OS/site construction with
  the measure's correlations.  Nothing found carries all three of
  {concrete model, proved gap, volume-uniform} on the reconstructed
  side: reflection-positivity's GappedTransfer packages the gap as a
  HYPOTHESIS ("gap inheritance"), never discharged for any concrete
  model, and has no spatial-volume-uniform statement; lgt's decay is
  measure-side clustering without operator/reconstruction content;
  pphi2's transfer-matrix spectral machinery sits under 27-29 project
  axioms.  The claim must be printed WITH the explicit comparison
  table, drawing the line ourselves before a referee does.

## INTER-AGENT CONFLICT, RESOLVED
The adjacent-work agent reported "Dobrushin uniqueness: empty in any
prover" and ruled "first machine-checked OS reconstruction survives
if worded as reconstruction".  Both are OVERTURNED by the Lean-agent's
deeper repo-level findings (lgt; reflection-positivity).  Lesson kept:
a negative from one search modality is never evidence against a
positive from another; the union governs.

## STRATEGIC NOTE FOR THE OWNER
There is a coordinated, active Harvard programme (M. R. Douglas, CMSA
+ Xi Yin; event 2026-05-06 "Formalization of QFT") whose declared
LIVE fronts are exactly: the OS reconstruction theorem, P(phi)_2, and
YM mass gap at strong coupling.  Their framework carries the spectral
gap as an undischarged hypothesis (GroundGap.lean).  Our OS-R endpoint
is precisely a concrete discharge of that shape (different framework,
same mathematical hole).  This raises the value of shipping OS-R
promptly and citing their repos generously -- and it means the niche
will not stay open long.  Toolchain note: they are on Mathlib
v4.30.0; we are pinned to v4.29.0-rc6 -- citation only, no interop.

Our own public trace confirmed: ai.viXra 2607.0078 (os-chain-z2,
zero extension, explicitly non-volume-uniform) plus the 2607.00xx
cluster -- currently the only public machine-checked lattice-gauge
OS-side chain, which is why the INTERNAL headline is spent but the
volume-uniform claim is fresh.

---



# APPENDIX A -- Lean ecosystem sweep

# Lean formalizations of OS reconstruction / reflection positivity / CQFT — survey results (2026-08-04)

There IS an active ecosystem, essentially all of it from one cluster (Michael R. Douglas, Harvard CMSA + Xi Yin, Harvard), created Jan–Jul 2026. Findings by your (a)/(b)/(c) taxonomy, then negatives per query.

## Positive hits

**1. `mrdouglasny/OSforGFF` + arXiv:2603.15770 "Formalization of QFT" — category (a): OS axioms verified for a concrete measure; NO reconstruction**
- URLs: https://github.com/mrdouglasny/OSforGFF , https://arxiv.org/html/2603.15770v1
- Authors: Douglas, Hoback, Mei, Nissim. Paper March 2026; repo v2.0 March 2026 (~32,000 lines, 47 files, 0 sorries, 0 axioms after community forks `or4nge19/OSforGFF` and `mrdouglasny/gaussian-field` eliminated the Minlos/nuclearity/Goursat axioms of v1).
- Formalized: Gaussian Free Field in d=4 as a measure on S'(R^4) via Minlos; all five Glimm–Jaffe/OS axioms OS0–OS4 including reflection positivity as an inequality (`OSforGFF/OS/Axioms.lean`).
- NOT there: reconstruction, GNS quotient, transfer operator, any spectral gap. The paper lists OS reconstruction as "next milestone".

**2. `xiyin137/OSreconstruction` — category (c) attempt: full OS↔Wightman reconstruction, INCOMPLETE**
- URL: https://github.com/xiyin137/OSreconstruction (mirror: `mrdouglasny/OSreconstruction-1`). Last updated 2026-06-24; 1,085 commits; Apache 2.0.
- Scope: both directions. GNS construction from Wightman functions (`Wightman/Reconstruction/GNSConstruction.lean`, theorem `wightman_reconstruction` — **proved**); `wightman_to_os` (R→E via Wick rotation); `os_to_wightman` (E→R via OS-II semigroup + tube-domain analytic continuation, Bargmann–Hall–Wightman, SNAG spectral measures); von Neumann algebra lane.
- Status (README snapshot 2026-05-10): **53 sorries + 12 explicit axioms** (3 functional analysis, 7 several-complex-variables/tube domains, 1 reconstruction bridge, 1 spectral). E→R blocked at `OSToWightmanBoundaryValues.lean` (locality + cluster frontiers); R→E blocked at a Ruelle cluster dominator estimate. So: the theorem is NOT complete in Lean; the Wightman-side GNS lane is the proved part.
- No transfer operator or volume-uniform gap statements; "spectral" here means the relativistic spectrum condition.

**3. `mrdouglasny/reflection-positivity` — category (b) exactly: GNS-style Hilbert space + transfer operator; gap is a HYPOTHESIS**
- URL: https://github.com/mrdouglasny/reflection-positivity . OS stack sorry-free as of 2026-06-03 (headlines axiom-clean `[propext, Classical.choice, Quot.sound]`); last updated 2026-07-20. Mathlib v4.30.0 only.
- Construction verified in-source: `ReflectionSystem` (measure, involution θ, positive-time sub-σ-algebra, RP property) → reflection form B(f,g)=∫f·(g∘θ)dμ via `InnerProductSpace.ofCore` → `physicalHilbertSpace := UniformSpace.Completion S.PosObs` (completion separates the null space, i.e. quotient+completion in one step). `TimeTranslatedSystem` adds τ with the OS relation τ∘θ∘τ = θ; transfer operator defined as completion of composition-with-τ; **self-adjointness and contraction PROVED** (`transferOperator_selfAdjoint`, `norm_transferOperatorLinear_le`); dictionary `reflectionCorrelation_eq_inner_T_pow`: ⟪[f],Tⁿ[g]⟫ = ∫f·(g∘τⁿ∘θ)dμ; Feynman–Kac trace formulas (`partition_eq_trace`); variance/susceptibility bounds from gap (`Var ≤ ‖f‖²/(1−gap)`, `connected_susceptibility_le`).
- Critical caveat: the spectral gap enters as a field of a `GappedTransfer` structure (`GroundGap.lean` — "packages only the data needed for gap inheritance"). **The gap is never proved for any concrete model.** The only concrete instantiation (`LatticeInstance.lean`) proves reflection positivity for finite-lattice even ferromagnetic nearest-neighbour Gibbs measures via Hubbard–Stratonovich — RP only, fixed finite ι, no gap, no thermodynamic limit.
- Uniformity: susceptibility bounds are uniform in TIME extent (Nt→∞ cylinder / periodic wrap). **No spatial-volume-uniform gap statement anywhere.**

**4. `mrdouglasny/lgt` — lattice Yang–Mills mass gap at strong coupling: correlation decay, NOT an operator gap**
- URL: https://github.com/mrdouglasny/lgt . Complete as of 2026-05-04 (0 sorries, 0 project axioms, independently comparator-verified); last updated 2026-07-27.
- Formalized: Wilson action, YM measure via Haar + withDensity on periodic torus (Z/NZ)^d, DLR/Gibbs specification, Dobrushin uniqueness (Chatterjee-style), for U(n), d≥2, N>2, β < 1/(4n·maxNeighbors d).
- I pulled the exact signatures (`LGT/MassGap/StrongCoupling.lean` lines 2049, 2180): `ym_mass_gap_exponential_decay` bounds |connected2pt(p,q)| ≤ 32n²/(1−α)·α^((dist−1)/2), and `ym_mass_gap_rate_exists` gives `∃ m>0, ∀ plaq p q, |connected2pt| ≤ 32n²/(α(1−α))·exp(−m·dist)` with α = `dobrushinAlpha n d β`. **N is fixed outside the ∃m**, so it is stated per-volume — but the witness is m = (−log α)/2 and α, the prefactor, and the β-window depend only on (n,d,β), never on N. De facto volume-uniform clustering; not packaged as a uniform statement, and explicitly NOT a spectral gap of a transfer operator (no transfer matrix, no character expansion, no GNS space in the repo).

**5. `mrdouglasny/pphi2` — φ⁴₂/P(φ)₂ construction with transfer-matrix spectral machinery, conditional**
- URL: https://github.com/mrdouglasny/pphi2 . Updated 2026-07-21. 0 sorries but **27–29 project axioms** (audited in `AXIOM_AUDIT.md`).
- Contains lattice transfer-matrix positivity and spectral-gap machinery (Jentzsch/Perron–Frobenius), OS0–OS4 targets on four spacetime routes; headline `pphi2_existence` (R², OS0–OS4) rests on 5 named axioms incl. Fröhlich-1976/Park-1977 tightness; torus non-Gaussianity result is axiom-free; RP (OS3) discharged 2026-07-21 via link-reflection. No OS reconstruction. Companion incomplete effort: https://github.com/xiyin137/Phi4 (21 core sorries, 2026-03-10).

**6. Mathlib proper — abstract GNS only, nothing OS**
- GNS construction for C*-algebras **merged into mathlib** 2026-01-09: PR https://github.com/leanprover-community/mathlib4/pull/33116 → `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`, `.../GNS.lean` (decls `GNS`, `PreGNS`, `gnsStarAlgHom`); author Gregory Wickham (Harvey Mudd senior thesis; NYC Lean talk 2026-06-07, https://lean.nyc/blog/formalizing-the-gns-construction ). State-on-C*-algebra → Hilbert space + representation; no reflection positivity, no QFT content.
- No "reflection positivity" or Wightman/Osterwalder declarations found in mathlib itself by any query.

**7. Programme context**
- Harvard event 2026-05-06 (https://www.math.harvard.edu/event/formalization-of-qft/): Douglas + Hoback/Mei/Nissim/Cipollina/Yin declare completed = free field + OS axioms; **in progress = OS reconstruction theorem, P(φ)₂, and "Yang–Mills mass gap at strong coupling"** — i.e. items 2, 4, 5 are the live fronts of a coordinated programme, active as of late July 2026.
- Peripheral: arXiv 2606.07922 (finite-lattice reciprocal-cost model) ships Lean files checking only elementary algebraic claims; its RP core is text-only. PhysLean (https://github.com/HEPLean/PhysLean) has perturbative QFT (Wick's theorem) but no Wightman/OS/RP content.

## Negative results, per query
- "Lean 4 formalization Osterwalder-Schrader reconstruction theorem": positives above; no completed reconstruction anywhere.
- "reflection positivity mathlib Lean": no mathlib hit; only the repos above + arXiv 2606.07922's decorative Lean files.
- "Wightman axioms Lean formalization": no hits beyond the Yin/Douglas cluster; nLab/physics only.
- Zulip (3 query variants: `site:leanprover.zulipchat.com Osterwalder…`, `"zulipchat" lean "quantum field theory"…`, `"leanprover.zulipchat.com" OSforGFF OR Minlos…`): **zero indexed threads** — current Zulip content is not search-indexed and the public HTML archive ends ~2021 (its "Formal treatment for physics" topic predates all of this); native Zulip search not accessible from here. Absence of indexed threads ≠ absence of threads.
- "Lean 3" + any of these terms: nothing found in any query; all activity is Lean 4/2026.
- **Volume-uniform spectral gap of a transfer operator on a GNS/quotient Hilbert space: found NOWHERE.** Closest existing objects: reflection-positivity repo (operator + gap-as-hypothesis, time-extent-uniform bounds only) and lgt (N-independent Dobrushin decay rate, but correlation-form, per-volume statement, no operator).

Direct relevance to the OS-R campaign: the combination this repo's OS-R charter targets — site-form GNS transported transfer operator WITH a proved volume-uniform gap — does not exist in any published Lean artifact found. The nearest competitor infrastructure is `mrdouglasny/reflection-positivity` (same architectural shape, gap unproved) and it is actively developed (last push 2026-07-20), as is `lgt`, which uses the same Dobrushin method as this repo's D-lane.

Sources: [arXiv 2603.15770](https://arxiv.org/html/2603.15770v1) | [OSforGFF](https://github.com/mrdouglasny/OSforGFF) | [OSreconstruction](https://github.com/xiyin137/OSreconstruction) | [reflection-positivity](https://github.com/mrdouglasny/reflection-positivity) | [lgt](https://github.com/mrdouglasny/lgt) | [pphi2](https://github.com/mrdouglasny/pphi2) | [Phi4](https://github.com/xiyin137/Phi4) | [mathlib4 PR #33116](https://github.com/leanprover-community/mathlib4/pull/33116) | [NYC Lean GNS](https://lean.nyc/blog/formalizing-the-gns-construction) | [Harvard event](https://www.math.harvard.edu/event/formalization-of-qft/) | [arXiv 2606.07922](https://arxiv.org/pdf/2606.07922) | [PhysLean](https://github.com/HEPLean/PhysLean)


# APPENDIX B -- Isabelle/Coq sweep

FINDINGS: Isabelle/HOL (AFP) and Coq/Rocq formalizations of OS reconstruction, reflection positivity, axiomatic/constructive QFT, lattice transfer operators, GNS-for-EQFT. Search date 2026-08-04.

## BOTTOM LINE

There is NO peer-reviewed or archive-published formalization of Osterwalder–Schrader reconstruction, reflection positivity, Wightman axioms, or Euclidean QFT in Isabelle/HOL (AFP) or Coq/Rocq. The AFP's entire Physics topic contains only relativity axiomatics and quantum information; the Rocq package index contains nothing in this area. The one Coq-language artifact that touches RP/OS/transfer operators is an unreviewed, partly vacuous GitHub repo (detailed below). The only genuine machine-checked constructive-QFT result anywhere is in Lean 4 (out of the requested provers, reported as context). The Lean authors themselves state (arXiv 2603.15770, §1.5): "we know of no previous formalizations of constructive QFT."

## DIRECT HITS IN THE REQUESTED PROVERS

1. **github.com/Shariq81/yang-mills-mass-gap** — Coq 8.18 ("Rocq Prover" per GitHub), created 2026-02-17, last push 2026-02-23, 2 stars, author signature "APEX" (reads AI-generated). Claims "first complete machine-verified formalization of the Yang-Mills mass gap theorem," conditional on a "Balaban Pointwise Convergence" research hypothesis plus interface assumptions. Verified scope by reading source:
   - `coq/reflection_positivity.v` (dated 2026-02-19): a genuine-looking generic lattice RP statement — OS inner product `Expect(ΘF·G)` with Boltzmann weight `exp(-wilson_action)`, Haar product over links, time reflection — but proved over an AXIOMATIZED typeclass interface (`HeatKernelPosDef G`, `HaarIntegral G`), and per its own `ASSUMPTIONS_CONTRACT.md` even `plaquette : Type` and the geometry/cluster "frontier instances" are assumptions, i.e. the lattice is axiomatized, not constructed.
   - `coq/os_axioms_complete.v` (2026-02-22, "Target: Clay Millennium Problem"): contains literally vacuous lemmas — e.g. `Lemma os0_lattice_analyticity : True. Proof. trivial. Qed.` The "All 5 OS axioms verified" claim in the README is false in the load-bearing sense; there is no OS reconstruction here.
   - `coq/rp_to_transfer.v` (2026-02-21): RP → transfer-matrix positivity → gap, but the Hilbert space, inner product, and transfer operator `T` are all `Variable`/`Hypothesis` — an abstract conditional skeleton.
   - Verdict: the only Coq artifact in existence touching RP/OS/lattice transfer operators; unreviewed, headline drastically overclaims, key OS-axiom file vacuous, everything conditional on axiomatized interfaces. Not on the Rocq/Coq package index, not on arXiv.

No Isabelle/HOL direct hit exists at all.

## NEAR-MISSES (explicitly NOT OS reconstruction)

2. **AFP: "The Gelfand–Naimark–Segal Construction"** — Richard Schmoetten, Jacques D. Fleuriot, 2026-03-09. https://www.isa-afp.org/entries/Gelfand_Naimark_Segal.html. Machine-checked: C*-algebras (class + locale), states, GNS Hilbert space and bounded-operator representation. Verified against entry page: purely operator-algebraic; zero mention of QFT, Euclidean fields, OS, RP, or Wightman. This is the operator-algebra GNS near-miss the task warned about — it provides the algebraic half of an OS-reconstruction toolchain in Isabelle but none of the Euclidean-field content (no reflection, no Schwinger functions, no quotient by the RP null space of a field-theoretic form).
3. **AFP: "Ergodic Theory"** — Sébastien Gouëzel, 2015-12-01. https://www.isa-afp.org/entries/Ergodic_Theory.html. Contains a `Transfer_Operator` theory — the dynamical-systems (Ruelle/Koopman-dual) transfer operator of a measure-preserving map. NOT a lattice-QFT transfer matrix; no Gibbs measures, no statistical mechanics.
4. **AFP: "Perron-Frobenius Theorem for Spectral Radius Analysis"** — Divasón, Kunčar, Thiemann, Yamada, 2016-05-20. https://www.isa-afp.org/entries/Perron_Frobenius.html. Matrix PF via Brouwer; relevant background math for transfer matrices, no physics.
5. **AFP Physics topic (full census, 8 entries)** — https://www.isa-afp.org/topics/mathematics/physics/ : GNS (above), gyrovector spaces, Malament-Hogarth halting, No-FTL-observers (×2), Schutz Minkowski axioms (2021 — spacetime geometry axiomatics, not QFT), physical units, safe-distance traffic. Quantum-information subtopic (8 entries: Isabelle Marries Dirac 2020, CHSH ×2, uncertainty principle, QFT-transform 2025, Kraus maps 2025, O2H 2025, compressed oracles 2025): all finite-dimensional quantum computation/information. Nothing QFT.
6. **Coq quantum-computing stack** — CoqQ (github.com/coq-quantum/CoqQ; finite-dim Hilbert spaces over MathComp, quantum program verification, arXiv 2207.11350), QWIRE/QuantumLib, DiracRepr: all finite-dimensional QC, no field theory.

## ADJACENT (Lean 4 — outside the requested provers, but decisive landscape context)

7. **"Formalization of QFT"** — Douglas, Hoback, Mei, Nissim, arXiv:2603.15770, 2026-03-16, Lean 4/Mathlib. Free bosonic QFT on 4D Euclidean space, proof that it satisfies the Glimm–Jaffe axioms (a variant of the OS axioms), Minlos + nuclearity of Schwartz space now proved internally. This is the closest existing thing to a machine-checked OS-side EQFT; it verifies the OS AXIOMS for the free field, not the reconstruction theorem to Wightman theory. Explicitly states no prior constructive-QFT formalization exists in any prover.
8. **PhysLean: "Digitalizing Wick's theorem"** — Tooby-Smith, arXiv:2505.07939, 2025-05-12, Lean 4 (perturbative algebra, not axiomatic QFT). **Mathlib** also has the GNS construction (Lean; same near-miss class as item 2).

## QUERIES THAT RETURNED NOTHING RELEVANT (explicit negatives)

- `"Osterwalder-Schrader" formalization Isabelle/Coq/Rocq` (web): nothing.
- `"reflection positivity" formal proof Isabelle/Coq machine-checked` (web): only "proof by reflection" tooling noise.
- `"Wightman axioms" formalization proof assistant` (web): nothing (nearest: Schutz Minkowski axiomatics in Isabelle — spacetime, not QFT).
- `site:isa-afp.org` for quantum field / reflection positivity / Osterwalder / Wightman / Euclidean field: zero AFP hits.
- arXiv API, `cat:cs.LO AND "reflection positivity"`: **0 results** (totalResults=0).
- arXiv API, `("Wightman" OR "reflection positivity") AND (Isabelle|Coq|Rocq|Lean 4|proof assistant|machine-checked)`: 0 results.
- arXiv API, `cat:cs.LO AND ("quantum field"|"lattice gauge"|"Euclidean field theory")`: 8 hits, only the two Lean papers (items 7, 8) are formalizations; rest categorical/QC noise.
- `"GNS construction" Coq/Rocq`: nothing (GNS exists only in Lean/Mathlib and Isabelle/AFP, item 2).
- Rocq package index (rocq-prover.org/packages): no packages for physics, field theory, operator algebras, C*-algebras, spectral theory, or statistical mechanics.
- `"Ising model" / "Gibbs" / "transfer matrix"` formalization Isabelle/Coq: nothing (nearest: Lean 4 Hopfield/Boltzmann-machine ergodicity, arXiv:2512.07766, 2025-12-08 — finite Markov chains, not lattice field theory).
- `"Schwinger functions" / "Euclidean field theory"` + Isabelle/HOL: nothing.
- `"lattice gauge theory" / "Yang-Mills"` formalization Isabelle/Coq: only item 1 (the unreviewed GitHub repo).

Method notes: AFP searched via topic index (https://www.isa-afp.org/topics/), full Physics and Quantum-Information topic listings, entry pages, and site-scoped web searches (the AFP FindFacts server search.isa-afp.org was unreachable from this environment — SSL error/empty response — so full-text AFP search was approximated by Google site-search plus the complete Physics-topic census). Coq index searched via rocq-prover.org/packages plus GitHub. arXiv searched via the export API with category filter cs.LO. Item 1's source files were read directly from raw.githubusercontent.com; item 2's scope from its AFP entry page; item 7's no-prior-work claim from the arXiv HTML full text.

Sources: [arXiv 2603.15770](https://arxiv.org/abs/2603.15770), [AFP GNS entry](https://www.isa-afp.org/entries/Gelfand_Naimark_Segal.html), [AFP Physics topic](https://www.isa-afp.org/topics/mathematics/physics/), [AFP Quantum information](https://www.isa-afp.org/topics/mathematics/physics/quantum-information/), [AFP Ergodic Theory](https://www.isa-afp.org/entries/Ergodic_Theory.html), [AFP Perron-Frobenius](https://www.isa-afp.org/entries/Perron_Frobenius.html), [Shariq81/yang-mills-mass-gap](https://github.com/Shariq81/yang-mills-mass-gap), [CoqQ](https://github.com/coq-quantum/CoqQ), [arXiv 2505.07939](https://arxiv.org/abs/2505.07939), [arXiv 2512.07766](https://arxiv.org/abs/2512.07766), [Rocq packages](https://rocq-prover.org/packages), [NYC Lean GNS blog](https://lean.nyc/blog/formalizing-the-gns-construction).


# APPENDIX C -- literature + own-trace sweep

## Web survey: machine-checked OS reconstruction / formalized EQFT / formalized transfer-matrix spectral gaps (2024–2026)

### A. External hits (not the Eriksson programme)

1. **arXiv:2603.15770 — "Formalization of QFT"** — Douglas, Hoback, Mei, Nissim; submitted 2026-03-16; Lean 4.
   - Claim: the free bosonic QFT in 4D Euclidean spacetime satisfies the **Glimm–Jaffe axioms (a variant of the OS axioms)**, machine-checked. Initially assumed Minlos, Schwartz nuclearity, and Goursat; later releases discharged all three, so the OS/GJ axioms are now proven from Lean+Mathlib alone.
   - Scope limits: **free field only; verifies the axioms, does NOT formalize the OS reconstruction theorem itself**. This is the closest external claim to "formalized Euclidean QFT" that exists.
   - URL: https://arxiv.org/abs/2603.15770

2. **HepLean / PhysLean / Physlib** — Joseph Tooby-Smith (Cornell); arXiv:2405.08863 (2024-05) + https://github.com/HEPLean/PhysLean and https://github.com/leanprover-community/physlib (merged with Lean-QuantumInfo, 2025–26).
   - Claim/scope: Lean 4 digitalization of physics — Wick's theorem in perturbative QFT, index notation (arXiv:2411.07667), some statistical mechanics, QM, particle physics. **No OS axioms, no reconstruction, no lattice gauge theory, no transfer-matrix spectral gap.** Related: Tooby-Smith perspective piece (Advanced Science, doi 10.1002/advs.202517294) and a 2026 report of an error in a widely-cited physics paper found via Lean.

3. **jazir555/Math-Proofs (GitHub)** — Lean 4 + Mathlib4, based on arXiv:2503.23758 (Weiguo Yin, 2025).
   - Claim: machine-checked **1D inhomogeneous lattice gas**: partition function via configuration sum = transfer-matrix trace; analyticity of free energy; thermodynamic derivative identities; claims sorry-free.
   - Scope limits: partition-function identities only — **no spectral gap, no QFT, no OS**; no external verification record (credibility: appears substantively complete but unaudited).
   - URL: https://github.com/jazir555/Math-Proofs

4. **arXiv:2607.07857 — Multi-agent autoformalization of tensor-network theory** (2026) — formalization blueprint for the fundamental theorem of matrix product states. Adjacent (transfer-operator-flavored quantum lattice math), not OS/QFT axioms.

5. **Near-miss, checked and negative:** arXiv:2606.07922 "A Finite-Lattice Model from a Reciprocal Cost Action: Spectral and Reflection-Positivity Properties" — reflection positivity + spectral analysis of a finite lattice model, but **ordinary mathematics**: Python verification scripts only, no proof assistant.

### B. The Eriksson programme's own public trace (ai.viXra, Mathematical Physics section)

The zero-extension OS chain prior **has a public trace**, verified by direct fetch of the abstract page:

- **ai.viXra:2607.0078 — "From the Gibbs Weight to the Spectral Gap: A Complete Machine-Checked Osterwalder-Seiler Chain for the Z_2 Lattice Gauge Chain"** — Lluis Eriksson, 2026-07-28, Lean 4 + Mathlib. Abstract confirms: spatial slice is a point (zero extension), 2×2 transfer operator, gap 1 − tanh β, mass −log tanh β; **fixed finite size, not volume-uniform; explicitly disclaims SU(N), continuum limit, and YM mass gap**. URL: https://ai.vixra.org/abs/2607.0078

Surrounding cluster surfaced on the section listing https://www.ai.vixra.org/mathph/ (single-fetch summary; only 2607.0078 independently verified against its own abstract page, though the IDs are consistent with known programme records): 2607.0130 (Z_N RP framework, Z2 Wilson instance, 07-27), 2607.0075 ("Where the Elementary Reconstruction Stops"), 2607.0076 (GNS quotient), 2607.0083/0084/0085 (transfer bridge / strict non-uniform gap / Perron), 2607.0088/0089, 2607.0090–0093 (endpoint RP, uniform tanh β modulus decoupled, operator bound, bond RP "The Collapse", 07-30/31), 2608.0013 (08-03), plus 2607.0039 (exact 2D SU(2) YM in Lean), 2607.0042/0043, 2607.0032 (Amos bound), 2607.0025 (polymer tree majorants).

### C. Queries that came up empty

- "machine-checked Osterwalder-Schrader" → **no external hit**; only classical OS literature plus arXiv:2603.15770 (axioms, not reconstruction). **No formalized OS reconstruction theorem exists anywhere as of 2026-08.**
- "os-chain-z2" as a search string → empty (blockchain/crypto noise only); the identifier itself has no public web trace — the public trace is the 2607.0078 title wording, not the internal name.
- Isabelle or Coq formalization of Wightman axioms / reflection positivity → empty.
- Isabelle AFP statistical mechanics / Gibbs measures → nothing surfaced (martingales, measure theory only).
- "Lean lattice gauge theory formalization" → nothing external beyond noise; the only machine-checked lattice-gauge material found is the Eriksson programme's own viXra cluster.
- Machine-checked reflection positivity for lattice gauge (excluding Eriksson) → only homonym hits (lattice-based **cryptography**, orthomodular lattices); no gauge-theory RP formalization.

### Bottom line
No one has formalized the OS reconstruction theorem in any proof assistant. The external state of the art is arXiv:2603.15770 (Lean 4, free field satisfies GJ/OS axioms, no reconstruction) and PhysLean (perturbative pieces). No external formalized transfer-matrix spectral gap exists in a QFT/gauge context (jazir555's repo stops at partition-function identities). The Eriksson programme's ai.viXra 2607.00xx cluster is currently the only public machine-checked lattice-gauge OS-side chain (zero extension, Z2, explicitly non-volume-uniform).

Sources:
- [arXiv:2603.15770 — Formalization of QFT](https://arxiv.org/abs/2603.15770)
- [HepLean arXiv:2405.08863](https://arxiv.org/pdf/2405.08863)
- [PhysLean GitHub](https://github.com/HEPLean/PhysLean)
- [physlib GitHub](https://github.com/leanprover-community/physlib)
- [Tooby-Smith, Advanced Science perspective](https://advanced.onlinelibrary.wiley.com/doi/10.1002/advs.202517294?af=R)
- [jazir555/Math-Proofs](https://github.com/jazir555/Math-Proofs)
- [arXiv:2607.07857 — tensor network autoformalization](https://arxiv.org/pdf/2607.07857)
- [arXiv:2606.07922 — Reciprocal Cost Action (not formalized)](https://arxiv.org/pdf/2606.07922)
- [ai.viXra:2607.0078 — Eriksson OS-Seiler chain Z2](https://ai.vixra.org/abs/2607.0078)
- [ai.viXra Mathematical Physics listing](https://www.ai.vixra.org/mathph/)
- [Isabelle AFP](https://isa-afp.org/)


# APPENDIX D -- adjacent-work referee sweep (its Dobrushin negative and its verdict are superseded -- see rulings)

FINDINGS — formal work adjacent to a "first machine-checked OS reconstruction" claim (searched 2026-08-04; all via public web index)

## 1. THE dangerous citation: free-field OS/Glimm–Jaffe axioms in Lean 4
- **Douglas, Hoback, Mei, Nissim, "Formalization of QFT"** — https://arxiv.org/abs/2603.15770 (submitted 2026-03-16), Lean 4, repos `mrdouglasny/OSforGFF` (+ `gaussian-field`, `bochner`).
- Exact scope: constructs the free massive scalar (Gaussian) Euclidean QFT in d=4 and proves the five Glimm–Jaffe axioms **OS0 analyticity, OS1 regularity, OS2 Euclidean invariance, OS3 reflection positivity, OS4 ergodicity** for the generating functional; earlier assumptions (Minlos, nuclearity of Schwartz space, Goursat) now proven or avoided — axioms hold from Lean+Mathlib alone.
- Why it is NOT an OS reconstruction: it verifies the **Euclidean axioms for one measure**; the OS reconstruction theorem (Hilbert space / Hamiltonian / Wightman functions from Euclidean data) is **explicitly listed as future work** in the paper. But it IS a machine-checked **reflection positivity** proof, so any priority claim must say "reconstruction" (building the physical Hilbert space and transfer/Hamiltonian structure from RP data), never "first machine-checked OS positivity" or "first machine-checked OS axioms."

## 2. Perron–Frobenius, formalized (three times)
- **Isabelle AFP `Perron_Frobenius`** (Divasón, Kunčar, Thiemann, Yamada, May 2016) — https://www.isa-afp.org/entries/Perron_Frobenius.html — PF for nonnegative real matrices incl. peripheral spectrum/reducible case, via Brouwer; built for spectral-radius/complexity certification. Matrix-level linear algebra; no measures, no reconstruction.
- **Isabelle AFP `Stochastic_Matrices`** (Thiemann, Nov 2017) — https://isa-afp.org/entries/Stochastic_Matrices.html — stationary distributions of stochastic matrices via PF. Same verdict.
- **Lean 4: Cipollina, Karatarakis, Wiedijk, "Formalized Hopfield Networks and Boltzmann Machines"** — https://arxiv.org/abs/2512.07766 (2025-12-08) — claims **first PF in Lean 4** (irreducibility via strong connectivity of the associated quiver, proven equivalent to the algebraic characterization), used to prove ergodicity/unique stationary distribution of Boltzmann-machine dynamics. Finite-state, matrix-based; no Gibbs specification, no OS structure.

## 3. The known "Ising" formal work — pinned
The closest existing formal Ising work is the **Boltzmann machine paper above**: a Boltzmann machine is exactly a finite Ising-type energy function with stochastic (Glauber-style) dynamics, and what is proved is **ergodicity + convergence to the unique stationary (Gibbs) distribution of a finite-state Markov chain** via their new PF. Scope is therefore: finite state space, dynamics/ergodicity — **not** free energy, not correlation inequalities, not transfer-matrix spectral gap, not infinite volume, not phase transition. Direct searches for Ising in AFP (Ising/Potts/partition function), Lean/mathlib/Zulip, and Coq returned **nothing else** — no formalized free energy, no Onsager, no transfer-matrix spectral gap outside the user's own repository. (Referee risk is that this paper is cited as "the Ising model has been formalized"; its actual scope is dynamics ergodicity of finite networks.)

## 4. Spectral gap of Markov/transfer operators
- **Isabelle AFP `Expander_Graphs`** (Karayel, 2023-03-03) — https://isa-afp.org/entries/Expander_Graphs.html — spectral gap definitions for random walks on finite graphs, Cheeger's inequality, random-walk tail bounds, Margulis–Gabber–Galil construction. Finite combinatorial walks; no transfer operator on a state space of a field theory, no reconstruction.
- **Isabelle AFP `Markov_Models`** (Hölzl, Nipkow, 2012-01-03) — https://www.isa-afp.org/entries/Markov_Models.html — DTMCs, MDPs, pCTL model checking; **no spectral theory at all**.
- **Isabelle AFP `Ergodic_Theory`** (Gouëzel, 2015-12-01) — https://www.isa-afp.org/entries/Ergodic_Theory.html — Poincaré recurrence, Kac, Birkhoff, Kingman, Gouëzel–Karlsson; qualitative ergodic theorems, **no spectral gap of transfer operators** (Gouëzel never formalized his own transfer-operator spectral theory).
- Lean/mathlib: no Ruelle/transfer-operator spectral gap found — **empty**.

## 5. Reflection positivity in any system
- Real instance: **Douglas et al. OS3** (item 1) — Gaussian measure RP, machine-checked.
- **Washburn, "A Finite-Lattice Model from a Reciprocal Cost Action: Spectral and Reflection-Positivity Properties"** — https://arxiv.org/abs/2606.07922 (June 2026), repo `jonwashburn/shape-of-logic` — the paper **itself states** the RP analytic core is text-only; only elementary algebraic lattice facts are in Lean. Not a machine-checked RP; citable only carelessly.

## 6. Gibbs measures / DLR
- **`YaelDillies/GibbsMeasure`** (Lean 4, following Georgii, active, ~196 commits, upstreaming to Mathlib) — https://github.com/YaelDillies/GibbsMeasure — **definition** of specifications/Gibbs measures (DLR form); by its own README "no construction yet": no existence, no uniqueness, no phase transition. Definitions only; not a reconstruction and not even an existence theorem.
- Isabelle/Coq DLR: **empty**.

## 7. Dobrushin uniqueness
Targeted search ("Dobrushin uniqueness/condition" + mechanized/formalized/machine-checked): **empty** — nothing in any proof assistant outside this repository's own D-lane.

## 8. Other adjacent items a referee might reach for
- **PhysLean, "Digitalizing Wick's theorem"** (Tooby-Smith) — https://arxiv.org/abs/2505.07939 (May 2025), Lean 4 — perturbative/normal-ordered Wick's theorem in an operator algebra (52 files, 929 lemmas); purely algebraic/perturbative, no measure, no positivity, no reconstruction.
- **Kytölä, "Virasoro algebra and Sugawara constructions formally in Lean"** — https://arxiv.org/abs/2510.21741 (Oct 2025) — algebraic CFT representation theory; no analytic continuation or Hilbert-space reconstruction from Euclidean/lattice data.
- Measure-construction infrastructure (context, not competitors): Ionescu-Tulcea in Mathlib https://arxiv.org/abs/2506.18616; Brownian motion in Lean https://arxiv.org/abs/2511.20118.

## Empty queries (reported as instructed)
- Ising in AFP / Lean / Coq beyond item 3: empty.
- FKG / Griffiths / correlation inequalities formalized: empty.
- Mixing time / Glauber dynamics formally verified: empty.
- OS **reconstruction** itself in any proof assistant: empty — Douglas et al. explicitly defer it.
- Wightman axioms formalized: empty (only the Euclidean side above).
- Dobrushin uniqueness, DLR in Isabelle/Coq: empty.

## Verdict for the priority claim
"First machine-checked OS reconstruction" survives IF worded as reconstruction (transfer operator / Hilbert space / gap from reflection-positive lattice data). It does NOT survive as "first machine-checked OS axioms/reflection positivity" (Douglas–Hoback–Mei–Nissim, Mar 2026) nor as "first formal Perron–Frobenius / spectral gap" (AFP 2016/2023, Lean Dec 2025) nor as "first formal contact with Ising-type models" (Boltzmann-machine ergodicity, Dec 2025). Recommended: cite 2603.15770 and 2512.07766 explicitly in related work and draw the reconstruction/axiom-verification line yourself before a referee does. Caveat: web index is US-only and shallow for Zulip/repo-level work; the related-work sections of 2603.15770 and 2512.07766 are the right place to double-check for anything unindexed.

Sources: [arXiv:2603.15770](https://arxiv.org/abs/2603.15770), [AFP Perron_Frobenius](https://www.isa-afp.org/entries/Perron_Frobenius.html), [AFP Stochastic_Matrices](https://isa-afp.org/entries/Stochastic_Matrices.html), [arXiv:2512.07766](https://arxiv.org/abs/2512.07766), [AFP Expander_Graphs](https://isa-afp.org/entries/Expander_Graphs.html), [AFP Markov_Models](https://www.isa-afp.org/entries/Markov_Models.html), [AFP Ergodic_Theory](https://www.isa-afp.org/entries/Ergodic_Theory.html), [arXiv:2606.07922](https://arxiv.org/abs/2606.07922), [GibbsMeasure repo](https://github.com/YaelDillies/GibbsMeasure), [arXiv:2505.07939](https://arxiv.org/abs/2505.07939), [arXiv:2510.21741](https://arxiv.org/abs/2510.21741), [arXiv:2506.18616](https://arxiv.org/abs/2506.18616), [arXiv:2511.20118](https://arxiv.org/abs/2511.20118)
