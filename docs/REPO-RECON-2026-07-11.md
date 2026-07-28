# REPO RECONNAISSANCE — 2026-07-11 (18 repos, owner lluiseriksson)

Desk: mathematical reconnaissance (survey session; no fabrication, no audit
role claimed). Method: shallow clones (depth 1) of 17 public repos into
`C:\Users\lluis\AppData\Local\Temp\claude\repo-survey\`; the mother repo read
from the local push2 clone (CLAUDE.md Parts I+II and `docs/` only, per
instruction). Every Lean repo was text-scanned for `sorry` / `axiom`
(three hits found, all three false positives inside comments — verified by
context). NO repo was independently rebuilt with `lake build` in this
session; where a build claim is repeated below, its witness is a committed
oracle log, CI run id, or ledger entry, and it is labeled as such. In the
Part-I tricotomy the correct label for everything below is at best
"verified" (machine-checked elsewhere, witnesses committed), never upgraded
here.

Label conventions used in this file:
- **[oracle-logged]** — a committed `#print axioms` log or CI run id showing
  `[propext, Classical.choice, Quot.sound]` exists in the repo.
- **[text-clean]** — zero `sorry`/`axiom` at text level, confirmed this
  session; no committed oracle seen for the specific declaration.
- **[hypothesis-carried]** — the statement is honest but conditional: the
  analytic content enters as named theorem arguments or structure fields.
- **[interface-only]** — theorem is a field projection from a hypothesis
  package; the name promises more than the proof contains (flagged where the
  naming is aggressive).

---

## PART A — PER-REPO INVENTORY

### 1. THE-ERIKSSON-PROGRAMME (mother; local clone, docs/ + CLAUDE.md only)

- **Stack:** Lean 4 (v4.29.0-rc6) + Mathlib pinned `0764272...`; Python
  (mpmath, sympy, python-flint/Arb) for the Part-I paper track; TeX.
- **Strongest artifacts:**
  - *Part II (YM Lean):* core at ~8369 jobs, zero sorry, zero project
    axioms (ledger claim). Headline: `normalized_exp_wilson_loop_area_law`
    (`L1_GibbsMeasure/RestrictedGate.lean`) — volume-uniform area law for the
    TRUE Wilson factor `∏ exp(z_p)`:
    `‖(∫ tr W_C·∏exp(z_p))/Z‖ ≤ N_c·e^{#loopSupp·4d·K}·σ^{Area(C)}·e^{#loopSupp·4d·S(σ)}`,
    all constants volume-free, no integrability hypothesis families
    (Addenda 18–18d). Non-vacuity audited (17t). [oracle-logged per ledger]
  - *Part I (Surface Theorem paper track):* (i) `F_B > 0` on `(0,π)` proved
    twice; (ii) `E' < 0` proved for `0 < β ≤ 3.5` **conditional only on the
    φ-lemma**, whose Lean core `phi_step_of_recurrences` is machine-checked
    [oracle-logged in acta] with the Bessel inputs as NAMED HYPOTHESES:
    ```lean
    theorem phi_step_of_recurrences (m b R0 R1 R2 : ℝ)
        (hm : 1 ≤ m) (hb : 0 < b) (_hR0 : 0 < R0) (hR1 : 0 < R1)
        (hrec1 : 1 / R0 = R1 + 2 * m / b)
        (hrec2 : R2 = 1 / R1 - 2 * (m+1) / b)
        (hAmos : R1 < b / (m + 1/2 + Real.sqrt ((m + 1/2) ^ 2 + b ^ 2))) :
        ((m-1)/R0^2 + (m+1)*R1^2) / m < (m/R1^2 + (m+2)*R2^2) / (m+1)
    ```
    Correct claim (acta's own words): "machine-checked modulo classical
    Bessel inputs carried as named hypotheses" (hrec = DLMF 10.29.1,
    hAmos = Amos 1974 / Segura 2011 / Ruiz-Antolín–Segura 2016 Thm 2).
    Certified-arb harvest transcript `harvest_arb_transcript_1d888e99.txt`
    committed (22,986,387 cells, point/stability/3×3 all True). Acta at v88
    (2026-07-11): sanitation pass T1–T7 all green, mark-5 numerical evidence
    out of maintenance.
  - Note: `docs/SURFACE-CLOSURE-NOTES.md` header says "v3 (2026-07-09e)"
    while its tail runs to v88 (2026-07-11) and CLAUDE.md says "v1–v48" —
    version numbering across rewrites is inconsistent; most-recent-hash
    rules per house law.
- **Open problems / carried:** Part I — pass 2 of THE PAGE, mechanical
  cascade, oven [3,15], edges, [SLOT]s; do not submit with a live slot.
  Part II — the sole carried analytic input is the §6.3 Balaban UV
  single-scale bound `hRpoly`. Clay distance stated ~0%.
- **Shared machinery:** KP/cluster expansion (exported to
  lean-zero-free-regions and the two tree repos), rooted-tree/Catalan
  combinatorics (Appendix-F), interval/arb certification discipline,
  Bessel-ratio (Amos) machinery shared with lean-transfer-matrix/FHBessel.

### 2. riemann-prime-resolvent

- **Stack:** Lean 4 + Mathlib (25 files, ~1.8k LOC incl. subproject);
  Python (docs tooling, audit scripts); MkDocs manuscript; Docker; heavy CI.
- **Strongest artifact:** in the subproject `riemann-one-point-resolvent`,
  the compact-propagation layer (`StieltjesCompactBound.lean`), e.g.
  `exists_finitePositiveStieltjes_family_bound_on_compact`: a uniform
  one-point bound at `x₀ > 0` propagates to EVERY compact
  `K ⊆ Complex.slitPlane` with one compact-dependent constant:
  `∃ C, 0 ≤ C ∧ ∀ j z, z ∈ K → ‖finitePositiveStieltjes (s j) (weight j) (spectrum j) z‖ ≤ C * M`.
  Plus `CompactifiedKernelLimit.lean` (weak convergence of compactified
  finite measures ⇒ pointwise Stieltjes convergence). Root project:
  elementary bookkeeping (error budgets, positivity, rate exponent algebra)
  — the repo's own `docs/THEOREM-LEDGER.md` says so and states plainly:
  "The full integer-cutoff prime-tail inequality, slit-plane criterion and
  concrete operator convergence are not present as verified declarations."
  [oracle-logged via ledger + `oracle_check.lean` in CI]
- **Open problems:** the entire first arrow (concrete prime-built `S_j` →
  one-point bound + interval convergence). Carries `NO-RH-CLAIM.md`.
- **Mismatch flag:** doc-to-theorem ratio is extreme (78 .md files,
  versioned manuscript site, container pipeline around ~19 verified
  elementary declarations plus one genuine compact-bound layer). Honestly
  labeled throughout, but a reader of the apparatus alone would
  overestimate the verified content by an order of magnitude.
- **Shared machinery:** resolvents/Stieltjes transforms, moment
  certificates (with #17, #18), slit-plane analyticity.

### 3. lean-rooted-tree-polymer-expansion

- **Stack:** Lean 4 wrapper package (4 files, 155 LOC) + large
  provenance/CI/docs apparatus (189 files); depends via Lake on the MOTHER
  repo at pinned commit `4e45246a` (UPSTREAM.lock).
- **Strongest artifact:** publication endpoints (`PaperTheorems.lean`,
  [text-clean; CI-verified per badges]):
  `normalizedRootedChildFactorialTreeBound` —
  `((n:ℝ)+1) * ((n+1)!)⁻¹ * (Σ_T Π_v (c_T(v))!) ≤ 4^n`;
  `markedRootLeafGeometricBound` — `(n+1)·S_n(r) ≤ M·L^n` with `L = 4M²`;
  `targetPreservingWeightedTreeBound` — `T_n(Y) ≤ M·e^{-ρ·m(Y)}·L^n`.
  All three are one-line applications of pinned mother-repo theorems
  (`YangMills.KP.RootedLeafSummation`,
  `YangMills.RG.AppendixFSecondUrsellLeafSummation`).
- **Open problems:** none of its own — ARCHIVED (v2.4.3, terminal). States
  explicitly: does not prove `hRpoly`, continuum, OS, or mass gap.
- **Mismatch flag:** none in substance; but note the repo's mathematical
  content lives upstream — this is packaging + provenance around three
  wrapper theorems. Its own framing admits this.
- **Shared machinery:** rooted-tree/Ursell combinatorics (#4, #6),
  Appendix-F hole geometry (mother), polymer expansions.

### 4. rooted-tree-catalan-closure

- **Stack:** Lean 4 (lean-patch overlay onto the mother repo at pinned base
  commit; 11 files, ~2.5k LOC) + Python integer cross-checks + TeX paper
  (ai.viXra 2607.0001).
- **Strongest artifact:** the exact identity, proved unconditionally
  [oracle-logged: closure PR #5, replay commit `1eff8fc6`, CI run
  28610948452; `#print axioms` in-file]:
  ```lean
  theorem sum_prod_rootedChildCount_factorial_eq (n : ℕ) :
      (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v, (rootedChildCount T v)!) = n ! * catalan n
  ```
  with consumer `rootedChildFactorialCatalanIdentity_holds n` and the
  DISCHARGED Appendix-F adapter
  `appendixFHoleHsharpWeightedTreeMarkedRootSum_le_catalan` (Catalan
  hypothesis removed from the mother-facing marked-root bound:
  `(n+1)·MarkedRootSum ≤ catalan n · C_M(d,κ₀)^{2n+1}`).
  Independent finite evidence: three integer-only methods agree for
  `0 ≤ n ≤ 8` (`evidence/finite-catalan-checks.json`); Prüfer brute force
  `1 ≤ n ≤ 6`.
- **Open problems:** none for the identity; the downstream adapter in the
  MOTHER repo still exposes the proposition as an explicit hypothesis
  (instantiation into the mother core not yet merged there).
- **Mismatch flag:** none found — README status table distinguishes
  recovery vs. theorem-completeness cleanly. Venue is ai.viXra, not arXiv.
- **Shared machinery:** Catalan/plane trees (#6), spanning-tree
  combinatorics (#3), Appendix-F H# bounds (mother).

### 5. physmath-knowledge-tree

- **Stack:** JavaScript/HTML (local-first research-graph tooling, 350
  files); 6 token Lean files.
- **Strongest artifact:** NOT a theorem repo. The canonical evidence-labelled
  graph (59 nodes / 115 edges, `graph/*.json`) plus the curation pipeline
  (batch `batch-2026-07-03-ym-unblock`) which demonstrably SPAWNED two real
  satellites: hausdorff-certificates (Bridge Card 8) and
  physmath-lean-lemmas (Bridge Card 6). The Lean "microtheorems" are
  trivial identities [text-clean, no independent value].
- **Open problems:** n/a (infrastructure).
- **Mismatch flag:** the "Frontier mathematics corpus atlas" and nine
  browser "experiences" are large tooling investments with zero theorem
  content; the repo says as much ("a visual connection is never intended to
  imply a theorem"), so aspiration is labeled — but weight of tooling vs.
  math is worth knowing.
- **Shared machinery:** the bridge-card protocol itself (it is the routing
  layer used to mint #17 and #16).

### 6. mathlib-plane-tree-catalan

- **Stack:** Lean 4, single Mathlib-styled file (222 lines) + prepared PR
  apparatus + paper (same ai.viXra preprint as #4).
- **Strongest artifact:** `Mathlib/Combinatorics/Enumerative/PlaneTree.lean`
  [oracle-logged: committed `verification/pr1-compile-oracle.log`, exit 0,
  axioms exactly `[propext, Classical.choice, Quot.sound]` on the three
  headliners]:
  `PlaneTree.forestEquivBinTree : List PlaneTree ≃ Tree Unit`
  (left-child/right-sibling), and
  ```lean
  theorem card_treesOfNumNodesEq_succ (n : ℕ) :
      (treesOfNumNodesEq (n + 1)).card = catalan n
  ```
  Clean, self-contained, genuinely Mathlib-ready enumerative combinatorics.
- **Open problems:** PR not yet opened (needs Zulip/push access — a purely
  social step).
- **Mismatch flag:** none. README claims match the code exactly.
- **Shared machinery:** Catalan/plane-tree layer of #4; candidate upstream
  dependency for #11's future admissible-cut counting.

### 7. lean-ym-flow

- **Stack:** Lean 4 + Mathlib (10 files, ~930 LOC).
- **Strongest artifact:** `YMFlow/DiscreteHeat.lean` [text-clean;
  frontier doc claims 0 sorry]: unconditional discrete parabolic toolbox on
  finite weighted graphs — `heatStep_le_of_le` / `le_heatStep_of_le`
  (discrete maximum/minimum principles under CFL), `sum_heatStep` (exact
  mass conservation for symmetric weights), full iterate stability suite.
  Small but real analysis-adjacent Lean.
- **Open problems:** everything continuum: `rade_global_dim_two_three`,
  `struwe_schlatter_dim_four_conditional`,
  `waldron_no_finite_time_blowup_dim_four` are statements-first wrappers
  around literature-named hypothesis records [interface-only — FLAG: the
  bare names read as formalized theorems of Råde/Schlatter–Struwe/Waldron;
  they are not].
- **Shared machinery:** none load-bearing yet; heat semigroup discretics
  could serve #13's Gaussian-chain M3 and mother RG smoothing interfaces.

### 8. lean-zero-free-regions

- **Stack:** Lean 4 + Mathlib; DIRECT Lake dependency on the mother repo's
  KP layer at `7a71754b` (only satellite that imports mother code).
- **Strongest artifact:** the KP zero-free polydisc [text-clean; frontier
  doc dated 2026-07-03]:
  `partition_withActivity_ne_zero_of_kp` — ONE KP weight certifies
  `Z ≠ 0` for EVERY pointwise-dominated activity family (KP criterion is
  monotone in `‖z‖`), plus `partition_diskFamily_ne_zero_of_kp`,
  `analyticOn_partition_diskFamily` (fugacity disc section analytic +
  zero-free). First discharged Lee–Yang instance:
  `allZerosOnUnitCircle_singleBondPolynomial` (`z² + 2cz + 1`, real
  `|c| ≤ 1`, pure conjugation algebra).
- **Open problems:** M1 analyticity/clustering interfaces
  (`AnalyticLogPartitionHypothesis` etc.), M2 Asano/Lieb–Sokal, M3
  Heilmann–Lieb — all hypothesis-carried; frontier branch is sorried by
  design. Explicit no-RH-claim.
- **Shared machinery:** cluster/polymer expansion (mother KP), Lee–Yang /
  zero-free patterns (dictionary file cross-references Mathlib's
  `riemannZeta_ne_zero_of_one_lt_re` — labeled droppable).

### 9. ym-lattice-numerics

- **Stack:** Python (31 files; pytest; interval arithmetic in
  outward-rounded Decimal); no Lean exports (Interfaces.lean intentionally
  empty).
- **Strongest artifact:** `src/ym_lattice_numerics/exact2d.py` — CERTIFIED
  interval enclosures (truncated Bessel power series + explicit geometric
  tail bound, outward rounding) of `I_ν(β)`, the exact 2D mean plaquette
  `I_2(β)/I_1(β)`, and the exact 2D string tension
  `σ(β) = -log(I_2/I_1)`; cross-validated against its own SU(2) heat-bath
  MC at β = 1 (`tests/test_mc_vs_exact2d.py`). Also
  `scripts/aqft_bridges/transfer_gap_oracle.py` and
  `gaussian_covariance_oracle.py` — numerical twins of #13 and #14.
- **Open problems:** M2/M4 milestones open; constants file is smoke-only;
  no authoritative KP/Balaban window imported; states the expected M4
  answer is NEGATIVE (formal KP window far from continuum regime) and that
  this is a deliverable, not an assumption. Exemplary honesty.
- **Shared machinery:** interval certificates (house style of Part I),
  Bessel ratios (twin of #10 and of the φ-lemma lane), transfer
  gap / Gaussian covariance twins of #13/#14.

### 10. lean-2d-yang-mills

- **Stack:** Lean 4 + Mathlib (7 files, ~690 LOC), interface satellite.
- **Strongest artifact:** the convergence engine + SU(2) Witten layer
  [text-clean; frontier audited through PR #44]:
  `summable_su2_dim_sq_exp_neg_casimir` (heat-kernel character series
  convergence input: `Σ (n+1)² e^{-t·Casimir}` summable for `t > 0`),
  `summable_su2WittenZetaTerm` (`1 < Re s`),
  `su2_wittenZetaSeries_eq_riemannZeta`, and `su2WittenZetaPackage` — the
  repo's first fully unconditional package instance.
- **Open problems:** heat-kernel convolution/semigroup, Migdal
  self-similarity, exact area law, continuum limit — ALL carried as
  structure fields (`HeatKernelCharacterPackage`,
  `MigdalSelfSimilarityPackage`, `ExactAreaLawPackage`).
- **Mismatch flag:** theorem names `migdal_self_similarity`,
  `simpleLoop_areaLaw_exact` are field projections [interface-only]; README
  says so, but the names alone overstate. Also eight consecutive PRs
  (#29–#44) were digest refreshes adding zero theorems — activity metrics
  here do not track mathematical progress.
- **Shared machinery:** exactly soluble 2D sandbox shared with
  ym-lattice-numerics (`exact2d.py` is its declared numerical twin);
  string tension = Bessel ratio connects to the Amos lane (#13/FHBessel,
  mother φ-lemma).

### 11. lean-connes-kreimer

- **Stack:** Lean 4 + Mathlib (9 files, ~1.2k LOC).
- **Strongest artifact:** M0 core [text-clean]: `Forest Tree := Finsupp
  Tree ℕ`, `CKAlgebra R Tree := MvPolynomial Tree R`, vertex-count grading
  (`homogeneousSubmodule`, closure under `add/smul/mul`), and the
  `AdmissibleCutData` contract with grafting-operator wrapper lemmas
  (`graftOperator_forestMonomial` etc. — consequences of SUPPLIED data).
- **Open problems:** the actual Hopf structure. M1 (coproduct by admissible
  cuts, coassociativity), M2 (antipode), M3 (Birkhoff/BPHZ) — none started
  as proofs. The frontier doc's own INTERFACE FINDING (issue #29) is
  admirably honest: the `Has*` names are `Nonempty` wrappers witnessed by
  ANY bialgebra structure on the polynomial algebra, not only the
  Connes–Kreimer one; existence of admissible-cut data is open.
- **Mismatch flag:** repo name/README promise "Connes-Kreimer Hopf algebra";
  code contains a graded commutative polynomial algebra and a data
  contract. Distance to an actual CK coproduct theorem: all of it.
  Scope disclaimer (no YM connection until a consumer exists) is exemplary.
- **Shared machinery:** rooted trees (#3, #4, #6). Note: no tree TYPE is
  fixed — `Tree` is a parameter; #6's `PlaneTree` is the obvious candidate
  instantiation.

### 12. lean-os-positivity

- **Stack:** Lean 4 + Mathlib (11 files, ~2.0k LOC). Committed build note:
  "Build completed successfully (1905 jobs)".
- **Strongest artifact:** the pairing-form layer [text-clean]:
  `normSq_pairingForm_le` — the reflection Cauchy–Schwarz inequality
  (Glimm–Jaffe Thm 6.2.2) proved by the discriminant argument; plus a real
  model instance: `isingBond_reflectionPositive` (ferromagnetic bond weight
  `e^{β·k}` with PSD kernel ⇒ finite-volume reflection positivity,
  `0 ≤ β`), with null-space well-definedness bridges
  (`pairingForm_respects_null_*`) — the substrate for the M2 GNS quotient.
- **Open problems:** the GNS quotient itself (M2), transfer-matrix
  certificates (`TransferMatrixReflectionCertificate`), `GNSReconstruction`
  data, `WilsonRPCertificate`, operatorial mass gap — interfaces with
  explicit fields. Not the Euclidean OS axioms on ℝ^d; says so.
- **Shared machinery:** OS positivity/transfer dictionary consumed by #13's
  targets; Ising model shared with #13; direct service role for mother
  M1/M2 milestones.

### 13. lean-transfer-matrix

- **Stack:** Lean 4 + Mathlib (10 files, ~760 LOC) + the standalone
  `FHBessel/` module.
- **Strongest artifacts (two):**
  1. The Ising chain closed end-to-end [text-clean; CI run 28801139572
     recorded]: `Ising1DGap.lean` — `isingSpectralRatio_eq_tanh`, strict
     two-sided gap `|λ₋| < λ₊` for every real coupling,
     `isingTransferData_hasExponentialClustering` (amplitude one, exact
     rate), and `isingInterface` — the first `TransferOperatorInterface`
     instance with ZERO carried hypotheses (both directions gap ⇄
     clustering are theorems there).
  2. `FHBessel/FHBesselAmos.lean` [in-file `#print axioms`; checked
     standalone per its README against Lean 4.30.0-rc2 — NOT wired into
     this repo's lakefile]:
     ```lean
     theorem unit_step_of_recurrence_and_amos
         (x nu I0 I1 I2 : ℝ) (hx : 0 < x) (hnu : 0 ≤ nu)
         (hI0 : 0 < I0) (hI1 : 0 < I1)
         (hrec : I0 - I2 = 2 * (nu + 1) / x * I1)
         (hamos : I1 / I0 < x / (nu + 1/2 + Real.sqrt ((nu + 1/2)^2 + x^2))) :
         I1 / I0 - I2 / I1 < 1 / x
     ```
     plus `amos_calibration` and `logderiv_unit_step_increase`. This is the
     machine-checked core of the mother repo's Feynman–Hellmann Bessel
     paper (`papers/bessel-amos-fh`, spec v87 CLOSED) — the same
     recurrence+Amos hypothesis pattern as the surface track's φ-lemma.
     [hypothesis-carried: the Amos bound itself is NOT proved.]
- **Open problems:** M1/M2 generic finite-dimensional Perron–Frobenius
  (hypothesis-explicit), M3 Gaussian chain not started.
- **Shared machinery:** transfer matrices (twin:
  `transfer_gap_oracle.py` in #9), Ising with #12, THE Amos/Bessel lane
  with the mother Part-I paper track and #10's string tension.

### 14. lean-gaussian-field

- **Stack:** Lean 4 + Mathlib (11 files, ~1.3k LOC).
- **Strongest artifact:** covariance layer [text-clean]:
  `GaussianVectorSpec.covariance_sq_le` / `abs_covariance_le`
  (Cauchy–Schwarz for PSD covariance via discriminant),
  `covariance_eq_zero_of_diag_left/right` (degenerate directions),
  `charExponent` facts (`charExponent_re_nonpos`,
  `norm_exp_charExponent_le_one`), pairing-type cardinality lemmas.
  Honest but modest: pure finite linear algebra.
- **Open problems:** the actual content is all carried — Isserlis/Wick
  (`IsserlisInterface.isserlis` is DATA), uniform moment bounds, existence
  and uniqueness of the realized Gaussian law, lattice covariance decay
  (`(-Δ+m²)^{-1}` decay is M3, untouched).
- **Mismatch flag:** none serious (frontier doc is precise); but note the
  README milestone list reads like a plan and NONE of M1–M3 is closed.
- **Shared machinery:** Gaussian fields (twin:
  `gaussian_covariance_oracle.py` in #9); intended consumer is the mother
  small-field/`hRpoly` lane; #12's Gaussian-chain targets.

### 15. hausdorff-certificates

- **Stack:** Python only (mpmath sole runtime dep); deterministic JSON
  certificates; 46 tests; Makefile; CI regenerates artifacts and fails on
  byte drift.
- **Strongest artifact:** the exact-rational PSD DECISION backend: for
  Hankel matrices `H_N = (b_{i+j})`, `L_N = (b_{i+j} - b_{i+j+1})`,
  `L_N^θ = (θ b_{i+j} - b_{i+j+1})`, produces either an exact
  `P^T A P = L D L^T` factorization with `D ≥ 0` or an exact rational
  witness `v` with `v^T A v < 0`; interval backend certifies
  enclosure-wide PD or enclosure-wide failure, else INCONCLUSIVE. The
  verifier revalidates WITHOUT trusting the generator. Committed reference
  batch includes both directions on real examples
  (`laplacian5_coercivity_pass` / `laplacian5_coercivity_fail`,
  `two_atoms_support_true/false`, ζ-tier `N ≤ 14` truncated moments).
- **Open problems:** ζ demonstration tier gated on two literature/
  computation gates (SOURCES.md). Scope contract states PSD_CERTIFIED for
  finitely many N proves nothing infinite; NOT_PSD is a genuine finite
  falsifier. Correctly claims zero distance moved to RH/Clay.
- **Shared machinery:** THE two dictionaries — Riemann side
  (`b_n(x₀) = x₀^n(-1)^n S_Ξ^{(n)}(x₀)/n!`) exactly matching #18's Lean
  `hankelForm` layer; YM side (coercivity `K ⪰ cI` ⇔ support in
  `[0, θ]`, `θ = x₀/(c+x₀)`) matching #18's `theta_shift` lemma and aimed
  at mother precision-operator candidates.

### 16. physmath-lean-lemmas

- **Stack:** Lean 4 + Mathlib (lakefile.toml; 4 files, ~420 LOC);
  `scripts/check_axioms.sh` in CI.
- **Strongest artifact:** the rooted closure of the three infinities
  [oracle-logged per README/CI]:
  ```lean
  theorem rootedTripleInfinity_closure_le
      (H : ℕ → ℕ → ι → ℝ≥0∞) (ε : ℕ → ℝ≥0∞) (w : ι → ℝ≥0∞) {M L K q G : ℝ≥0∞}
      (hH : ∀ k n Y, H k n Y ≤ M * ε k * (L * ε k) ^ n * w Y)
      (hq : ∀ k, L * ε k ≤ q) (hw : ∑' Y, w Y ≤ K) (hε : ∑' k, ε k ≤ G) :
      ∑' (k n : ℕ) (Y : ι), H k n Y ≤ M * G * K * (1 - q)⁻¹
  ```
  with the `e^{-c₀t}` variant, and the derived normed-space consumers
  `summable_of_rootedLeafBudget`, `norm_tsum_le_of_rootedLeafBudget`
  (`‖∑' p, H p‖ ≤ M·G·K·(1-q)⁻¹`). Design note worth copying: core in
  `ℝ≥0∞` where Tonelli is free, consumer layer DERIVED not assumed. A fully
  structural toy instance (bound 16/21) is included as a worked example.
- **Open problems:** none internal. The programme instantiation (feeding
  mother `summable_abs_of_omegaRootedClusterWithHolesActivityDecay`-style
  inputs) is explicitly deferred to the mother; consumption guidance says
  VENDOR the single file, do not take a Lake dep.
- **Shared machinery:** the geometric-budget pattern of #3; direct
  consumption point named in the mother's Appendix-F front.

### 17. riemann-resolvent-programme

- **Stack:** Lean 4 + Mathlib (3 files, ~260 LOC), lakefile.toml, axiom
  audit script in CI.
- **Strongest artifact:** the atomic Hausdorff/Hankel layer [oracle-logged
  per README table]: `hankelForm_atomic_eq_sum_sq`,
  `hankelForm_nonneg_of_atomic` (atomic moments ⇒ Hankel form is a sum of
  squares), `theta_shift_eq_atomicMoment` +
  `hankelForm_theta_nonneg_of_support` (the `L_N^θ ⪰ 0` support test — the
  formal half of #15's falsifier), and zero-model certificates
  `hankelForm_nonneg_of_zeroModel` / `hankelForm_L_nonneg_of_zeroModel`.
  Assemblies `riemannHypothesis_of_slitPlaneExtension`,
  `riemannHypothesis_of_primeResolventApproximation` are proved AS
  ASSEMBLIES with carried inputs `bridgeA`, `bridgeC` named in the
  signature — the honest pattern (defined against Mathlib's
  `completedRiemannZeta` and `RiemannHypothesis`).
- **Open problems:** bridges A (slit-plane holomorphic extension of
  `𝒮_Ξ`) and C (prime-resolvent approximation), tasks T1–T4,
  `primeTail_bound`. Distance to RH: stated unchanged. `shares_method`
  ONLY with the YM programme; RH⇔YM implication explicitly discarded at
  curation.
- **Shared machinery:** Hankel/moment positivity duplicated *by design* as
  the formal twin of #15 (numeric) — the two are one construction split
  across a Lean side and a certificate side; Stieltjes/resolvent layer
  overlaps #2.

### 18. aqft-split-inclusion-series

- **Stack:** TeX (5 papers, v2, ai.viXra 2512 series) + Python verification
  suites (13 scripts, 9 committed logs) + CSV/NPY results. No Lean.
- **Strongest artifact:** the verification discipline itself: every v2
  correction is driven or confirmed by an exact numerical check with
  committed logs — e.g. 0060's repaired reconstruction-fidelity bound
  passing at every admissible point with margins 46–68×, 1916 random gapped
  fidelity pairs with 0 violations; 0061's corrected work-sign verified
  over 200 random energy-conserving unitaries (v1's sign reached −1.12;
  corrected min +0.48); 0061's new unconditional entropy-production floor
  `P_min ≥ k_B T σ(ρ)` (Spohn) with rate-Pythagoras split verified to
  1e−13; 0064's exact quasi-free rate-inheritance law
  `κ(ε) = P(ε)e^{−2q(ω_b)ε}` (fitted slope 0.8106 vs analytic 0.8109).
  Notable: v1 errors are documented and REFUTED numerically in-repo (a
  vacuous definition, a sign error, a placeholder figure) — real
  falsifier practice.
- **Open problems:** rate inheritance for interacting gapped buffers
  (0071's hinge, "partially resolved"). Theorems are TeX-proved,
  physics-grade, NOT machine-checked; verification is numerics, not proof.
- **Shared machinery:** Combes–Thomas exponents / gapped-buffer decay
  (`arccosh(1+m²/2)`), Gaussian covariance methods — and #9 carries
  `scripts/aqft_bridges/` oracles referencing this series, so a numerics
  bridge already exists in code.

---

## PART B — SYNTHESIS: THE REAL BRIDGES

Ranked by (provable with existing assets) first, (interesting) second.
House rule respected throughout: no bridge below claims value via
proximity to RH or YM; each states exactly what would be proved. Every
judge is computable BEFORE the page is written.

### BRIDGE 1 — Catalan closure into the mother Appendix-F core
**(#4 rooted-tree-catalan-closure + #6 mathlib-plane-tree-catalan → mother KP/RG)**

- **What EXISTS:** `sum_prod_rootedChildCount_factorial_eq` proved
  unconditionally [oracle-logged]; the discharged consumer
  `appendixFHoleHsharpWeightedTreeMarkedRootSum_le_catalan` already
  written against mother namespaces; the mother-side replacement point
  named (`YangMills/KP/RootedCatalan.lean` patch); the wrapper repo #3
  pinning the `4^n` predecessor; a Mathlib-ready `PlaneTree` file with
  committed compile+oracle log.
- **What must be BUILT:** essentially nothing mathematical — a merge/replay
  of the lean-patch into the current mother head (base commit drift
  `1d044a35` → current is the only risk), plus the one-line swap of
  `4^n` for `catalan n` at the Appendix-F consumption sites. Separately:
  open Mathlib PR 1 (a social step).
- **NEW theorem:** unconditional sharpened marked-root second-Ursell leaf
  bound in the mother core: leaf overcount `catalan n` (~`4^n/n^{3/2}√π`)
  replacing `4^n` — a strict constant/polynomial improvement in the KP
  radius bookkeeping, with the Catalan hypothesis GONE from the frontier
  list.
- **Honest size:** lemma (bookkeeping improvement inside a pipeline whose
  binding constraint is `hRpoly`; moves `hRpoly` zero). The Mathlib PR is
  a genuine, small, standalone contribution regardless of the programme.
- **Pre-registrable judge:** (a) mother `lake build YangMillsCore` green
  with job count STRICTLY incremented; (b) `#print axioms` on the merged
  consumer = exactly the three standard axioms; (c) rerun of
  `scripts/check_finite_catalan.py` (three integer methods, `n ≤ 8`)
  byte-identical; (d) the frontier ledger line for the Catalan hypothesis
  deleted in the SAME commit.

### BRIDGE 2 — One Bessel module discharges the same named hypothesis in three repos
**(#9 ym-lattice-numerics exact2d + #13 FHBesselAmos + mother φ-lemma + #10 string tension)**

- **The observed fact:** the identical hypothesis
  `hAmos : I_{ν+1}/I_ν < x/(ν+1/2+√((ν+1/2)²+x²))` is carried, verbatim in
  substance, at THREE consumption sites: the mother surface-track φ-lemma
  `phi_step_of_recurrences` (on which E'<0 for β ≤ 3.5 is conditional),
  #13's `unit_step_of_recurrence_and_amos` (the FH Bessel paper), and —
  one inference away — #10's exact string-tension positivity
  (`σ = -log(I_2/I_1) > 0` follows from hAmos at ν=1 since the Amos bound
  is < 1). Meanwhile #9's `exact2d.py` ALREADY computes certified interval
  enclosures of exactly these `I_ν` and ratios (truncated series +
  explicit geometric tail, outward rounding).
- **What must be BUILT:** a single module — either (route L) Lean: define
  `besselI ν x` for the needed integer/half-integer orders as its power
  series (Mathlib has NO Bessel functions; absolute convergence is easy),
  prove the finitely many series manipulations needed for the Amos bound
  on a pre-registered compact box (m,β) ∈ [1,M]×(0,B] via explicit tail
  bounds and rational arithmetic; or (route A) Part-I-style: an arb
  transcript certifying `min slack of hAmos` > 0 on the pre-registered
  grid with ball+boolean and provenance header (the acta records an
  auditor pass on [1,100]×[0.01,300] with min slack 2.5e-7 — that is the
  landscape; the committed certificate does not exist yet).
- **What EXISTS:** all consumer algebra (both step lemmas, oracle-clean);
  the interval methodology in Python with tests; the pre-registered slack
  landscape in the acta; the DLMF recurrences as the only other inputs.
- **NEW theorem:** "the φ-lemma holds for I_m(β) on [1,M]×(0,B],
  machine-checked / certified without the Amos hypothesis" — upgrading the
  surface paper's E'-relay from "conditional on classical Bessel inputs"
  to certified on the working window; simultaneously the FH paper's
  targets 1–2 become unconditional on that window, and 2D string-tension
  positivity `σ(β) > 0` becomes a theorem in #10's sandbox.
- **Honest size:** paper-grade support lemma for the Part-I manuscript
  (it feeds a live [SLOT]-adjacent obligation of the ACTIVE programme —
  by owner priority this is the highest-value bridge); route L is a
  respectable standalone formalization note (first Bessel-I inequalities
  in Lean).
- **Pre-registrable judge:** register the grid and the minimum-slack floor
  BEFORE the run (e.g. slack ≥ 1e-7 everywhere on the auditor's grid, with
  the known minimum location (m,β) reproduced within one cell); acceptance
  = certified enclosure of `x/(ν+1/2+√((ν+1/2)²+x²)) − I_{ν+1}/I_ν` has
  positive lower ball at every registered node, transcript committed with
  script sha256 before any ink; Lean side: the discharged statement must
  syntactically instantiate `hAmos` as consumed by
  `phi_step_of_recurrences` — no restatement.

### BRIDGE 3 — The 1D Ising vertical slice: first end-to-end unconditional instance of the OS→transfer→gap dictionary
**(#12 lean-os-positivity + #13 lean-transfer-matrix + #8 lean-zero-free-regions + mother KP; numeric twin in #9)**

- **What EXISTS:** RP for the ferromagnetic bond (`isingBond_reflectionPositive`,
  #12) + reflection Cauchy–Schwarz + null-space bridges (the GNS
  substrate); the FULLY unconditional transfer side (`isingInterface`,
  exact rate `-log tanh β`, #13); the KP zero-free polydisc consuming the
  mother's `KPCriterion` (#8); a committed numeric twin
  (`transfer_gap_oracle.py`, #9).
- **What must be BUILT:** (a) the M2 GNS quotient in #12 (the
  well-definedness lemmas are done; the quotient construction and transfer
  operator on it are not); (b) the high-temperature polymer representation
  of the 1D Ising chain satisfying `KPCriterion` (finite, explicit
  activities — a genuine but bounded formalization task); (c) the assembly
  statement tying the three satellites' Ising instances to ONE model
  (currently each repo has its own Ising encoding — an isomorphism layer
  is needed; this is the hidden cost).
- **NEW theorem:** "the zero-field 1D Ising chain at every β ≥ 0 has
  reflection positivity, a GNS transfer operator with spectral gap exactly
  `-log tanh β`, exponential clustering at that rate, and nonvanishing
  partition function in a KP polydisc — with zero carried hypotheses and
  axiom oracle `[propext, Classical.choice, Quot.sound]`."
- **Honest size:** paper-grade FORMALIZATION exercise; zero new
  mathematics (all classical). Its real value is programme-internal: a
  non-vacuity witness that the whole interface stack (certificates,
  dictionaries, satellite imports) composes on a real model — precisely
  the audit the satellites' `Nonempty`-wrapper risk (cf. #11's issue #29
  finding) calls for.
- **Pre-registrable judge:** (a) the final statement contains NO
  certificate/package fields — grep-checkable; (b) axiom oracle on the
  assembled headline; (c) numeric twin: `transfer_gap_oracle.py` rate
  matches `-log tanh β` on a pre-registered β grid within stated interval
  tolerance, transcript committed first.

### BRIDGE 4 — Finite coercivity screens: Lean support-test ⇄ exact certificates
**(#17 riemann-resolvent-programme + #15 hausdorff-certificates → mother SPD/precision frontier)**

- **What EXISTS:** the Lean atomic direction
  (`hankelForm_theta_nonneg_of_support`: support in `[0,θ]` ⇒
  `L_N^θ ⪰ 0`, with `theta_shift_eq_atomicMoment` giving the coercivity
  dictionary `θ = x₀/(c+x₀)`); the exact-rational DECISION procedure with
  committed pass AND fail certificates on the 5-site Laplacian
  (#15 `laplacian5_coercivity_pass/fail`); the mother's B/local
  metric/rate/amplitude dictionary frontiers as the declared consumer of
  claimed coercivity constants.
- **What must be BUILT:** the finite CONVERSE in Lean — for a finite
  spectrum (j atoms), `L_N^θ ⪰ 0` for `N ≤ j` implies
  `supp(μ) ⊆ [0,θ]`, i.e. `K ⪰ cI` — finite linear algebra
  (Vandermonde/quadrature argument), lemma-sized; plus a thin
  Lean-statement-to-JSON-certificate correspondence (same rational data on
  both sides).
- **NEW theorem:** a finite EQUIVALENCE, machine-checked: "for
  finite-dimensional symmetric `K` and fixed `x₀ > 0`:
  `K ⪰ cI ⇔ L_N^θ(b(K,x₀)) ⪰ 0 for N ≤ dim`, `θ = x₀/(c+x₀)`" — which
  upgrades #15's screen from consistency-check to certified decision
  procedure for coercivity claims entering ANY repo's frontier (mother
  precision candidates, #17's YM-side dictionary).
- **Honest size:** lemma (clean, self-contained; possibly Mathlib-adjacent
  as finite Hausdorff moment machinery). No claim about infinite
  dimensions, RH, or hRpoly — the scope contracts of both repos already
  say this correctly.
- **Pre-registrable judge:** instantiate the Lean equivalence on the
  committed `laplacian5` rational data; acceptance = Lean verdicts
  reproduce the two JSON certificates' verdicts (pass at the certified c,
  fail at the refuted c) with `decide`-grade rational arithmetic; axiom
  oracle standard.

### BRIDGE 5 — Vendor the three-infinities closure into the mother Appendix-F front
**(#16 physmath-lean-lemmas → mother)**

- **What EXISTS:** `norm_tsum_le_of_rootedLeafBudget` and
  `summable_of_rootedLeafBudget` proved, oracle-audited, in a single
  self-contained file DESIGNED for vendoring (consumption guidance
  explicit); the mother side already owns the shell-growth/marginal
  summability substrate the budget hypotheses mirror.
- **What must be BUILT:** the instantiation only — identify
  `(M, L, K, q, G)` with the mother's existing Appendix-F constants and
  discharge the four budget hypotheses from theorems already in the core
  (candidates named in #16's own docs). If any budget hypothesis is NOT
  yet a mother theorem, the bridge honestly reduces scope to "the ones
  that are".
- **NEW theorem:** collapse of the three convergence budgets (cluster
  order n, target geometry Y, RG scale k) into ONE summable observable
  with the closed bound `M·G·K·(1-q)⁻¹` inside the sorry-free core —
  replacing three separate tsum manipulations at the Appendix-F front
  with one lemma call, and adding the `e^{-c₀t}` decay form for free.
- **Honest size:** lemma / refactoring theorem. States nothing about
  `hRpoly` (its hypotheses are exactly the carried inputs; the repo's own
  scope contract already says distance unchanged).
- **Pre-registrable judge:** (a) vendored file compiles inside the core
  with zero modifications beyond namespace; (b) build job count
  increments; (c) at least one existing mother theorem's proof strictly
  shortens (diff-line count pre-registered) with identical statement and
  oracle — if no existing proof shortens and no new consumer discharges
  its hypotheses from existing theorems, the bridge FAILS its judge and
  the vendoring is not merged.

### Explicitly REJECTED bridge candidates (recorded so they are not re-derived)

- **#11 (Connes–Kreimer) → mother counterterm bookkeeping:** no consumer
  exists (`hRpoly` is not currently multiscale-with-counterterms); the CK
  repo itself says the connection is contingent. Building M1 (admissible-cut
  coproduct + coassociativity, ideally on #6's `PlaneTree` as the concrete
  tree type) is worthwhile Mathlib-facing combinatorics ON ITS OWN TERMS,
  but as a "bridge" it fails the proved-reduction test today.
- **#2/#17 (Riemann repos) ↔ anything YM:** `shares_method` only, by the
  owner's own curation record (`discard.rh_ym_equivalence`). The shared
  machinery (Hankel positivity, Stieltjes compacts) is real and is
  exploited in Bridge 4 WITHOUT any RH/YM value transfer.
- **#18 (AQFT series) → Lean repos:** the Combes–Thomas/gapped-buffer
  numerics are physics-grade and the falsifier practice is exemplary, but
  no Lean statement on the list currently names an input that a #18
  artifact certifies. The existing `aqft_bridges` oracles in #9 are the
  right-sized connection already.

### Cross-cutting observation

The ecosystem has a consistent and unusually honest architecture: every
Lean satellite carries its analytic debt as named hypotheses/certificate
fields (no project axioms anywhere; the three text-level `sorry`/`axiom`
hits in 17 repos were all comments), and four satellite pairs come with
committed numerical twins (#10⇄#9 exact2d, #13⇄#9 transfer oracle,
#14⇄#9 covariance oracle, #17⇄#15 Hankel certificates). The recurring
failure mode is not dishonesty but AMBITION IN THE NAMING and
doc-apparatus mass exceeding theorem mass (#2, #5, #10 PR-churn, #11).
The two assets that are simultaneously finished, oracle-witnessed, and
consumed nowhere yet are the Catalan closure (Bridge 1) and the
three-infinities lemma (Bridge 5); the single highest-leverage NEW build
is the Bessel/Amos module (Bridge 2), because it is the only item on this
list that feeds the ACTIVE Part-I paper's own critical path.

*End of inventory. Survey clones remain in
`C:\Users\lluis\AppData\Local\Temp\claude\repo-survey\` for spot-audit.*
