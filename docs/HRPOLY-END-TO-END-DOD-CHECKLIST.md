# hRpoly end-to-end Definition-of-Done checklist

Status: LIVE COMPLETION AUDIT.  This document prevents a green intermediate
brick from being reported as closure of hRpoly.  A row is complete only when
the cited current-state evidence proves the full scope of that row.

Baseline: `9da8a6feaf832067c45e64398c77fbb61314f225` is an ancestor of the
active branch.  Branch: `codex/cmp116-interacting-wilson-hessian`.  PR #29
must remain draft until every row below is complete.

Hard invariants while this checklist is open:

- terminal producer count is `20/41`;
- `TermSource = 0`;
- window 15 is compatible but not attained.

These values may change only when a compiled source-facing producer or
inhabitant justifies the exact movement.

| requirement | status | authoritative evidence / remaining gate |
|---|---|---|
| Exact baseline ancestry | **complete** | `git merge-base --is-ancestor 9da8a6fe... HEAD` returned success on 2026-08-25. |
| Source-specific Units A--E | **complete** | Cold run `32329127991`, source `9d378412...`, 36/36 stages exit zero, 124 allowed axiom blocks, inner SHA-256 `90D66229...`, outer SHA-256 `1E500200...`; ledger Addendum 869. |
| Unit F periodic-owner continuation | **complete** | Cold run `32343215395`, source `fa29c350...`, 8/8 stages exit zero, 49 allowed axiom blocks; ledger Addendum 870. |
| C6 source/localized retained dependency boundary | **complete** | Addenda 946--947: fresh Eq. (3.59) source `cd6ff656...` passed a `11012`-job cold root; all 34 C6d blobs match checkpoint `3738ddb6...`; the retained-runtime cross gate passed all 17 audits and 92/92 allowed axiom readouts; the joint verifier emitted `C6D_EQ359_CROSS_EVIDENCE_OK`.  Seal `850fd929...` retired exactly the 34 C6d marks.  Archive hashes are `F7838E80...` (Eq. (3.59)) and `4ECF337A...` (cross); bundle `49FCD9A4...`. |
| C6d.1 literal localized retained precision | **complete** | Addendum 949: exact source `38c4d4df...` passed all four source/audit pairs and a cold `11012`-job root; the same-checkout supplement confirms 15/15 allowed axiom readouts.  The literal `Delta'_a = Delta_U + a_j Q'^* Q'` is constructed from the physical regularity witness and internally generated retained tower with both summands and source spacing visible.  Archive `E0B5F4F5...`, supplement `2566D9AD...`, manifest `DD225250...`. |
| Eq. (3.37) complex Ubar boundary | **complete** | Fresh Colab Pro+ source `573d70e0...`: the coordinate/background gate (`57` declarations, root `8508.658` s, archive `B14FF541...`) and the closed physical recursion gate (`14` declarations, root `8972.230` s, archive `A60925A...`) both emitted literal `FINAL_STATUS=PASS`; the exact twelve PRE-VALIDATION notices are retired by the selective seal recorded in Addendum 944. |
| Complex inverse and all-orientation small-field producer | **complete** | The sealed prerequisite graph proves the explicit finite-product `(1+r)^M` costs, the `q/(1-q)` inverse loss and the non-vacuous common zero-radius witness consumed by the closed-radius physical gates.  No inverse or all-orientation bound is accepted as free caller data. |
| Forced finite complex recursion | **complete** | `cmp99Eq337SourceComplexClosedRecursiveBackground` constructs the fine perturbation and every coarse `Ubar` background internally from literal `U`, `A`, `eta` and the generated scalar radii; its cold audit is part of the `A60925A...` evidence package.  No background family, free `hdev`, per-scale smallness proof or terminal equality is an input. |
| Physical flowing-radius-chain producer | **complete** | `CMP99ComplexClosedRadiusBudget` exposes one growth factor and one initial-scale `terminal_small` inequality; the sealed physical bridge/gates derive every strict per-scale no-winding, log and next-link gate and feed the closed recursion.  No radius family or `∀ k < depth` smallness package is caller data. |
| Retained-tower/source-region transport of the four physical actions | **in progress** | The complex Eq. (3.59) tower, its exact physical real slice and the 34-file retained source boundary are sealed (Addenda 945--947); C6d.1 seals the literal localized retained precision (Addendum 949). Addendum 951 seals the baseline real slice, retained complex extension and recursive physical/analytic tower agreement from a fresh `11026`-job root. Addendum 952 then seals the terminal tower pair, physical-radius bridge, C6d-specific Eq. (3.60) route and closed physical precision from a fresh `11040`-job root. Addendum 953 seals the positive-depth source-generated coercivity/reachability and internally constructed baseline Green from a fresh `11060`-job root with 80 allowed axiom readouts. Addendum 955 seals the full-companion ambient precision, explicit active-region reindexing, canonical Green transport and exact `depth = 0` companion/Green: all eleven source/audit pairs, all 58 allowed axiom readouts and the same-checkout root passed from fresh source `89cb81e0...`; seal `6d2b2709` retired exactly 22 marks. Addendum 958 seals the source-separated positive-depth and zero-depth ambient Greens, their canonical ambient completion and the terminal-block finite-range diameter from one fresh `11085`-job root; exactly eight additional PRE-VALIDATION notices are retired. Addendum 959 seals the rectangular reindex algebra and exact physical background, Laplacian and precision dictionaries from fresh source `deeabe20...`, with ten allowed readouts and a successful same-checkout root. The remaining live boundary is re-instantiation of the four fixed-depth CMP96 actions on that one transported physical Green. Equality of independently chosen towers, precisions or Greens remains inadmissible; see `tmp/C6D-SOURCE-DIRICHLET-COMPRESSION-DESIGN.md`. |
| Eq. (3.51) source-sign convention | **measured no-go; physical regrouping open** | Addendum 948 seals the explicit two-by-two witness proving that the repository/source raw diagonal sign is not the printed Eq. (3.51) sign under the fixed convention, while the norm equality survives.  This forbids a silent definitional identification; it does not prove Eq. (3.51)--(3.54) or the physical row bound. |
| Uniform physical `B0, delta0` | **open** | Fixed-depth and source-flow Fourier pieces are sealed, but one positive amplitude/rate pair uniform in depth has not yet been produced for the transported physical actions.  Per-depth or per-action constants do not close this row. |
| Physical window 15 | **open** | Compatibility is proved; attainment requires the literal regional defect/Neumann estimate, not a renamed `norm R' < 1` hypothesis. |
| `PreEq136` producers | **open: 20/41** | Every remaining row must have a source-facing producer.  Assemblers do not increment the numerator. |
| First conditional `TermSource` inhabitant | **open: 0** | Requires `41/41`; a constructor receiving `PreEq136` is not an inhabitant. |
| Lemma-1 equation (1.36) for the physical operator | **open** | Generic L1/L2 and substantial source substrate exist, but the printed physical L1--L9 chain and final bound are not fully discharged.  This obligation is outside the 41-row conditional constructor. |
| Unconditional `TermSource` inhabitant | **open** | Requires the physical Lemma-1 certificate, not a free residual bound. |
| `hraw -> H# -> hprofile` physical chain | **open** | Exponential profile cannot remain a final hypothesis. |
| Nontrivial terminal theorem application | **open** | Endpoint fixed: a source-specific corollary must feed the unconditional physical `SingleScaleUVDecay` produced by the completed `hraw -> H# -> hprofile` chain into `lattice_mass_gap_of_singleScaleUVDecay_marginal`, yielding its displayed marginal mass-gap inequality.  It may consume genuine independent marginal-flow and IR hypotheses, but may not accept `SingleScaleUVDecay`, scalar `hRpoly`, `hprofile` or a terminal decay equality as a free input.  The existing `lattice_mass_gap_of_cmp116RawSource_hsharp_marginal` is conditional plumbing, not this closure, because it still receives `hprofile` explicitly. |
| Full clean build and complete axiom oracle | **open for final SHA** | Intermediate cold seals do not substitute for the terminal repository-wide build/oracle. |
| Terminal reproducibility | **open** | Two independent fresh heavy-environment checkouts at the same final SHA, with separate build state and matching output hashes. |
| Final paper | **open** | Update or traceably supersede `papers/hrpoly-cmp116-reduction/hrpoly_cmp116_reduction.tex`, its `README.md`, `CLAIM_MAP.md`, PDF and `output/pdf/hrpoly-cmp116-reduction.pdf` in the terminal SHA.  The current v0.3 artifacts still point to PR #28 and explicitly leave `hRpoly` open.  Compile, render and visually verify the terminal manuscript against the sealed theorem graph; no stale counters, placeholders or claims beyond compiled evidence. |
| PR #29 governance | **in progress** | PR is draft and tracks the active branch.  Keep draft until the full checklist is complete; use fast-forward publication only. |

Completion is forbidden while any row is open, while any source module still
contains a live PRE-VALIDATION notice that the final claim consumes, or while
an input merely renames an obligation listed above.
