# PETER-WEYL ROADMAP — RECLASSIFIED 2026-04-22

This document is **no longer on the Clay critical path**.

For the current critical path, see `BLUEPRINT_F3Count.md`,
`BLUEPRINT_F3Mayer.md`, and `STATE_OF_THE_PROJECT.md`.

For the original 574-line roadmap (Layer 0–5 architecture, six-layer
dependency chain, Mathlib availability map, first-milestone proof
sketch), see `PETER_WEYL_ROADMAP_HISTORY.md`.

For the audit confirming the reclassification holds and surfacing
related deadweight candidates, see `PETER_WEYL_AUDIT.md`.

---

## 1. Why this roadmap was reclassified

Consumer-driven recon of `YangMills/ClayCore/CharacterExpansion.lean`,
`ClusterCorrelatorBound.lean`, and `WilsonGibbsExpansion.lean` (HEAD
at commit `043a3f3`, 2026-04-22) established that
`CharacterExpansionData.{Rep, character, coeff}` are vestigial
metadata:

- `wilsonCharExpansion` fills them with `Rep := PUnit`,
  `character := fun _ _ => 0`, `coeff := fun _ _ => 0`.
- Zero external imports / citations of Peter–Weyl vocabulary outside
  `ClayCore`.
- Only `h_correlator ≡ ClusterCorrelatorBound N_c r C_clust` flows to
  the L3 cluster / Balaban consumer.

Consequence: arbitrary-irrep Peter–Weyl orthogonality (the bulk of
the original document) is **not a Clay blocker**. L2.6 was therefore
closed at 100% by sidecar reclassification — L2.5 + L2.6 main target
+ sidecars {3a, 3b, 3c} already span the integrand subalgebra that
the downstream character / Taylor expansion actually needs.

The strategic decision was correct in hindsight: Peter–Weyl was a
~6,100–13,100 LOC dependency that could be **bypassed** by working
in the scalar-trace subalgebra. The active F3 frontier sits entirely
inside that subalgebra.

## 2. Status as of 2026-04-25

Per `STATE_OF_THE_PROJECT.md` and `BLUEPRINT_F3Count.md` §−1:

- The new critical path is `ClusterCorrelatorBound` via the F3
  decomposition: F3-Mayer (Brydges–Kennedy random-walk cluster
  expansion) ⊕ F3-Count (Klarner BFS-tree lattice-animal estimate).
- v1.79–v1.83 packaged the entire F3 assembly object
  (`ShiftedF3MayerCountPackageExp`) with terminal endpoint
  `clayMassGap_of_shiftedF3MayerCountPackageExp`.
- The remaining work is two named analytic theorems:
  `connecting_cluster_count_exp_bound` (count side) and
  `truncatedK_abs_le_normSup_pow` (Mayer side, BK estimate).
- The first concrete inhabitant of `ClayYangMillsMassGap` lives in
  `AbelianU1Unconditional.lean` (with the caveat that N_c = 1 is the
  trivial gauge group; see `COWORK_FINDINGS.md` Finding 003).

None of these depend on Peter–Weyl orthogonality for arbitrary
irreps.

## 3. Why this document is preserved (not deleted)

The roadmap retains value as:

(a) **A historical record** of the analysis that led to the
reclassification. Future readers should know that the project
considered the full Peter–Weyl path before pivoting.

(b) **A Mathlib-PR / cleanup target.** Landing a proper Peter–Weyl
formalisation in Mathlib would upgrade
`CharacterExpansionData.{Rep, character, coeff}` from vestigial
`PUnit` / `0` / `0` to genuine representation-theoretic content. This
is desirable for mathematical cleanness but is **not required** for
the Clay statement. Background work only; do not block on it.

(c) **A design reference for the F3 cluster expansion.** The original
§3 Layer 4 (Kotecký–Preiss) and Layer 5 (Assembly) sections sketch
exactly the cluster-expansion structure that F3-Mayer + F3-Count
implement. The constants and convergence regime are consistent with
what the F3 blueprints arrive at independently. See
`PETER_WEYL_ROADMAP_HISTORY.md` lines 432–474 for the relevant
content.

## 4. What this roadmap does not promise (preserved verbatim)

* No claim that the full SU(N_c) roadmap is executable in a single
  Colab session, a single month, or a single reasonable project
  horizon.
* Layer 1 (full Peter–Weyl) alone is of the size of a Mathlib merge
  event; it has been a Mathlib wish-list item for years.
* Even with L1–L5 complete, `ClayYangMillsPhysicalStrong` admits
  trivial instantiations via degenerate observables or Dirac-supported
  measures; the project must separately demonstrate that the closed
  instance uses a non-degenerate `F` (e.g. a Wilson loop of non-trivial
  representation class) and the actual Wilson-Gibbs measure, not a
  pathological alternative.
* The full **continuum** Clay problem (no lattice, no cutoff) is
  strictly beyond every target in this document; `HasContinuumMassGap`
  is a statement about the lattice-to-continuum limit of
  `renormalizedMass`, which requires `a → 0` renormalisation-group
  control beyond the scope of this roadmap.

These caveats apply equally to the F3 path that supersedes this
roadmap.

## 5. References

* Osterwalder–Seiler, *Gauge field theories on a lattice*,
  Ann. Physics **110** (1978) — character expansion and small-β bounds.
* Kotecky–Preiss, *Cluster expansion for abstract polymer models*,
  Commun. Math. Phys. **103** (1986).
* Brydges–Kennedy, *Mayer expansions and the Hamilton-Jacobi equation*,
  J. Stat. Phys. **48** (1987).
* Balaban, *Large field renormalization. II. Localization, exponentiation,
  and bounds for the R operation*, Commun. Math. Phys. **122** (1989).
* Brydges, *A short course on cluster expansions*, Les Houches (1986).
* Klarner, *Cell-growth problems*, Canad. J. Math. **19** (1967).
* Madras, Slade, *The Self-Avoiding Walk*, Birkhäuser (1993),
  Chapter 3.
* Hölzl & Immler, *Peter–Weyl theorem in Isabelle/HOL* — reference
  for a comparable formalisation in a different proof assistant.
* Mathlib: `MeasureTheory.Measure.Haar.Basic`,
  `Mathlib.Analysis.Fourier.AddCircle`,
  `Mathlib.RepresentationTheory.FdRep`,
  `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`.

---

*Trimmed 2026-04-25 by Cowork agent. Original 574-line roadmap
preserved at `PETER_WEYL_ROADMAP_HISTORY.md`.*
