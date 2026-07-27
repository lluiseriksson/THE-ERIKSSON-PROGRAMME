# O CHARTER — "The operator bridge: from Euclidean clustering to a
# transfer-operator spectral gap" (registered 2026-07-27, BEFORE fabrication)

Owner order (2026-07-27, in-session): open the O lane after the
measurement in `docs/O-BRIDGE-AUDIT-20260727.md`; this desk FABRICATES,
external audit follows (role split per Part I regime rule 4 — this desk
does not judge its own artefact).

All Part II hard rules bind: no `sorry`, no project axioms, no vacuous
weakening, oracle every headline, job-count witness after core
integration.  All C1–C6 lessons bind: charters and amendments in OWN
commits before the work they govern; explicit staging (never `git add -A`);
hash rows from `git show`, never worktree bytes; the tricotomy of labels;
no score claimed without its external verdict.

## COORDINATION (registered now — the non-interference contract)

Concurrent lanes, from the owner: (a) **hRpoly** (Codex, Balaban
covariance: FTC of the rectangular minimiser, Neumann expansion of
`(QCQ*)⁻¹`, layer transport, physical walks); (b) **Surface Theorem
Part I** (Codex, `ladder15/16/17` certification campaigns); (c) **B-2**
(the Euclidean regime gate) — OPEN and UNCLAIMED, not this lane.

This lane works in NEW modules only, under the new namespace
`YangMills/OS/**`.  It does NOT touch:

- `YangMills/RG/**` (the whole hRpoly lane, including every `Physical*`,
  `AppendixF*`, `Catalan*`, `BalabanCMP*`, `PhysicalPoincare*` module),
- `YangMills/ClayCore/**`, `YangMills/KP/**`, `YangMills/L*/**`,
- `papers/surface-*`, `scripts/` and anything under the Part I queue.

The only shared files it will ever edit are `YangMillsCore.lean` (one
import line) and `oracle_check.lean` (one appended block), and only at
integration time; if either collides with another desk's push, resolution
is a PURE-ADDITION merge preserving both desks' lines, rebase-first.
Fabrication happens in the isolated short-path clone
`C:\Users\lluis\AppData\Local\Temp\obridge`.

## What the audit established (inputs, verbatim pointers)

- Zero occurrences of transfer operator, reflection positivity, GNS,
  spectral gap or physical spectrum in the 302 `.lean` files under
  `YangMills/` at `origin/main`.
- The M3 terminal statement `lattice_mass_gap_of_clustering`
  (`YangMills/Paper/ClusteringToGap.lean`) concludes about a function
  `cov : ℕ → ℝ`, not about any operator.
- The two satellites that would supply the link have it open:
  `lean-os-positivity` builds no GNS quotient; `lean-transfer-matrix`
  carries `gibbsTwoPoint_eq` **sorried** as its own declared "T0 honesty
  gap".
- Therefore closing hRpoly and surviving B-2 would still not produce a
  mass gap.  Bridge O is structurally independent of Bridge E.

## Phases, judges, budgets

- **Phase O-1 (THE AUTONOMOUS THEOREM; first fabrication).**
  New module `YangMills/OS/TransferGap.lean`:
  (i) `VacuumTransfer T Ω` — symmetric operator, unit vacuum, `T Ω = Ω`;
  `projectedTransfer T Ω = T − |Ω⟩⟨Ω|`; `connCorr` = the connected
  two-point function;
  (ii) `clustering_iff_gap` — an **equivalence**: exponential clustering
  at every vector at rate `r` ⟺ `‖T − |Ω⟩⟨Ω|‖ ≤ r`.  Stated as an
  operator-norm bound, deliberately NOT as `∃ gap > 0, …` (the shape of
  the vacuous terminal theorem this repository's history contains);
  (iii) `gap_of_dense_clustering` — the dense-family version, which needs
  a uniformly quadratic constant, and the module docstring stating why
  the two versions are BOTH shipped (they delimit the frontier);
  (iv) `volumeUniform_gap` — one rate `r < 1` shared across a family of
  volumes gives one mass `m = −log r > 0`, uniformly;
  (v) NON-VACUITY: `exists_vacuumTransfer_gap` and
  `euclidean_two_dim_vacuumTransfer_gap` — inhabitants with STRICTLY
  positive gap AND `projectedTransfer T Ω ≠ 0`, so no statement is
  satisfied only by the degenerate one-dimensional instance.

  **JUDGE J-O-1** (pre-registered, all five, in order, stop at first
  failure):
  1. module builds green; `#print axioms` on every headline prints
     exactly `[propext, Classical.choice, Quot.sound]`; zero `sorry`;
  2. the headline is an `iff`, and its right-hand side is not derivable
     without the left (checked by exhibiting the non-vacuity witness with
     `projectedTransfer ≠ 0`);
  3. anti-gameability: the C6 counterexample re-run — show the structure
     is NOT dischargeable by a scalar/trivial instantiation, i.e. the
     witness has a nonzero fluctuation sector and `0 < r < 1` strictly;
  4. after core integration, the build job count increments over the
     recorded 8410 baseline;
  5. adversarial self-audit for vacuous weakening, written into the
     commit message.
  Value alone (pre-registered band, absolute scale, C5 = 6.00 anchor):
  **4.5–5.5** — a correct, non-trivial, but classical operator-theory
  brick whose novelty is mechanisation plus the frontier it locates.  It
  is NOT worth more than that and no paper will claim more for it alone.
  Budget: 3 attempts.

- **Phase O-2 (THE GATE; the research risk).**  The audit's sharp
  question, now stated exactly because O-1 states it:

  > Is there a family of gauge-invariant observables, total in the
  > fluctuation sector, whose clustering constants are uniformly
  > quadratic in the Hilbert norm?

  The repository's constants are support-dependent and exponentially so
  (`C·e^{#loopSupp·4d·K}`; `C_clust = Σₙ C_conn n^dim A₀ rⁿ`), while a
  total family needs unbounded supports.  Two admissible outcomes, both
  publishable, neither promised:
  (a) a construction — a total family with uniformly quadratic constants,
      hence the operator gap from estimates of the type already proved;
  (b) a machine-checked OBSTRUCTION — the exponential support-dependence
      is not slack, and Bridge O closes negatively: a THIRD WALL in the
      format of the Poincaré-wall paper.
  **JUDGE J-O-2**: external evaluator verdict on whichever branch closes.
  ONE-SIDEDNESS RULE (Addendum 501, binding here): a favourable
  computation on any finite family is NOT a gate proof; only an
  all-families argument closes (a), only a proved lower bound closes (b).
  Budget: 3 attempts, then honest report.

- **Phase O-3 (conditional on O-2(a)).**  A fully non-vacuous instance:
  pure `Z_N` lattice gauge theory at strong coupling, where the gauge
  group is finite, every integral is a finite sum, and the whole chain
  (RP → GNS → transfer operator → identification → gap) is finite-
  dimensional linear algebra.  Target: a volume-uniform mass gap with NO
  carried hypotheses, for a genuine gauge theory.
  PRESENTATION RULE, registered now: `Z_N` is **not** SU(N); no Clay
  claim, no continuum claim, and the mother's strong-coupling VU area law
  (2607.0005) is the formal antecedent to cite.
  **JUDGE J-O-3**: non-vacuity audit (the model is not the trivial group,
  the gap is strictly positive, the fluctuation sector is nonzero) plus
  external verdict.  Budget: unset until O-2 closes.

## Kill criteria (registered now)

- O-1 needs a new axiom, or its witness has `projectedTransfer = 0` ⇒
  stop, diagnose in a commit, re-register.
- O-2 closes on branch (b) ⇒ the operator route from THIS repository's
  clustering estimates is DEAD; the charter converts to the obstruction
  paper plus a handoff naming what a different estimate would have to
  provide.  No silent pivot to an adjacent theorem.
- O-2 exhausts its budget without either branch closing ⇒ honest report,
  O-3 is NOT attempted, and the lane publishes O-1 alone at its
  pre-registered 4.5–5.5 band or not at all — owner's call.
- Any statement found vacuous at audit ⇒ same-commit retraction.
- Any collision with the hRpoly or Surface lanes ⇒ this lane yields.

## Score ladder (pre-registered, absolute scale, C5 = 6.00 anchor)

O-1 alone 4.5–5.5.  O-1 + O-2 obstruction (third wall) 5.8–6.5.
O-1 + O-2 construction 6.0–6.8.  O-1 + O-2 + O-3 (`Z_N` end-to-end,
volume-uniform, zero hypotheses) 6.5–7.2, with a distinct and separately
checkable novelty claim ("first machine-checked mass gap of a lattice
gauge theory") that must be verified against the literature by the
external desk before it appears in any abstract.  Kill risk on O-2:
50–65% on record.  No number is claimed in any paper without its external
verdict.

## AMENDMENT 1 (2026-07-27, own commit, pre-O-2 — THE SCISSORS READING IS
## RETRACTED BY THE FABRICATING DESK ITSELF)

Owner order: "continúa".  Before any O-2 fabrication, this desk retracts
a reading it published in its own audit and O-1 docstring a few hours
earlier.  Recorded here in full, because a retracted claim that is merely
deleted is the failure mode the house rule "measured failure = commit
with diagnosis, never delete" exists to prevent.

**WHAT IS RETRACTED.**  The audit
(`docs/O-BRIDGE-AUDIT-20260727.md`, section "Sharpening — the gate is a
volume-uniformity question") and the O-1 module docstring presented a
"scissors": the repository's uniform-constant estimate covers only a
local (non-total) family, while its total family (Wilson loops of
arbitrary size) carries a constant `exp((edgeSupport es).card · 4d · K)`
exponential in the support — and inferred a PRIOR favouring the
obstruction branch (b), on the ground that the two walls W-1 and W-3c
failed by the same volume-uniformity mechanism.

**THE SCISSORS DOES NOT EXIST.  The growth of the constant is
irrelevant.**  Let `S = T − |Ω⟩⟨Ω|` and

  `W := {v : ∃ C, ∀ n, ‖Sⁿ v‖ ≤ C · rⁿ}`.

`W` is a linear subspace (`C_{u+v} ≤ C_u + C_v`, `C_{cv} = |c| C_v`) — so
per-OBSERVABLE constants, however fast they grow with the support, close
up under linear combination with no uniformity at all.  And `W` is
CLOSED: it is exactly `ran E([-r, r])` for the spectral measure of `S`,
since `‖Sⁿ v‖² = ∫ λ^{2n} dμ_v` is `O(r^{2n})` iff `supp μ_v ⊆ [-r, r]`.
Dense + closed = everything, hence `‖S‖ ≤ r`.

Elementary form, avoiding projection-valued measures and using only the
CONTINUOUS functional calculus: if `λ₀ ∈ spec(S)` with `|λ₀| > r`, choose
a bump `f ≥ 0`, `f(λ₀) = 1`, supported in `{|λ| ≥ |λ₀| − δ}` with
`|λ₀| − δ > r`.  For `v ∈ W`, positivity of the calculus gives
`(|λ₀|−δ)^{2n} ‖f(S)v‖² ≤ ⟪v, (x^{2n} f²)(S) v⟫ = ‖Sⁿ f(S) v‖²
 ≤ ‖f‖_∞² C_v² r^{2n}`, so `‖f(S)v‖² ≤ ‖f‖_∞² C_v² (r/(|λ₀|−δ))^{2n} → 0`
and `f(S)v = 0`.  By density `f(S) = 0`, contradicting
`‖f(S)‖ = sup_{spec}|f| ≥ 1`.

**WHY THE ERROR HAPPENED (diagnosis, not excuse).**  `gap_of_dense_clustering`
as shipped assumes the constant is uniformly quadratic (`K‖v‖²`) because
its proof extends the bound by CONTINUITY of the quadratic form, and
continuity is what a vector-dependent constant destroys.  That is a true
statement about THAT PROOF.  This desk then read the hypothesis of its own
lemma as if it were a necessary condition of the theorem.  It is not: a
different proof (the one above) removes it entirely.  **A hypothesis that
one proof needs is not an obstruction; treating it as one is exactly the
inference the house forbids in the other direction, and it is no better
in this direction.**  The one-sidedness rule of Addendum 501 was invoked
in the audit and then violated in spirit by the desk that invoked it.

**WHAT THIS COSTS.**  The prior favouring a third wall is withdrawn.  The
obstruction branch (b) of O-2 loses its stated motivation; it is not
declared impossible, but this desk no longer has any argument for it and
must not present one it does not have.  The score ladder's
"O-1 + O-2 obstruction 5.8–6.5" line stays on the books as a possibility
with NO supporting argument behind it.

**WHAT O-2 ACTUALLY IS, RESTATED.**  With the constants question closed,
the open content of Bridge O is exactly the Osterwalder–Seiler
construction and nothing else:
  (O-2a) reflection positivity of the Wilson gauge measure in the time
         direction;
  (O-2b) the GNS quotient and the transfer operator `T` with `0 ≤ T ≤ 1`
         and `T Ω = Ω` (the object `lean-os-positivity` does not build);
  (O-2c) THE IDENTIFICATION `E[A · θ_n B] = ⟪A Ω, Tⁿ B Ω⟫` (the object
         `lean-transfer-matrix` carries sorried);
  (O-2d) that the repository's observables span a dense subspace of the
         fluctuation sector of that Hilbert space.
This is construction-heavy and CLASSICAL mathematics (Osterwalder–Seiler
1978), i.e. engineering risk rather than research risk — the opposite of
the wall-shaped phase this charter originally registered.  Kill risk is
therefore re-estimated DOWNWARD for "does it close at all" and the
schedule risk UPWARD; no numeric re-estimate is offered until a first
brick is measured, because this desk has just demonstrated what its
unmeasured estimates are worth.

**IMMEDIATE FABRICATION TARGET (O-1b, registered before it is written).**
The theorem above, as `gap_of_span_dense_clustering`: per-vector finite
constants on a set whose SPAN is dense ⟹ `‖S‖ ≤ r`, constants
unrestricted.  It removes `gap_of_dense_clustering`'s uniformly quadratic
hypothesis — but NOT as a literal subsumption of that shipped statement:
`gap_of_dense_clustering` is over ℝ and O-1b over ℂ, and the ℝ↔ℂ transport
is unproved, so the removal is available only in the complex
instantiation.  (This sentence was corrected after the adversarial audit
flagged the original "strictly SUBSUMES" as false as stated; the same
correction was applied in the module docstring.)  It needs
the continuous functional calculus, which Mathlib provides for
`IsSelfAdjoint` in a C*-algebra over ℂ only (the real instance at
`CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean:243` is derived
from the complex one via `[Algebra ℂ A]`, so it does not apply to
operators on a real Hilbert space).  Therefore O-1b is stated over a
COMPLEX Hilbert space, in its own module, and the ℝ↔ℂ bridge to O-1 is
NOT claimed — the two are separate instantiations of one argument and
saying otherwise without proof would be the same kind of unmeasured
inference this amendment retracts.
JUDGE J-O-1b: build green, oracle clean, and an explicit statement in the
module that it supersedes the scissors reading.  Budget: 3 attempts; on
failure, commit the failure with diagnosis and the retraction STANDS
anyway — the retraction is a mathematical fact independent of whether
Lean accepts this desk's formalization of it.

## AMENDMENT 2 (2026-07-27, own commit — O-1c registered, and the ℝ↔ℂ gap
## measured and declared unclosable by this lane)

Owner order: "termínalo pues", after this desk flagged that O-1 (over ℝ) and
O-1b (over ℂ) "do not count as one piece" until the ℝ↔ℂ bridge is proved.

ORDERING DISCLOSURE, so the record is not prettier than the work: this
amendment and the O-1c module were drafted in the same sitting.  The
amendment is committed BEFORE the module's commit, so the registration
precedes the artefact landing on the branch — but this desk is not
claiming the registration preceded the drafting.  The C1–C6 discipline
that amendments precede the work they govern was met in commit order, not
in wall-clock order, and saying otherwise would be exactly the kind of
tidy-looking overstatement Amendment 1 was written about.

**THE ℝ↔ℂ GAP, MEASURED.**  Closing it would mean complexifying a real
Hilbert space and transporting the operator, its norm and its self-
adjointness.  Measured against the pinned Mathlib:

- there is **no** `Complexification` anywhere under `Mathlib/Analysis/`
  (`grep -rl Complexification Mathlib/Analysis/` returns nothing; no file
  matches `*omplexif*` in the whole library);
- every route to a real continuous functional calculus for `IsSelfAdjoint`
  passes through `[CStarAlgebra A]`, which in Mathlib is a **complex**
  C*-algebra (`ContinuousFunctionalCalculus/Basic.lean:186`,
  `Instances.lean:243`, both via `Complex.reCLM` / `[Algebra ℂ A]`).

So the bridge requires building the complexification from scratch: the
space, its inner product, completeness, the operator extension, and norm
equality.  That is a Mathlib-contribution-sized project, and it is
**TOOLING, not mathematics** — the mathematical content of O-1b is already
proved.  DECLARED: this lane does NOT attempt it and does NOT claim it.
The consequence is stated in every affected docstring: O-1 is the ℝ
statement, O-1b/O-1c the ℂ statements, and **the sharp dense-family form
is available over ℂ only**.

**O-1c (registered).**  New module `YangMills/OS/SharpBridge.lean`: rebuild
the bridge's own objects over ℂ — `vacuumProjectionC`, `projectedTransferC`,
`connCorrC`, `VacuumTransferC` — so that O-1b's sharp theorem applies to a
transfer operator with a vacuum rather than to a bare self-adjoint operator.
Headline `sharp_clustering_iff_gap`:

  `‖T − |Ω⟩⟨Ω|‖ ≤ r  ↔  ∃ D, Dense (span ℂ D) ∧
     ∀ v ∈ D, ∃ C, ∀ n, ‖connCorrC T Ω v n‖ ≤ C · rⁿ`

— an EQUIVALENCE, with per-observable constants and **no relation assumed
between them**, so `C = e^{c·support}` is admissible.  Plus
`volumeUniform_sharp_gap` and non-vacuity witnesses over ℂ with a nonzero
fluctuation sector.  This is what closes "the two modules do not compose":
after O-1c there is ONE self-contained chain over ℂ, from the objects to
the sharp equivalence.

JUDGE J-O-1c (pre-registered): (1) build green, oracle exactly the
permitted triple or a subset, zero `sorry`; (2) the headline is an `iff`;
(3) non-vacuity witness with `projectedTransferC ≠ 0` and `0 < −log r`,
hypotheses discharged concretely in `EuclideanSpace ℂ (Fin 2)`; (4) job
count increments against THIS desk's own measured baseline, never against
the ledger's inherited 8410; (5) the ℝ↔ℂ gap stated in the module, not
implied away.  Budget: 3 attempts.

VALUE: O-1c adds no new mathematics beyond O-1b — it is the composition
brick.  The pre-registered band for the whole of O-1/O-1b/O-1c together
stays **4.5–5.5**, unchanged: composing one's own bricks does not raise a
score, and the equivalence remains classical (Glimm–Jaffe §19).

## AMENDMENT 3 (2026-07-27, own commit) — the adversarial audit verdict, the
## five defects and their fixes, the paper phase, and the registered
## continuation

Owner order: "pushea, audita, escribe paper con links de verificación en la
repo."  Recorded in the order the work happened.

**PUSH — ATTEMPTED, BLOCKED, NOT DONE BY THIS DESK.**  The arc was rebased
onto `origin/main` (which had advanced by two `DASHBOARD.md`-only commits,
zero `.lean`), the replay was recorded with byte-level blob equality
(`ad9c93d7`), and `git push origin HEAD:main` was run.  It failed: the
stored GitHub token is invalid (`Password authentication is not supported`;
`gh auth status` reports the keyring token invalid).  Re-authenticating
means entering credentials, which is the owner's action and not this
desk's.  All commit hashes are already final, so every permalink in the
manuscript resolves the moment the owner authenticates and pushes.

**AUDIT — PERFORMED IN A SEPARATE CONTEXT, NOT BY THIS DESK.**  Honesty
note on what that is and is not: the auditor was a separate reasoning
context with read-only access, instructed adversarially and forbidden to
build.  That satisfies "a different session audits before merging" in
substance.  It is NOT the external evaluator this house uses to fix
scores, and the score below is therefore an audit opinion, not a
registered verdict.

VERDICT: all nine judge marks (J-O-1 ×5, J-O-1b, J-O-1c) CONFIRMED, with
the reverse direction of O-1 independently re-derived, the cut-off
argument checked line by line, the three module blob SHAs recomputed, and
the transcript counts verified as 2249+22 / 2264+22 / 2282+22.  No
vacuity.  No gameability.  No Yang-Mills, continuum, Clay or OS-space
overclaim anywhere in three modules, two governance docs, nine commit
messages or the manuscript.  Audit score 5.0–5.2, judging the
pre-registered 4.5–5.5 band CORRECT.

FIVE DEFECTS FOUND, ALL FIXED before the paper was sealed:
1. MODERATE, a genuine self-contradiction: "strictly subsumes
   `gap_of_dense_clustering`" was FALSE as stated — that theorem is over ℝ,
   the sharp form over ℂ, and the same documents declare the transport
   unproved.  Fixed in the O-1b docstring and in Amendment 1 above.
2. `Bⁿ v → 0` for every `v` was asserted for a general self-adjoint `S`;
   it fails when `±‖S‖` is an eigenvalue (the powers converge to the
   eigenprojection).  True for the load-bearing `L²[0,1]` example.  The
   same overclaim was in the manuscript.  Fixed in both.
3. The retraction banner in `docs/O-BRIDGE-AUDIT-20260727.md` was scoped
   to one paragraph while the superseded scissors framing continued past
   it unmarked.  Banner extended to the whole section.
4. A bare `def` docstring read the norm bound as "mass gap `m`"
   unconditionally.  Made conditional on `VacuumTransfer` and on `0 ≤ T`.
5. No `docs/VERIFICATION-LEDGER.md` addendum existed for the arc, against
   the Part II loop rule.  Added as **Addendum 510**.

**PAPER PHASE (registered here, after the fact — disclosed).**  The
manuscript `papers/o-bridge/o_bridge.tex` + `.pdf` (tex and pdf in the
same commit, tectonic clean, 7pp) was written before this phase was
registered in the charter; the audit flagged exactly that.  Registered now
rather than backdated.  House discipline observed: tricotomy, no scores, no
desk language, no commit chronology beyond the freeze; freeze declared
in-paper as the Lean tree of `ad9c93d7` with 8415 jobs and 2304 oracle
invocations; provenance discharged by citing Glimm–Jaffe §19, Simon and
Osterwalder–Seiler for the classical equivalence, with NO novelty claimed
for it, and 2607.0005 as the same-programme formal antecedent for the
area-law constant shape.  All ten permalink targets were verified to exist
at the anchor commit before compiling.  SUBMISSION IS THE OWNER'S CLICK;
this desk does not submit.

**REGISTERED CONTINUATION (the audit's own recommendation, adopted).**
Every witness in the arc is `r·1 + (1−r)P` — an operator built *from* the
conclusion.  Nothing yet shows the interface is consumable by an object
coming from a measure, and that is the arc's remaining gameability
residue.  Next brick: an instance of `VacuumTransferC` derived from a
measure — the O-3 seed, `Z_N` pure gauge at one small volume, where
reflection positivity, the GNS quotient and the identification are
finite-dimensional linear algebra.  Until that exists, O-1c is a
self-composed brick and the charter says so.

## AMENDMENT 4 (2026-07-27, own commit) — EXTERNAL REVIEW RECEIVED; paper
## revised to v1.1; all seven revision items accepted

An external review of the v1.0 manuscript was relayed by the owner.
Recorded on ITS OWN SCALE and not converted to this house's absolute
scale, because converting a foreign scale would be fabrication:

  manuscript as submitted            86/100
  after editorial + bibliographic revision   90/100
  as first part of a chain including RP, OS reconstruction and a gauge
  transfer operator                  95/100 or more
  recommendation: strong accept as a short paper; weak accept / accept as
  a regular paper after the stated revisions
  per-criterion: scope honesty 10/10, reproducibility 9.5/10, potential as
  O-2 base 10/10, MATHEMATICAL NOVELTY 6–7/10 pending prior art.

The reviewer's core reading is adopted: the real headline is not the
elementary equivalence but the dense-family criterion — a common rate
plus dense span suffices, with arbitrary per-observable constants.

SEVEN ITEMS RAISED.  ALL SEVEN ACCEPTED AND APPLIED:

1. **A GENUINE DEFECT.**  The v1.0 abstract said "a symmetric bounded
   operator `T` with a fixed unit vector `Ω`", which does not state
   `T Ω = Ω`.  Without it the abstract's claim is not correct — the
   structural identity needs it.  Fixed: the abstract now says "a unit
   vector *fixed by* `T`, so that `T Ω = Ω`".  This was the reviewer's
   most important item and they were right.
2. Title was too absolute ("the Irrelevance of Observable-Dependent
   Constants"): the constants are harmless only given a common rate AND
   dense span.  Retitled "A Machine-Checked Dense-Family Criterion" with
   the prefactor claim demoted to a subtitle, and the two provisos are
   now stated in the abstract as essential.
3. `D_r(S)` was defined for `r ∈ ℝ` with an unconstrained `C`.  Paper now
   defines it for `r ≥ 0`, `C ≥ 0`, and states explicitly that the Lean
   definition is unconstrained and carries `r ≥ 0` at each use site.
4. **Prior art.**  Accepted in full and taken further than asked: the
   paper now states that NO mathematical novelty is claimed for the sharp
   criterion either, names the likely home (spectral subspaces / local
   spectral radius, `D_r(S) = ran E([-r,r])`), states that no exhaustive
   search was performed, and invites the closest antecedent.  What is
   claimed is the mechanization, the packaging for families with
   per-member constants, and the corollary.
5. "and nothing else" removed.  Replaced by "within the abstract
   implication isolated here, the remaining bridge obligations are…",
   plus an explicit non-exhaustiveness paragraph naming vacuum
   uniqueness, all-times rate control, the gauge-invariant sector, the
   Hamiltonian relation and the volume/spacing limit.
6. Area law separated from application: an explicit paragraph now says
   the area-law theorem is used ONLY to motivate the shape of the
   constant, supplies no dense family, no time-direction correlator, no
   common rate and no identification with `T^n`, and that nothing in the
   paper brings a mass gap closer to being deduced from an area law.
7. New Section "Formalization architecture": the module chain, what
   Mathlib did not provide, and two devices that may be reusable (the
   hand-proved `‖S²‖ = ‖S‖²`, so the real module needs no C*-algebra API;
   and the everywhere-positive denominator `max(c,|x|)^{2n}`, which makes
   the cut-off continuous with no case analysis and safe when `0` is in
   the spectrum).
   ON THE REVIEWER'S "minimal build target" SUGGESTION — MEASURED AND
   REPORTED AS NOT DELIVERING WHAT IT PROMISES: the isolated closure of
   the three modules is **8160 jobs** against the core's 8415.  Because
   the modules `import Mathlib` wholesale, essentially all of both figures
   is Mathlib from cache; a separate minimal target would not
   meaningfully reduce a referee's work.  The paper says so, and says the
   8415 figure is integration evidence rather than a measure of the
   paper's size.  No new library target was added, which also avoids
   touching `lakefile.lean` — a shared file outside this lane's
   registered coordination contract.

Presentation items also applied: abstract shortened; the "not elementary"
remark split into three labelled paragraphs under a subsection heading;
"linear subspace" used in the mathematical exposition with "submodule"
reserved for the Lean map.

RESULT: `papers/o-bridge/o_bridge.{tex,pdf}` v1.1, tectonic clean, 8pp,
zero overfull boxes, all ten verification links unchanged and still
resolving to paths that exist at the freeze commit.  No Lean was touched;
the freeze anchor is unchanged.

## AMENDMENT 5 (2026-07-27, own commit) — second external review; paper
## frozen at v1.2 for submission

Second review of v1.1, recorded on its own scale: manuscript quality
92/100, submission readiness 90/100, standalone importance 86–89/100,
value as the foundation of a complete Bridge O 96/100; strong accept as a
short paper, accept as a regular paper at a formalization venue.
Mathematical novelty 6/10 "correctly declared" — the v1.1 decision to
disclaim novelty for the criterion was accepted as the right call.

**ONE GENUINE MATHEMATICAL DEFECT IN THE PRINTED PROOF, now fixed.**  The
v1.1 proof sketch of the equivalence applied Banach–Steinhaus to the
family `r^{-n} S^n`, which is undefined at `r = 0`, and used
`G_v(2n) = ⟨v, S^{2n} v⟩` without restricting to `n ≥ 1` — the structural
lemma gives that identity only for positive times, and `G_v(0) ≠ ⟨v, v⟩`
in general.  The LEAN PROOF ALREADY CASE-SPLIT ON `r = 0` CORRECTLY; the
defect was in the printed argument only, which is exactly the kind of gap
between formalization and exposition a formalization paper must not have.
The sketch now separates `r = 0` (where `‖Sv‖² = G_v(2) ≤ 0` forces
`S = 0`) from `r > 0`, and states the `n ≥ 1` restriction explicitly.

Also applied: `0 ≤ r < 1` added to the prefactor corollary; the claim
"uniformity in `i` is not an added hypothesis" corrected — the common
rate `r` IS a uniform cross-volume input, and what is not assumed is
uniformity of the constants, which is the stronger and more accurate way
to put it; the spectral identity `D_r(S) = ran E([-r,r])` explicitly
marked as the conceptual reading and NOT separately formalized, since it
does not appear in the theorem-to-artifact map; "not established here,
anywhere, in any form" narrowed to "not established in this paper, nor
anywhere in the Lean development accompanying it", which is what was
meant and cannot be read as a claim about the literature; and the
overstatement "Lemma 4.2 is the entire content of the sharpening"
replaced — the lemma is the algebraic step from a family to its span, the
substantive mathematics is the functional-calculus argument.

BIBLIOGRAPHY: a local-spectral-theory reference was requested and added —
Laursen and Neumann, *An Introduction to Local Spectral Theory*, LMS
Monographs New Series 20, Clarendon Press / OUP, 2000.  The citation was
VERIFIED against the publisher record rather than cited from memory
(ISBN 9780198523819); note the OUP listing spells the second author
"Neuman", while the standard citation form is "Neumann", which is what is
used.  With it, "we expect the criterion to be known" now reads as a
bibliographic location rather than a bare guess.

RESULT: v1.2, tectonic clean, 8pp, zero overfull boxes, no undefined
references, all ten verification links unchanged.  NO LEAN WAS TOUCHED in
either revision round; the freeze anchor `ad9c93d7` is unchanged, and the
paper is frozen for submission at this version.  Submission remains the
owner's click.

## AMENDMENT 6 (2026-07-27, own commit, PRE-FABRICATION) — O-3 OPENED, and
## O-2/O-3 REORDERED

Owner order: "dale", after the O-1 arc was pushed to `main` (`80406f29`)
and the manuscript submitted.

**REORDERING, and why.**  The original charter made O-3 (a non-vacuous
instance) *conditional on O-2* (the Osterwalder–Seiler construction).
That order is now inverted.  Both the adversarial audit and the external
review converged independently on the same residue: every witness in the
O-1 arc is `r·1 + (1−r)P`, an operator built **from** the conclusion, so
nothing yet shows the interface is consumable by an object coming from a
**measure**.  O-3 is therefore not a victory lap after O-2 — it is the
cheapest complete instance of O-2's own chain, on a group where every
integral is a finite sum, and it de-risks the expensive version.

**O-3 — the target.**  Pure `Z_N` lattice gauge theory on a finite box
with one distinguished time direction: build the whole
Osterwalder–Seiler chain and *consume* `sharp_clustering_iff_gap` with
it.  Gauge group finite ⇒ the configuration space is a finite type, every
expectation is a `Finset.sum`, and no measure theory is required.

Brick ladder, each to be measured on its own:
- **O-3a** substrate: finite configuration type, the Wilson weight
  `w(U) > 0`, the time reflection `θ`, the half-space observable algebras.
  Non-vacuity: `N ≥ 2` and a box with at least two time slices.
- **O-3b** REFLECTION POSITIVITY.  **This is the load-bearing brick and
  the one that can kill the phase.**  The content is that the plaquettes
  straddling the reflection plane contribute a kernel with a non-negative
  character expansion.  Registered risk: whether the site-reflection or
  the link-reflection form is the one that closes, and at which `N`.
- **O-3c** the GNS quotient: the pairing `⟨F,G⟩ = E[θF̄ · G]`, positive
  semidefinite by O-3b, quotiented by its null space.  TOOLING RISK to be
  measured BEFORE fabricating: whether Mathlib can build an
  `InnerProductSpace` from a PSD sesquilinear form on a finite-dimensional
  space without hand-rolling it.
- **O-3d** the transfer operator `T`: self-adjoint for the GNS inner
  product, `T Ω = Ω` with `Ω` the class of the constant function, and
  `0 ≤ T ≤ 1`.
- **O-3e** THE IDENTIFICATION `E[A · θ_n B] = ⟪AΩ, Tⁿ BΩ⟫` — the object
  `lean-transfer-matrix` carries sorried, here proved by Fubini on finite
  sums.
- **O-3f** the endpoint: instantiate `VacuumTransferC` from O-3d and apply
  `sharp_clustering_iff_gap`.

**JUDGE J-O-3 (pre-registered, in order, stop at first failure).**
1. Build green, oracle within the permitted triple, zero `sorry`.
2. **THE WITNESS COMES FROM THE MEASURE.**  The `VacuumTransferC`
   instance must be *constructed from* the Wilson weight, not postulated;
   a proof that merely exhibits another hand-built operator FAILS this
   judge outright.  This is the entire point of the phase.
3. `sharp_clustering_iff_gap` is actually APPLIED, not merely cited.
4. Non-vacuity: `N ≥ 2`, box nontrivial, fluctuation sector nonzero — the
   endpoint must not be satisfiable by the trivial group or a
   single-slice box.
5. Job count measured against this desk's own baseline (currently 8415),
   never against an inherited figure.

**KILL CRITERIA.**  If O-3b does not close within budget, the phase STOPS
and reports; there is no point building GNS on a pairing not known to be
positive.  If O-3c's tooling probe shows Mathlib cannot supply the
quotient without a disproportionate hand-rolled construction, that is
reported as a tooling wall and the phase is re-scoped, not forced.  Budget:
3 attempts per brick.

**SCORE BAND, unchanged from the original registration: 6.5–7.2** for the
complete chain, with the novelty claim ("first machine-checked mass gap of
a lattice gauge theory") to be VERIFIED AGAINST THE LITERATURE by an
external desk before it appears in any abstract.  Stated plainly in
advance: `Z_N` is **not** `SU(N)`, the underlying mathematics is easy, and
the entire value is mechanization plus completeness of the chain.  No Clay
claim, no continuum claim, at any point.

**COORDINATION unchanged.**  New modules under `YangMills/OS/**` only.
The concurrent lanes are hRpoly (Codex, branch
`codex/cmp116-interacting-wilson-hessian`, head `1b181bad`, 993 commits
ahead of main and now PUBLISHED) and Surface Part I (Codex, branch
`codex/maintenance-baseline`, head `ea7367a6`, external audit in flight).
Neither is touched by this phase.

## What this lane will never claim

Progress on the Clay problem; anything about the continuum limit;
anything about SU(N) beyond what a proved reduction transfers; and no
"mass gap" wording for any statement whose conclusion is the decay of a
real-valued function.
