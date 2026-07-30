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

## AMENDMENT 7 — O-3c: the transfer operator from the measure, and the gap

**Status of the charter's registered gameability residue: REMOVED for one system.**

Amendment 3 recorded the adversarial audit's central objection, and the first
external review repeated it: every witness in the O-1 arc had the form
`r*1 + (1-r)P`, an operator built *from* the conclusion.  Nothing showed the
interface was consumable by an object arriving from a measure.  O-3c closes
that for the `Z_2` system.

`YangMills/OS/Z2Transfer.lean` defines

    z2TransferOp β = a β • 1 + b β • swapOp,
    a β = e^β / (e^β + e^{-β}),   b β = e^{-β} / (e^β + e^{-β}),

which is the normalised transfer matrix of the `Z_2` gauge system read off the
Gibbs weight.  `swapOp` is the geometric exchange of the two configurations.
No eigenvector, no projection and no spectral datum occurs in the definition.
Then:

* `z2TransferOp_fix` — the vacuum is fixed.  This is a *consequence* of
  `a + b = 1`, i.e. of normalisation, not an assumption.
* `z2TransferOp_vacuumTransfer` — it is a `VacuumTransferC` instance.
* `z2Projected_eq` — the key identity: the projected operator acts as
  `(a-b)` times the projection off the vacuum, proved componentwise from
  `a + b = 1` alone.
* `z2TransferOp_gap` — `‖T − |Ω⟩⟨Ω|‖ ≤ a − b`, by an explicit operator-norm
  bound, not by citing a spectral theorem.
* `z2A_sub_z2B_eq_tanh` — the rate is exactly `tanh β`.  Proved, because the
  module's prose names that value.
* `z2_clustering_of_transfer` — feeding this into `connCorrC_le_of_gap` gives
  exponential decay of the connected two-point function at rate `tanh β`,
  with explicit constant `2‖v‖²`, for an operator that came from the measure.

**Scope, stated so it cannot be inflated.**  The `Z_2` system here has a single
spatial variable, so its transfer operator is `2 x 2`.  A lattice with spatial
extent has a transfer operator on a larger space and is **not** treated.  The
gap is at fixed finite size; it is **not** volume-uniform, and at this size the
question does not arise.  There is no GNS quotient: the pairing of this system
is already definite, so the quotient is the identity and naming it would gain
nothing.  This is not a statement about `SU(N)`, the continuum limit, or the
Clay problem, and the Clay distance is unchanged at ~0%.

**Judge 2 of Amendment 6 (a witness that comes from a measure) is met for
`Z_2` and for no larger system.**  O-3d–g (GNS quotient where the pairing is
degenerate, spatial extent, the identification `E[A·θ_n B] = ⟪AΩ, T^n BΩ⟫`,
volume-uniformity) remain open and unclaimed.

### House note bought here (a false alarm, recorded because I raised it)

Mid-fabrication I found `IsSelfAdjoint` on `E →L[ℂ] E` elaborating with an
instance displayed as `ContinuousLinearMap.instStarId`, and flagged a possible
vacuity: if `star` were the identity, every operator would be self-adjoint and
the module's self-adjointness statements would be empty.  **The alarm was
wrong.**  `ContinuousLinearMap.star_eq_adjoint` proves `star f = adjoint f`;
the `Id` in the instance name refers to the ring hom `σ = RingHom.id`, not to
`star = id`.  The real defect was an instance-path mismatch between two routes
to the same `Star`, which `IsSelfAdjoint.smul` would not unify.  Fixed by
proving self-adjointness in coordinates instead.  Recorded because the check
cost a build and the next reader should not pay it again.

Second note, already in the ledger's house list and re-confirmed here: goals
from `isSelfAdjoint_iff_isSymmetric` sit over the **`LinearMap` coercion**, so
a lemma stated about the `ContinuousLinearMap` will not fire.  The bridge is
`ContinuousLinearMap.coe_coe` in the `simp only` set.

## AMENDMENT 8 (2026-07-28, own commit, PRE-FABRICATION) — O-3d OPENED: the identification, with its judges fixed before any measurement

Addendum 511 named the identification `E[A·θ_n B] = ⟪AΩ, T^n BΩ⟫` as the one
missing link and as the brick that would justify a third paper.  This amendment
opens it and fixes what will count as success, BEFORE the Lean exists.

**Disclosure**: I have sketched the proof on paper before writing this
amendment.  Pre-registration here means the JUDGES are fixed before the
measurement, not that the mathematics is unexplored.  The sketch is stated in
full below so that a later reader can check I did not move the target.

### The intended statement

Configurations are `σ : Fin (n+1) → Fin 2` — a chain of `n+1` time slices, each
carrying a single `Z_2` variable.  The weight is the Boltzmann product

    pathWeight β σ = ∏_{t : Fin n} exp(β · s(σ t.castSucc, σ t.succ)),
    s i j = if i = j then 1 else -1,

and the expectation is `E_n[Ā·B] = (Σ_σ conj(A(σ 0))·B(σ last)·pathWeight)/Z_n`
with `Z_n = Σ_σ pathWeight`.  The claim is that for every `n` and every pair of
observables `A B : Fin 2 → ℂ`,

    E_n[Ā(σ_0)·B(σ_n)]  =  ⟪A·Ω, (z2TransferOp β)^n (B·Ω)⟫,

with `Ω` the uniform vacuum of O-3c.

### Sketch (recorded now, so the target cannot move)

Induction on `n`, splitting the first spin with `Fin.cons`.  The step turns the
observable `A` into `A' i = Σ_s A(s)·exp(β·s(s,i)) = z2Norm β · (T A) i`, so one
factor of `z2Norm` is emitted per bond and the operator power is built up one
application at a time; closing the step needs only the SYMMETRY of the kernel,
i.e. the self-adjointness already proved in O-3c.  Taking `A = B = 1` and using
`T·1 = 1` (double stochasticity, itself a restatement of `a + b = 1`) gives
`Z_n = 2·(z2Norm β)^n` exactly, and the two `z2Norm` powers cancel.

### JUDGES (all five must pass; failure of any one is a measured failure, committed with diagnosis, not deleted)

1. **NON-CIRCULARITY.** The left-hand side must be defined using ONLY
   `Real.exp` and the sign function.  If the definition of the measure, the
   weight, or the partition function mentions `z2TransferOp`, `z2A`, `z2B` or
   `z2Kernel`, the brick FAILS.  The whole point of O-3d is that two
   independently-defined objects turn out to agree.
2. **PARTITION FUNCTION PROVED.** `Z_n = 2·(e^β + e^{-β})^n` must be a theorem.
   If it is assumed, or divided out symbolically without being computed, the
   brick FAILS.
3. **FULL QUANTIFICATION.** The identification must hold for ALL `n : ℕ` and
   ALL `A B : Fin 2 → ℂ`.  A version restricted to a subfamily of observables,
   or to small `n`, does not discharge this brick.
4. **NON-VACUITY.** An explicit `A`, `B` must be exhibited for which both sides
   are nonzero and depend on `n`.  An identity that reads `0 = 0` on every
   instance is not an identification.
5. **THE CHAIN MUST COMPOSE — the endpoint.** A statement PURELY ABOUT THE
   MEASURE, with no operator in it, derived through the operator: the two-point
   function of the sign observable decays exponentially at rate `tanh β`.  The
   pre-registered exact value is

       E_n[f(σ_0)·f(σ_n)] = (tanh β)^n,   f i = if i = 0 then 1 else -1,

   because `f` is the eigenvector of `T` for the eigenvalue `a − b = tanh β`.
   Judge 5 is the payoff: it is the first statement in this lane that is about
   a MEASURE, is proved THROUGH the transfer operator, and whose rate is the
   gap of O-3c.

### What O-3d will still NOT deliver, fixed in advance

One spatial variable; `T` remains `2 × 2`; fixed finite size, NOT
volume-uniform; the pairing stays definite so the GNS quotient remains ABSENT
rather than closed; `Z_N` for `N > 2` untouched; nothing about `SU(N)`, the
continuum limit, or Clay.  The Clay distance stays ~0% and ledger-internal.

### On the third paper

If and only if all five judges pass, the lane holds a COMPLETE machine-checked
Osterwalder–Seiler chain for one system: measure → reflection positivity →
Hilbert space → transfer operator → identification → gap → clustering.  The
paper that would then be honest is a formalization paper whose claim is that
the INTERFACES COMPOSE, exhibited on the smallest system, and whose novelty is
mechanical verification end to end — NOT new mathematics, since the 1D chain
is textbook.  Any draft claiming more than that fails its own charter.  The
submission decision remains the owner's and is not delegable.

## AMENDMENT 9 (2026-07-28, own commit, PRE-FABRICATION) — O-3e OPENED: the quotient that is not the identity

Addendum 515 froze the OS-chain paper with one honest hole named in its own
abstract: the pairing of that system is definite, so the Gelfand--Naimark--Segal
quotient is the identity and *does no work*.  Three external reviews named the
same thing.  This amendment opens the brick that removes it, and fixes what
counts as success before any Lean exists.

**Why this and not spatial extent (O-3f).**  Not because it is easier.  Because
of dependency order: with spatial extent *and* multi-slice observables the
pairing is degenerate anyway, so O-3f would be built on top of a quotient that
does not exist.  Building the hard analytic part over a missing link is the
mistake this programme exists to avoid.

### Where the degeneracy comes from — the real mechanism, not a contrived one

Half-space observables of **two time slices**, `A : Z_2 -> Z_2 -> C`, so the
observable space is `4`-dimensional.  The physical space of this chain is
`2`-dimensional.  Integrating out the future collapses four observables onto two
states; the collapse *is* the null space.  That is the mechanism
Osterwalder--Seiler reconstruction exists to handle, and it is the one that will
reappear at every larger system.

The reflected pairing is the explicit finite sum

    <A,B> = SUM_{a,b,c,d} conj(A b a) * B c d * k(a,b) k(b,c) k(c,d),

with `k = z2Bond` the Boltzmann bond weight of O-3d --- `exp` and the bond sign,
nothing else.  The map to be shown to be the reconstruction map is

    (Phi A)(c) = SUM_d k(c,d) * A c d.

### Sketch, recorded now so the target cannot move

Regrouping the four-fold sum gives `<A,B> = SUM_{b,c} conj(Phi A b) k(b,c) Phi B c`,
i.e. the pairing factors through `Phi` with the transfer kernel in the middle.
The self-pairing then rearranges into a manifest sum of two non-negative terms,

    <A,A> = (e^b - e^-b)(|v_0|^2 + |v_1|^2) + e^-b |v_0 + v_1|^2,   v = Phi A,

which delivers positivity and the null-space characterisation from one identity.
`Phi` is surjective (`4 -> 2`), so the quotient is the physical space itself.

### JUDGES (all five; failure of any one is a measured failure, committed with diagnosis, never deleted)

1. **NON-CIRCULARITY.**  The pairing must be defined from `z2Bond` alone.  If
   its definition mentions `slicePhi`, `z2TransferOp`, `z2A` or `z2B`, the brick
   FAILS.  Verified by printing definitions, as in Amendment 8.
2. **THE NULL SPACE MUST BE PROVED NON-ZERO.  THIS IS THE JUDGE.**  An explicit
   `A != 0` with `<A,A> = 0` must be exhibited and its non-vanishing proved.  If
   the null space turns out to be zero, this brick has rebuilt the trivial case
   and FAILS --- the entire purpose is a quotient that does work.
3. **EXACT CHARACTERISATION, not mere non-emptiness.**  `<A,A> = 0` must be
   proved *equivalent* to `Phi A = 0`.  Exhibiting one null vector without
   identifying the whole null space would leave the quotient undetermined.
4. **THE QUOTIENT MUST BE IDENTIFIED WITH THE PHYSICAL SPACE, and by the
   reconstruction map.**  A dimension count does not discharge this: the
   isomorphism must be induced by `Phi`, so that the quotient is the physical
   space *because of what the map does*, not because two numbers agree.
5. **REFLECTION POSITIVITY OF THIS PAIRING PROVED, not assumed**, and stated for
   the range of `b` where it holds.  The pairing is definite only for `b > 0`;
   at `b = 0` the kernel itself degenerates, and that boundary must be stated
   rather than quietly excluded.

### Fixed in advance as NOT delivered

Still `Z_2`; still one variable per slice; still fixed finite size; still not
volume-uniform; `Z_N` for `N > 2` untouched.  Two slices, not `m`.  The
completion step of the reconstruction is trivial here because everything is
finite-dimensional, and that must be said rather than presented as done work.
Nothing about `SU(N)`, the continuum limit, or Clay; the Clay distance is
unchanged at ~0% and stays ledger-internal per hard rule 6.

### On the paper

A paper is honest here only if its claim is: *the quotient step of the
reconstruction, exercised on a genuinely degenerate pairing, with the null space
computed and the quotient identified with the physical space by the
reconstruction map.*  It is not a mass-gap result, and it does not supersede the
frozen OS-chain paper --- it removes that paper's declared hole, and must say so
in those words.  Submission remains the owner's decision.

## AMENDMENT 10 (2026-07-28, own commit, PRE-FABRICATION) — O-3f OPENED: spatial extent, and the judge that exists to stop me overclaiming

The OS-chain and OS-quotient papers are submitted.  Both say in print that the
next step is spatial extent: a transfer operator on a space that grows with the
volume.  This amendment opens it and fixes what counts as success BEFORE any
Lean exists.

**I have said repeatedly, in print and to the owner, that this is where the
construction is expected to stop being easy.**  That prediction is now under
test, and this amendment is written so that a favourable-looking result cannot
be quietly reinterpreted as vindication.

### The two systems, and why both are needed

Time slices now carry `L` spins, so the state space is `Fin L -> Fin 2` and the
transfer operator acts on a space of dimension `2^L`.

* **DECOUPLED**: kernel `∏_j k_β(σ_j, τ_j)` — time bonds only, no interaction
  between spatial sites.
* **COUPLED**: the same, multiplied by a spatial weight `∏_j k_γ(σ_j, σ_{j+1})`
  that couples neighbouring sites within a slice.

The decoupled system is the one where the machinery is expected to port.  The
coupled system is the physically meaningful one, and it is the one expected to
break the construction.

### Sketch (recorded now so the target cannot move)

Row sums of the decoupled kernel factor as `∏_j (∑_t k_β(σ_j,t)) = Z_β^L`,
**independent of `σ`** — so the uniform vector stays fixed and the whole
`a + b = 1` structure of O-3c survives.  The single-site sign observable
factorises the same way and is an eigenvector with eigenvalue exactly
`(e^β − e^{-β})/Z_β = tanh β`, **independent of `L`**.

For the coupled kernel the spatial weight depends only on `σ`, so it factors
out of the sum over `τ` and the row sum becomes `w_γ(σ)·Z_β^L` — which
**depends on `σ`**.  Constant row sums fail, so the uniform vector is no longer
fixed, and `TΩ = Ω` — which in the one-dimensional chain was a free consequence
of normalisation — is FALSE.  The vacuum becomes a Perron vector with no closed
form, and every later step of the O-3c/O-3d chain loses its starting point.

### JUDGES (all five; failure of any one is a measured failure, committed with diagnosis, never deleted)

1. **THE ROW-SUM IDENTITY PROVED FOR ARBITRARY `L`**, not for small cases and
   not assumed.  This is what carries the uniform vacuum.
2. **THE EIGENVALUE EXACT AND VOLUME-INDEPENDENT.**  The decoupled non-vacuum
   eigenvalue must be proved equal to `tanh β` with `L` a free variable, so the
   independence is visible in the statement rather than inferred.
3. **THE OBSTRUCTION MUST BE A PROVED NEGATIVE**, with explicit witnesses: two
   configurations whose row sums differ, hence constant row sums fail, hence the
   uniform vector is not fixed.  An observation that "row sums look
   configuration-dependent" does not discharge this.
4. **NON-VACUITY of the obstruction**: it must be exhibited at explicit `L` and
   `γ ≠ 0`, so it cannot be an artifact of an empty parameter range.
5. **THE HONESTY JUDGE, and the reason this amendment exists.**  The decoupled
   system will yield a volume-independent rate.  That is
   **`L` non-interacting copies of a two-state system**, and its uniformity is
   therefore PHYSICALLY EMPTY — a tensor power has volume-independent spectrum
   for trivial reasons.  The paper MUST say so in the abstract, MUST NOT use the
   phrase "volume-uniform gap" as a headline, and MUST NOT present the decoupled
   result as evidence about the coupled case.  If a draft implies that a
   volume-independent rate was obtained for an interacting lattice gauge system,
   **that draft fails this charter regardless of whether its theorems are
   correct.**

### Fixed in advance as NOT delivered

No gap bound for the COUPLED system — that is the open problem, not a
deliverable here.  No continuum limit, no `SU(N)`, no `Z_N` for `N > 2`, no
Clay.  The Clay distance is unchanged at ~0% and stays ledger-internal per hard
rule 6.  Nothing here is a mass-gap result: an interacting system whose vacuum
is an unidentified Perron vector has not been given a gap by this work.

### On the paper

A paper is honest here only if its thesis is: *the algebraic half of the
reconstruction ports to spatial extent unchanged; the elementary route to the
gap does not, and here is exactly where it stops.*  The negative half is the
contribution.  A paper that leads with the positive half has misread its own
result.  Submission remains the owner's decision.

## AMENDMENT 11 (2026-07-29, POST-FABRICATION) — O-3g/O-3h CLOSED AND PAPER 6 SUBMITTED

The design ladder in `docs/O-LANE-CONTINUATION-20260728.md` produced the S-1
wall theorem and then one bounded strengthening at `L=2`.  The submitted paper
is *Blind to the Coupling: a Second Machine-Checked Obstruction at Spatial
Extent*, v1.2.1, frozen at paper commit `3d313d92` and formal anchor
`a70426f4`.  The owner reports submission on 2026-07-29; the public ai.viXra
identifier is pending and is not guessed here.

**Closed by theorem:** source- and target-factor blindness of the projective
cross-ratio; the symmetrised-kernel corollary; the exact
`exp(4 * beta * L)` witness and consequent volume degeneration; exact
two-site block eigenpairs; a strictly positive eigenvector; and domination of
every real or complex eigenvalue, making its eigenvalue the spectral radius.

**Still open and explicitly outside the submission:** a general-`L`
Perron--Frobenius theorem, uniqueness and simplicity, a volume-uniform gap for
an interacting system, and any `SU(N)`, continuum, or Clay conclusion.  The
unrestricted interacting volume-uniform target is contradicted by the recorded
numerical probe and is not a valid future goal; any positive gap target must
state an explicit small-coupling/high-temperature region.

The immutable artifact hashes, exact submission fields, and scope boundary are
recorded in
`docs/O-LANE-SUBMISSION-SPATIAL-BIRKHOFF-20260729.md`.

## AMENDMENT 12 (2026-07-29) — PUBLIC IDS VERIFIED; S-2 CLOSED IN A SEPARATE FROZEN PAPER

The public author page now lists the five preceding O-lane papers as
ai.viXra `2607.0070`, `2607.0073`, `2607.0075`, `2607.0076`, and
`2607.0078`.  Their public v1 PDFs were downloaded and each SHA-256 matches
the corresponding repository PDF exactly.  The permanent crosswalk is
`docs/PUBLICATIONS.md`.

Paper 6 remains submitted by owner report with public ID pending; no nearby
identifier is assigned by inference.

The item listed as still open in Amendment 11 has since been discharged in a
**separate** paper: `YangMills/OS/PerronKernel.lean` at anchor `08a90502`
proves, for strictly positive finite kernels, existence and positive
uniqueness of a normalized Perron vacuum, geometric simplicity, and the
spectral-radius statement.  The manuscript *A Machine-Checked Perron Theorem
for Strictly Positive Kernels, and the Coupled-Slice Vacuum at Every Spatial
Extent* is frozen at `316648e2`; submission is not reported.

This does not retroactively widen paper 6.  It also proves no strict peripheral
separation and no volume-uniform interacting gap.  The next analytic target
remains a non-vacuum bound under an explicit regime hypothesis, or a precise
no-go theorem for the available tools.

## AMENDMENT 13 (2026-07-29) — PAPER 8 SUBMITTED; STRICT WHOLE-SPECTRUM GAP AT EACH FINITE EXTENT

The owner reports submission of *Strict but Not Uniform: a Machine-Checked
Spectral Gap at Every Finite Extent of the Coupled Slice*, v1.2.  The public
ai.viXra identifier is pending and is not inferred from nearby records.

The frozen paper is `papers/perron-gap/perron_gap.pdf` at paper commit
`b03766bd`, SHA-256
`e8063013965ea1699718d08f2bce1646e73f0dd2b970a518bb9e6339c68d78a0`.
Its formal anchor is `ac897963`; the terminal endpoint
`coupled_gap_all_eigenvalues` is at
`YangMills/OS/PerronGap.lean:483`.  The exact fields and hashes are recorded in
`docs/O-LANE-SUBMISSION-PERRON-GAP-20260729.md`.

**Closed by theorem:** at every fixed finite extent, for every beta and every
strictly positive source weight, every complex eigenvalue distinct from the
Perron eigenvalue has strictly smaller modulus.  The normalized vacuum is also
packaged in the convention consumed by the Osterwalder--Seiler lane.

**Not closed:** the strict inequality carries no quantitative modulus, no
single epsilon uniform over the spectrum has been packaged, and nothing is
uniform in the spatial extent.  The reported collapse of finite-dimensional
ratios is measured and unproved.  No `SU(N)`, continuum, or Clay conclusion is
claimed.  The next analytic target therefore remains a non-vacuum bound under
an explicit regime hypothesis, or a precise no-go theorem.

## AMENDMENT 14 (2026-07-29) — PAPER 9 SUBMITTED; THE SPATIAL GIBBS MEASURE-TO-TRANSFER BRIDGE IS NOW EXPLICIT

The owner reports submission of *The Measure the Spectral Results Were About:
a Machine-Checked Transfer Bridge for the Spatial Z_2 Slice*, v1.1.  The
public ai.viXra identifier is pending and is not inferred from nearby records.

The frozen paper is `papers/spatial-gibbs/spatial_gibbs.pdf` at paper commit
`dc2935eb`, SHA-256
`92c8235c54c8c6cafa7325d1a126f8b962ea486ac9e95d2e0872ec25969ce243`.
Its formal anchor is `c4fa6a9e`; the normalised ratio and positive-denominator
endpoints are `gibbsCorr_eq_ratio_iterate` and `gibbsCorr_denom_pos` in
`YangMills/OS/SpatialGibbs.lean`.  The exact fields, artifact hashes, and scope
boundary are recorded in
`docs/O-LANE-SUBMISSION-SPATIAL-GIBBS-20260729.md`.

**Closed by theorem:** the honest finite two-dimensional Gibbs weight is
exactly the symmetrised-kernel path weight with boundary dressing; its
unnormalised two-point sum is an iterated self-adjoint transfer-matrix
element; its normalised expectation is the ratio of two such elements with
strictly positive denominator; and the fluctuation sector is invariant.
Connected decay is proved only under an explicit contraction hypothesis.

**Not closed:** Paper 8's pointwise strict spectral separation has not been
converted into the operator-norm contraction required by that decay theorem.
There is no quantitative modulus, nothing uniform in the spatial extent, and
no reflection-positivity theorem in this paper.  No `SU(N)`, continuum,
mass-gap, or Clay conclusion is claimed.  The next construction remains the
fixed-volume spectral maximum/operator-norm bridge, followed—only if the
mathematics permits—by a regime-explicit uniform estimate.

## AMENDMENT 15 (2026-07-30) — PAPER 10 SUBMITTED; THE FIXED-EXTENT MODULUS IS CLOSED

The owner reports submission of *The Modulus: a Machine-Checked Operator Bound
on the Fluctuation Sector of the Coupled Z_2 Slice*, v1.9.  The public
ai.viXra identifier is pending and is not inferred from nearby records.

The frozen paper is
`papers/spatial-spectral/spatial_spectral.pdf` at paper commit `21199f40`,
SHA-256
`200cfe770180f86aa725683d20424772e009ccc980c991faa7f03f99b42287b8`.
Its formal anchor is `9704b3f3`; exact fields and immutable artifact metadata
are recorded in
`docs/O-LANE-SUBMISSION-SPATIAL-SPECTRAL-20260730.md`.

**Closed by theorem:** `specGap` is the largest non-Perron eigenvalue modulus
and is strictly below the Perron eigenvalue; it is the sharp
fluctuation-sector operator bound; `specRatio = specGap / lambda` is below
one; Paper 9's fixed-extent contraction hypothesis is discharged; and the
normalised Gibbs two-point bound holds past an explicit threshold independent
of the observable.

**Not closed:** `specRatio` depends on the spatial extent and is not bounded
uniformly away from one.  The measured approach to one remains evidence, not
a theorem input.  Reflection positivity, `SU(N)`, the continuum limit, the
Yang--Mills mass gap, and the Clay problem are untouched.  The next positive
target must therefore state an explicit regime in which a volume-uniform
estimate could be true; an unrestricted uniform target is not authorized.
