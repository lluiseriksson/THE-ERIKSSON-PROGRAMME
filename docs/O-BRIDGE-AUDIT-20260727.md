# O-BRIDGE AUDIT — 2026-07-27 (the operator-side link, never audited)

Desk: O (isolated clone `C:\Users\lluis\AppData\Local\Temp\obridge`).
Method: read-only measurement over `origin/main` at `15792bb` (the last
substantive commit is `b6c9a28`, 2026-07-14, Addendum 509; everything
after it is the `dashboard [skip ci]` bot).  No file in any live clone
was touched to produce this document.

Status of this document: AUDIT (measurement + consequence).  It makes no
mathematical claim of its own and grants no credit to any lane.  The
house honesty rule applies verbatim: importance is not inherited by
thematic proximity, only a proved reduction transfers it.

## Verdict in one line

`docs/M3-BRIDGE-AUDIT-20260713.md` located the weakest link on the
EUCLIDEAN side (the identification of `covIR + covUV` with the Wilson
truncated two-point function).  There is a SECOND link, structurally
independent of it and never audited: even a perfect Euclidean correlator
with exponential decay does not produce a mass gap, because a mass gap is
a statement about the spectrum of an operator and **no operator exists
anywhere in this tree**.

## The measurement (reproducible)

Over the 302 `.lean` files under `YangMills/` at `origin/main`:

| searched token | occurrences |
|---|---|
| `transferOperator` / `TransferOperator` | 0 |
| `reflectionPositiv*` / `ReflectionPositiv*` | 0 |
| `HasStrictSpectralGap` / `spectralGap` | 0 |
| GNS construction | 0 |
| physical Hilbert space of states | 0 |
| Hamiltonian / physical spectrum | 0 (1 prose mention, `Paper/GapRefinementChallenge.lean:30`) |

Reproduce with:

```bash
git grep -i -c 'transferOperator\|reflectionPositiv\|spectralGap\|GNS' origin/main -- 'YangMills/**'
```

Two dangling references were found in passing and are NOT counterevidence:
`YangMills/ErikssonBridge.lean:2` imports `YangMills.P7_SpectralGap.Phase7Assembly`
and `OracleC97`–`OracleC100` import `YangMills/P8_PhysicalGap/Vacuum*.lean`;
none of those modules exists at `origin/main` (they survive only in
`archive/old-main-v2.234`).  They are stale roots outside `YangMillsCore`,
not operator-side content.  Registered as a hygiene item for the Part II
desk, not as a defect of any live theorem.

## The consequence

The terminal statement of the M3 lane is
`lattice_mass_gap_of_clustering` (`YangMills/Paper/ClusteringToGap.lean`):

```lean
theorem lattice_mass_gap_of_clustering (covIR : ℕ → ℝ) (covUV C1 C2 r c0 : ℝ) (t : ℕ) … :
    ∃ gap : ℝ, 0 < gap ∧ |covIR t + covUV| ≤ (C1 + C2) * Real.exp (-(gap * t))
```

Its conclusion is the decay of a real-valued function.  The module's own
docstrings are honest about the scope (they say "conditional lattice
result", and they correctly disclaim OS1/O(4) and the continuum limit),
so this audit records **no dishonesty**; what it records is a structural
consequence that is nowhere registered:

> Closing hRpoly and surviving B-2 would make the *Euclidean decay*
> statement unconditional.  It would still not produce a mass gap.  The
> step from "the truncated correlator decays" to "the transfer operator
> has a spectral gap" is the Osterwalder–Seiler theorem, and none of its
> ingredients — reflection positivity of the Wilson measure, the GNS
> quotient, the transfer operator, the identification of the Euclidean
> correlator with a matrix element — exists in this repository or in any
> satellite in provable form.

Satellite state (from `docs/CROSS-REPO-RECON-20260713.md`, §1 Bridge 3 and
§3): `lean-os-positivity` proves the reflection Cauchy–Schwarz pairing
calculus and RP instances but **constructs no GNS quotient**;
`lean-transfer-matrix` publishes `TransferOperatorInterface` /
`HasStrictSpectralGap` and one hypothesis-free instance, but its
`gibbsTwoPoint_eq` — the identification itself — is **sorried** on its
frontier branch and labelled a "T0 honesty gap" there.  So the operator
link is not merely absent from the mother: it is the acknowledged hole of
the two satellites that would supply it.

## Why this is a distinct lane, not a restatement of B-2

The two links fail for unrelated reasons and can die independently:

- **Bridge E (Euclidean, = C6/B-1 + B-2).**  Question: is there one
  coupling at which the proved IR input and the planned UV input are
  about the same measure?  Failure mode: regime incoherence.
- **Bridge O (operator, this audit).**  Question: does exponential decay
  of the correlators the expansion controls imply a spectral gap of the
  Osterwalder–Seiler transfer operator?  Failure mode: the constants.

Bridge O can be attacked with Bridge E entirely open, and vice versa.
Neither subsumes the other, and closing both is necessary — not
sufficient — for the word "mass gap" to be earned at fixed lattice
spacing.

## What the O-1 brick then measured (fabrication result, same desk)

`YangMills/OS/TransferGap.lean` proves the autonomous half and, in doing
so, converts the vague worry above into a sharp dichotomy.  Two theorems,
deliberately both:

- `clustering_iff_gap` — clustering **at every vector of the Hilbert
  space**, with a constant free to depend on the vector, is EQUIVALENT to
  the gap.  Uniformity is bought by Banach–Steinhaus, i.e. by
  completeness, at no cost.
- `gap_of_dense_clustering` — clustering on a merely **dense set** implies
  the gap only when the constant is uniformly quadratic (`K‖v‖²`).  The
  proof is continuity of the quadratic form; a dense subspace is meagre,
  so no Banach–Steinhaus substitute exists.

A cluster expansion produces the second shape, never the first: it bounds
a *family* of observables.  And here the repository's own two estimates
sit on opposite horns, which is what makes the gate sharp rather than
merely hard:

- `ClayCore/ExponentialClustering.lean`: the connecting-cluster constant
  `C_clust = Σₙ C_conn · n^dim · A₀ · rⁿ` is **uniform** — it does not see
  the observable at all.  But the family it covers is the two-plaquette
  correlator: a *fixed, local* family, which is **not total** in the
  fluctuation sector.  Uniform constant, family too small.
- `L1_GibbsMeasure/RestrictedGate.lean`, `normalized_wilson_loop_area_law_unconditional`:
  covers Wilson loops of arbitrary size — large enough to be total — but
  its constant is, verbatim from the conclusion,
  `N_c · exp((edgeSupport es).card · 4d · K) · σ^{chainArea} ·
   exp((edgeSupport es).card · 4d · S(σ))`,
  **exponential in the edge support of the loop**.  Family big enough,
  constant not uniformly quadratic.

The rate `r` is uniform in both (it is the polymer activity rate); it is
the *constant* that fails, and it fails on exactly the horn where the
family becomes total.

> **RETRACTED THE SAME DAY BY THE DESK THAT WROTE IT — see AMENDMENT 1 in
> `docs/O-BRIDGE-CHARTER.md`.**  The "sharpening" below, and the prior it
> derives favouring a third wall, are WRONG.  The growth of the constant is
> irrelevant: `W = {v : ∃C, ∀n, ‖Sⁿv‖ ≤ C rⁿ}` is a subspace (so
> per-observable constants close up under linear combination with no
> uniformity) and is closed (it is `ran E([-r,r])`), so dense + closed
> forces `‖S‖ ≤ r` whatever the constants do.  The paragraph is kept
> unmodified below because the house rule is that measured failures are
> committed with a diagnosis, never deleted.  The diagnosis: this desk read
> a hypothesis its own proof needed as if it were a necessary condition of
> the theorem.

**Sharpening — the gate is a volume-uniformity question.**  At FIXED
finite volume the scissors does not bite: loops have support bounded by
the volume, the constant is finite, and (the Hilbert space being finite-
dimensional) a gap exists for trivial reasons.  What the exponential
support-dependence destroys is the *volume-uniform* statement: a total
family in volume `Λ` needs supports growing with `Λ`, so the constant
grows like `e^{c|Λ|}` while `‖A‖²_{L²}` stays `O(1)` for a Wilson loop.
Bridge O's gate is therefore the SAME KIND of question as `W-1` and
`W-3c` — both of which closed as walls — and this is registered here as
raising the prior on outcome (b), NOT as evidence for it.  A prior is not
a proof; the one-sidedness rule below still binds in both directions.

So the O-2 question is not vague — it is a two-sided question about
closing that scissors:

> Is there a family of gauge-invariant observables, total in the
> fluctuation sector, whose clustering constants are uniformly quadratic
> in the Hilbert norm?

If yes: the operator gap follows from estimates of the type this
repository already proves, and Bridge O closes positively.  If provably
no: Bridge O closes negatively and the result is a THIRD WALL in the
format of the Poincaré-wall paper — the exponential support-dependence is
not a slack bound but an obstruction.  This audit does not prejudge it,
and no favourable computation will be treated as a gate proof (the
one-sidedness rule of Addendum 501 applies).

## Counters, measured by this desk (not inherited)

| quantity | value | how |
|---|---|---|
| ledger-recorded jobs (Addendum 503, commit `12ca1a87`) | 8410 | inherited, NOT re-measured |
| `lake build YangMillsCore` at `origin/main` **today** | **8412** | measured, this desk |
| same, with `YangMills/OS/TransferGap` imported | **8413** | measured, this desk |
| O-1's own contribution | **+1** | the difference of the two measurements |
| `#print axioms` commands in `oracle_check.lean`, before | 2250 | measured |
| same, after O-1's appended block | 2271 | measured (+21) |

LEDGER HYGIENE NOTE for the Part II desk: the +2 between the recorded 8410
and today's measured 8412 is `PhysicalPoincareLowModeHodge` (W-3b,
Addendum 506) and `PhysicalPoincareLowModeBlock` (W-3c, Addendum 507),
which landed after the 8410 checkpoint was sealed.  Had this desk
subtracted against the inherited 8410 it would have claimed +3 for O-1
instead of the true +1.  Recorded here so the next desk subtracts against
a measured baseline, not a thirteen-day-old one.

## Unchanged by this document

Clay distance ~0% (<0.1%).  `hRpoly` OPEN and untouched (Codex lane).
Surface Theorem Part I OPEN and untouched (Codex lane).  B-2 OPEN and
unclaimed.  Nothing here is a claim about Yang–Mills, the continuum
limit, or the mass gap of any gauge theory.

## Operational hazard found in passing (not a mathematics item)

The designated push clone `C:\Users\lluis\AppData\Local\Temp\eriksson-push2`
sits at HEAD `bbd4de16` (2026-07-14) with **1083 unstaged deletions** in its
working tree and 5 untracked files.  A `git add -A` from that clone would
commit the deletion of 1083 tracked files.  This is the exact failure the
Part I class rule 9 was written against.  No desk should push from it until
it is reset or abandoned; this desk uses its own clone and never touched it.
