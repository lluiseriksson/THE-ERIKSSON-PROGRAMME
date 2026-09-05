# CONTRIBUTING

The project's single law is **honesty over progress** — a smaller true claim
always beats a larger hollow one. The full working rules live in
[`CLAUDE.md`](CLAUDE.md) (they bind human contributors exactly as much as
automated ones). The short version:

## Hard rules

1. **No `sorry`** in committed code, anywhere.
2. **No `axiom` declarations** in the verified-core tree. Genuine gaps are
   carried as explicit theorem *hypotheses* and registered in
   [`HYPOTHESIS_FRONTIER.md`](HYPOTHESIS_FRONTIER.md).
3. **No vacuous weakening.** Never restate a target so it becomes trivially
   true; provide non-vacuity witnesses (non-empty parameter windows,
   non-trivial instantiations) as theorems.
4. **Oracle every headline.** `lake build YangMillsCore` green, and
   `#print axioms` must return exactly `[propext, Classical.choice, Quot.sound]`.
   Add new headlines to [`oracle_check.lean`](oracle_check.lean).
5. **Record it.** Every verified result lands as an addendum in
   [`docs/VERIFICATION-LEDGER.md`](docs/VERIFICATION-LEDGER.md) with the
   verbatim oracle output. State that lives only in chat or commit messages
   does not exist.

## Before opening a PR

* `python scripts/check_consistency.py` passes (CI enforces it).
* `lake build YangMillsCore` is green locally; note the job count.
* The ledger, the relevant `docs/*-PLAN.md`, and (if the frontier moved)
  `HYPOTHESIS_FRONTIER.md` are updated in the same PR.
* The Clay-distance statement (~0%, <0.1%) is unchanged unless you have
  genuinely reduced a named obstruction — in which case, name it.

## Review checklist

* Is the statement exactly what the docs claim it is?
* Could it be vacuously true? What is the witness?
* Are all carried hypotheses explicit in the signature?
* Does the build job count match the ledger?

## Documentation and research updates

Use [NEWS.md](NEWS.md) for short, dated developments and
[docs/HRPOLY-STATUS.md](docs/HRPOLY-STATUS.md) for the current hRpoly reading
summary. A useful update names what changed, the exact source commit and
ledger entry, the verification scope, and what remains open. Distinguish
`main` results, research-branch results, diagnostic runs and unvalidated drafts.

When updating a milestone, refresh the source snapshot and every summary that
quotes its counters. Link the detailed evidence instead of copying a full
campaign log into the front page. Preserve failed records and historical
checkpoints. Do not turn build-job counts into progress percentages or change
`project-state.json` merely because documentation was refreshed.

For documentation-only changes, review the diff, relative links, GitHub
rendering and applicable CI results. Record explicitly that no new Lean build
or mathematical verification is claimed. Changes to Lean sources, imports or
mathematical claims still require the full relevant build/oracle evidence on
the sanctioned execution plane.
