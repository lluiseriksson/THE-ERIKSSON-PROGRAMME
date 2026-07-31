# SU(2) two-transporter no-go — intake status, 2026-07-31

## Public object

- Draft PR: [#39](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/39)
- Branch: `codex/su2-two-transporter-nogo-20260731`
- Audited candidate SHA: `1fa29e657c43ed71a249808611bf3aea64f2b115`
- Commit subject: `clarify totalized integrals and no-go evidence split`
- Integration state: **draft, unmerged, not imported by `YangMillsCore`**

The remote SHA and commit order were checked independently before this intake
record was written.  The two final documentation qualifications were already
present at `1fa29e65` before the reported audit ran.

## Result carried by the draft

The new module states a left-Haar projection theorem for two freely and
independently integrated transporters and specializes it to the reduced SU(2)
Wilson weight.  For observables independent of the transporters, both audited
orientations collapse to the trivial Haar sector.  In particular the
fundamental trace, whose Haar mean is zero, has zero quadratic form in the two
free-transporter construction.

The negative conclusion is deliberately narrower than a physical lattice
statement:

- it does not derive the common transporter of the frozen SU(2) reflection
  lane by gauge fixing;
- it does not rule out correlated or restricted transporters;
- it does not rule out observables that depend on the transporters;
- it does not construct a physical `GaugeConfig` cell or prove OS positivity;
- the strict comparison with the frozen `beta/4` result is a documented
  cross-SHA comparison, not an import into the new Lean module.

The producing session reports an 8159-job target build, an oracle containing
only `propext`, `Classical.choice`, and `Quot.sound`, a clean forbidden-token
scan, and two identical executions of the finite exact certificate with
SHA-256 `9228daedb29d1d62e1f63b5d2ffe66be4be2b195a987ba1358edd828d9c23201`.
Those measurements belong to PR #39 and are not promoted here into a merged
core checkpoint.

## Audit classification

The producing task reports `PASS WITH NOTES` on the exact SHA `1fa29e65`.
However, neither PR #39 nor its six-file diff contains a durable audit report
that identifies whether the auditor was a fresh blind session or a context-
inheriting subagent of the manufacturer.  Until that provenance is recorded,
the PASS is classified here as **non-terminal internal review**.  It does not
discharge the requested independent terminal audit.

This classification is about independence, not about a discovered mathematical
defect.  The reported audit found none of high severity and independently
rechecked the left-Haar reductions, the quaternion witness, the concrete Wilson
weight, the separation between formal collapse and paper comparison, and the
standard axiom set.

## CI attribution correction

The red `Validate repository control plane / test` check on PR #39 reports
`4134` validation errors across `623` committed run manifests.  The sentence
"the same failure appears in main" was not supported by a cited `main` run:
recent `main` runs visible at intake contained the honesty and Pages workflows,
not this path-filtered `test` job.

The non-attribution to PR #39 nevertheless has a stronger, directly checkable
basis: its diff contains exactly six paths — `.gitignore`,
`HYPOTHESIS_FRONTIER.md`, one new Lean module, one oracle, one documentation
file and one finite certificate — and **no run manifest or manifest validator**.
Therefore the manifest failures cannot have been introduced by this diff.

The underlying backlog is repository-level control-plane debt.  A validator
that fails on the unchanged historical inventory makes every qualifying PR red
and destroys the check's power to distinguish a new regression from inherited
state.  It needs a separate repair or an explicitly baselined/quarantined
migration; silently weakening the validator is not an acceptable repair.

## Next admissible actions

1. Record the audit's session/provenance facts.  If it was not fresh and blind,
   run a genuinely independent read-only audit on `1fa29e65`.
2. Keep PR #39 draft until that classification is resolved.
3. Repair or explicitly baseline the 623-manifest control-plane backlog in a
   separate lane.  Do not charge it to the no-go diff.
4. Do not infer a physical gauge-fixing theorem or update the Clay distance.
