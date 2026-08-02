# Operational Governance Charter

**Scope:** repository-wide operational governance for every programme and
worktree.  These rules govern evidence, audits, integration, guards, and local
infrastructure.  They do not assert or amend mathematics.

**Amendment date:** 2026-08-02.

Only rules paid for by observed repository incidents belong here.  A rule's
evidence label is part of the rule: `versioned` means that the repository holds
the cited record; `incident report` means that the owner reported the event but
no exact transcript is versioned here.

## Active owner rules adopted 2026-08-01

The following rules are operative instructions.  They supersede inconsistent
older execution defaults, including the local build token and the detached
Windows build recommendation formerly recorded in `CLAUDE.md`.

### Sanctioned execution and terminal reproduction

**Rule.**  Colab Pro+ on Linux is the sanctioned compilation and reproduction
plane.  Lean and Lake builds, oracles, `YangMillsCore`, numerical ovens,
campaigns, and all other sustained computation run there, regardless of
implementation language or programme.  PART I/Surface being active and
prioritized affects scheduling priority within Colab capacity; it creates no
environment exception.

Windows is the owner's desktop and is limited to editing, git, hashes,
commits/push/PR, and scripts proved by reliable prior measurement to satisfy
all three local-light limits:

1. at most 30 seconds wall time;
2. exactly one process with no worker pool; and
3. at most 512 MiB peak RSS.

Without reliable prior measurements establishing all three limits, a script
is presumed heavy and runs in Colab.  Rational certifiers are local only when
they meet this contract.  Running Lean, Lake, an oracle, a numerical oven, or
any computation outside the local-light contract on Windows is prohibited.
The only exception is explicit owner authorization in the same assignment
that names the command or campaign.  An idle or apparently available Windows
machine does not grant permission.

The spatial `symWeighted` judge, measured at 171 seconds, is not light.  Its
former Windows authorization is superseded and it runs in Colab.
The former local build token and any one-session-total rule are superseded.

Colab Pro+ permits multiple concurrent runtimes.  The operating limit is
compute units consumed per hour of connected runtime, not a presumed maximum
of one session.  Multiple threads may execute concurrently when the budget
permits.  Each concrete runtime/session belongs to exactly one thread; sharing
one runtime between threads is prohibited.

Notebooks and commands must be prepared while disconnected.  Opening a runtime
to prepare work, or keeping a runtime connected without executing, is
prohibited.  Disconnect the runtime when each execution unit finishes.  The
default runtime is CPU/high-RAM.  GPU use requires an explicitly justified
numerical campaign.  Each thread records runtime opening and closing, runtime
type, and total connected time.

If Colab rejects a runtime, record the literal rejection message.  Distinguish
a concurrent-session limit from exhaustion of compute units before deciding
to serialize.  Before authorizing more than two simultaneous sessions, inspect
the visible compute-unit consumption.  Serialize because of budget, never
because of a fictitious technical one-session restriction.

Terminal reproducibility requires two fresh, independent clones in Colab,
checked out at the same SHA, with matching output hashes.  It does not require
two operating systems.  Windows execution is not closure debt.

### Acceptance-safe Python certificates

**Rule.**  No decision to accept input, accept a mutation, increment an
acceptance counter, or emit `PASS` may depend on a Python `assert`.  Acceptance
checks must be explicit and must raise an error or return a non-zero exit code
in both normal execution and `python -O`.  A certifier may emit `PASS` only
after all checks have completed and an explicit acceptance counter has been
checked.

Certificate self-tests must run in normal and `-O` modes and must include real
field mutations, not only author-invented placeholders.  An internal `assert`
is permitted only when it does not participate in deciding certificate
acceptance; no certificate may depend on it for its verdict.

### Sentinels transport exit status; they do not certify success

**Rule.**  The mere existence of a sentinel never means success.  A sentinel
contains exactly one line: the real decimal exit code of the child process,
captured after that process terminates.  Sentinel publication is atomic:

1. write the exit code to a temporary file;
2. close the temporary file;
3. validate that it is non-empty and parses as an integer; and
4. rename it to the final sentinel path.

Every reader must distinguish four states: sentinel absent; sentinel empty or
non-integer; sentinel containing a non-zero integer; and sentinel containing
zero.  Only the last state, together with separate validation of the log,
permits a candidate `PASS`.  Logs and sentinels must use semantic mode names,
such as `normal` and `optimized`, rather than indistinguishable numeric
suffixes.

### Agent calls have a measured 300-second transport ceiling

**Incident that paid the rule (2026-08-02):** two monolithic Fable Gate 7
calls on the same SHA and unchanged contract were terminated by the outer MCP
transport at approximately 300 seconds.  The second call requested a
900-second bridge timeout, but the outer transport still returned the literal
error `timed out awaiting tools/call after 300s`.  Neither expiration returned
a verdict.  The exact measurements and the later terminal verdict are recorded
in the PR #35 Gate 7 audit trail: [timeout
measurement](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/35#issuecomment-5157227097)
and [terminal phased
verdict](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/35#issuecomment-5157390269).

**Rule.**  No single agent or MCP call may be designed on the assumption that
it will run for more than 300 seconds.  If the task may not fit, partition the
execution before launching it and make every intermediate result durable so a
transport death does not erase completed work.

For a preregistered gate, partitioning never changes, removes, or weakens a
criterion.  Every phase receives the original contract and criteria verbatim;
only its execution responsibility is bounded.  Role separation is preserved
by one continuing auditor or by explicit fresh re-blinding, and a separate
synthesis consumes sealed phase reports.  No phase may reveal to a later blind
phase the route it must independently discover.  A timeout is not a verdict
and creates no authority to amend the gate.

## Historical provenance for the 2026-08-01 rules

This subsection records why the active rules above exist; it is incident
history, not an alternate execution procedure.  The rule adopted on
2026-08-01 was purchased by three measured incident classes:

- a Windows cache was destroyed through a junction;
- two certificates emitted false `PASS` under `python -O`, which removes
  `assert` statements; and
- a sentinel was empty and did not transport the child process's exit code.

No new cost, duration, or success metric is inferred here.  The detailed cache
incident record, including its separately labelled measurements and causal
reconstruction, remains the evidence cited in section 1 below.

## 1. Worktree cache isolation

**Incident that paid the rule (2026-07-31):** a Windows junction made a
worktree's `.lake/packages` alias the principal clone's cache.  A recursive
cleanup was reconstructed as having crossed that junction and deleted the
target contents.  The incident measurements, causal status, 7.2 GB / 7,788
`.olean` cost, aggregate two-morning cost, and local `.ltar` recovery are
separated in the
[Mathlib junction cache incident note](INCIDENT-MATHLIB-JUNCTION-CACHE-DELETION-20260731.md).

**Rule.**  Copy `.lake/packages` between worktrees with `robocopy`; never share
it through a junction.  Remove an existing junction only with
`cmd /c rmdir <link>`, without `/s`, after resolving the exact link path.
Never use `Remove-Item -Recurse` on a junction.

## 2. Terminal audits certify commits, not lanes

**Incident that paid the rule (2026-07-31):** the terminal pre-audit reported
its verdict against the exact protected commit
[`a66b1c7da3c7441e06864e327b5c4efa43e9c79d`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/a66b1c7da3c7441e06864e327b5c4efa43e9c79d),
not against a branch name.  The incident report is the evidence for that audit
association; this charter change does not inspect, alter, or recertify the
protected tree.  The repository separately versions non-rebase integration
checkpoints in [REPRODUCIBILITY.md](../REPRODUCIBILITY.md).

**Rule.**  A terminal audit certifies an exact SHA, not a lane.  Integrate the
certified SHA unchanged by merge commit or fast-forward.  Never squash or
rebase it: both create a different commit, so the verdict loses its referent.
This is the second, independent reason recorded for the existing
merge-never-rebase rule; it adds preservation of the audit referent without
inventing or restating the rule's earlier rationale.

## 3. A failed gate is immutable; an inexecutable gate has a narrow amendment path

**Incident that paid the rule (2026-07-31):** a terminal gate was reported
`INEXECUTABLE` for a cause external to the mathematics.  The owner had to
decide whether an alternate route could preserve the judge without turning the
lane into its own evaluator.  This is an
[incident-report-only record](#evidence-boundary-for-the-2026-07-31-audit-incidents),
not a reconstructed transcript.  Versioned precedents for fixing judges before
results and forbidding retrospective adjustment appear in
[C5 Charter, Amendment 8](C5-CHARTER.md) and for rerunning after an external
stdout failure without changing mathematical parameters in the
[weak-main detached-stdout incident](INCIDENT-WEAK-MAIN-V4-DETACHED-STDOUT-20260728.md).

**Rule.**  A gate that has returned `FAIL` is never amended.  A gate that is
`INEXECUTABLE` for a non-mathematical external cause may be amended only if all
of the following hold:

1. the amendment is fixed before anyone sees results;
2. it names the invariant property and requires an equal or stronger property;
3. anyone who supplied the alternate route is excluded from auditing it;
4. the original criterion remains registered and becomes a second witness if
   it later becomes executable; and
5. the owner, never the lane's fabricator, makes the decision.

## 4. An auditor has no inbound channel

**Incident that paid the rule (2026-07-31):** an audit reportedly completed
all measurements but had to withhold its verdict after receiving information
while it ran.  The measurement completion and withheld verdict are
[incident-report-only facts](#evidence-boundary-for-the-2026-07-31-audit-incidents).
The repository already versions the channel failure class in
[Surface Closure Notes v60, incident #27](SURFACE-CLOSURE-NOTES.md): plausible
result lines arrived through task notifications but did not match bytes on
disk.

**Rule.**  Launch the auditor, wait, then read its report.  While it runs, send
it no messages, operational notices, owner readings, summaries, or partial
results.  Silence is part of the audit boundary, not a convenience.

## 5. A guard's name must not claim more than its predicate

**Incident that paid the rule (2026-07-31):** two independent auditors were
reported to have obtained false greens from a phrase-whitelist guard: the
required text was present while semantic honesty was not established.  The
exact July 31 reports are subject to the
[evidence boundary below](#evidence-boundary-for-the-2026-07-31-audit-incidents).
The same failure class is versioned in
[Verification Ledger Addenda 563 and 566](VERIFICATION-LEDGER.md):
`check_module_prose.py` returned zero findings while external readings still
found false or stale claims, and the ledger explicitly records that the guard
reads identifiers rather than claims.

**Rule.**  A guard's name and status must describe exactly what it checks.  A
whitelist of phrases certifies textual presence only.  It must not be named or
reported as a semantic-honesty certificate.

## 6. Guard regression mutations come from external field attacks

**Incident that paid the rule (2026-07-31):** the same two-auditor false-green
incident exposed field attacks that the author's guard had not rejected.  The
adopted causal inference is that author-invented cases alone had not covered
the external attack surface; it is not presented as an audit transcript.  The
July 31 report is limited as stated
[below](#evidence-boundary-for-the-2026-07-31-audit-incidents).  The external
field catches preserved in
[Verification Ledger Addenda 563 and 566](VERIFICATION-LEDGER.md) are versioned
examples of the required regression corpus.

**Rule.**  Regression mutations for a guard must be derived from real field
attacks supplied by external auditors.  The guard's author may add cases, but
author-invented cases alone cannot qualify the guard.  Otherwise “who checks
the checker?” has merely moved up one level.

## Evidence boundary for the 2026-07-31 audit incidents

The owner supplied the July 31 incident facts used in sections 2–6 during
operational coordination.  No exact audit transcript for sections 3–6 is
versioned on `main` at the time of this amendment.  Accordingly:

- this charter records those events as **incident reports**, not certified
  transcripts;
- it links versioned repository precedents where they independently exhibit
  the same failure class;
- it does not infer dialogue, timing, results, or actor identities beyond the
  reported facts; and
- it does not rerun, inspect, or amend the protected terminal-audit lane.
