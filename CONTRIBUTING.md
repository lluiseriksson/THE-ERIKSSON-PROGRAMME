# CONTRIBUTING

> ⚠ **POSSIBLY STALE — describes the registry-based workflow that
> is no longer maintained.**
>
> This file (2026-03-12) prescribes a contribution flow built
> around `registry/nodes.yaml`, `dashboard/current_focus.json`,
> and the L0–L8 node organisation. As of 2026-04-25, those
> files have **not been updated for 3+ weeks** and are no
> longer consulted by the project's operational governance
> (per `COWORK_FINDINGS.md` Findings 007 and 008).
>
> **For the current contribution process**, see:
>
> - `CONTRIBUTING_FOR_AGENTS.md` — operational loop for
>   autonomous agents (Codex daemon, Cowork sessions)
> - `CODEX_CONSTRAINT_CONTRACT.md` — rules + active priority queue
> - `STRATEGIC_DECISIONS_LOG.md` — append-only decision log
>   (replaces `DECISIONS.md` ADR-002 in practice)
> - `AXIOM_FRONTIER.md` — live axiom census (replaces
>   `registry/nodes.yaml` for verification)
> - `COWORK_FINDINGS.md` — for filing obstructions
>
> The historical content below is preserved but does not reflect
> current practice. See Finding 008 in `COWORK_FINDINGS.md` for
> the supersession discussion.

---

## Contribution rule zero

Do not add important state only in chat, commit messages, or memory.
Update the registry.

## Before opening a PR

You must:
1. identify the target node ID,
2. check its dependencies,
3. update `registry/nodes.yaml` if status/evidence changes,
4. update `DECISIONS.md` if an architectural choice was made,
5. ensure no undocumented `axiom` or `sorry` was introduced.

## Allowed evidence upgrades

Examples:
- `PAPER_ONLY` → `FORMALIZED_WEAK`
- `PAPER_ONLY` → `IMPORTED_THEOREM`
- `FORMALIZED_WEAK` → `FORMALIZED_KERNEL`

## Forbidden moves

- marking a critical node closed with external tests only
- adding a placeholder package and calling the node formalized
- hiding new assumptions in undocumented axioms
- weakening the target statement without updating definition of done

## Review checklist

- Is the statement exact enough?
- Is the evidence label honest?
- Are dependencies registered?
- Is anti-vacuity addressed?
- Does the dashboard still reflect reality?
