# CONTRIBUTING

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
