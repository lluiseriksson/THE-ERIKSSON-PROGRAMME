# JOINT_AGENT_PLANNER.md

This file is the shared planning surface for Codex, Cowork, and any local
sidecar model such as Gemma/Ollama. It records the current consensus on where
the project is, where it is going, and which percentage numbers may be quoted.

It is not a proof. It is a planning and honesty instrument. The machine-readable
source is `registry/progress_metrics.yaml`; the README must summarize the same
numbers, and Cowork must audit any percentage change before it becomes canonical.

## Current consensus

| Metric | Current estimate | Meaning |
|---|---:|---|
| Clay-as-stated | ~5% | Literal Clay Millennium target: continuum quantum Yang-Mills on R4, OS/Wightman/Wightman-compatible theory, SU(N), N >= 2, positive mass gap. |
| Internal lattice small-beta subgoal | ~28% | What this repository is actively formalizing now: small-beta lattice mass gap via representation theory, Klarner/F3 counting, and Mayer/Kotecky-Preiss. |
| Honest lattice discount | ~23-25% | Same as the 28% lattice estimate, but with vacuous/low-content retirements mostly discounted. |
| Named-frontier retirement | 50% | Internal monotone accounting over named entries in `AXIOM_FRONTIER.md` and `SORRY_FRONTIER.md`; useful, but not the Clay-as-stated percentage. |

Global Clay status remains `NOT_ESTABLISHED`.

## Why there are multiple numbers

The Clay statement and the repository's current front are not the same target.
The project has real formal assets in Haar/Schur/character/F3 infrastructure,
but the literal Clay problem additionally requires a continuum quantum field
theory, OS/Wightman reconstruction, and a nontrivial continuum mass-gap theorem
for SU(N), N >= 2. Those are represented by `OUT-*` rows in
`UNCONDITIONALITY_LEDGER.md` and remain blocked.

The README must therefore quote three distinct metrics:

- `Clay-as-stated`: currently ~5%.
- `lattice-small-beta`: currently ~28%, with a 23-25% honesty discount.
- `named-frontier retirement`: currently 50%, historical internal metric.

Agents must not replace one metric with another.

## Critical path

1. `F3-SAFE-DELETION`: prove the global root-avoiding safe-deletion theorem for
   nontrivial anchored preconnected buckets.
2. `F3-ANCHORED-WORD-DECODER`: iterate safe deletion into a full Klarner/BFS
   anchored word decoder and close `F3-COUNT`.
3. `F3-MAYER-URSSELL`: prove the Mayer/Ursell identity and connectingBound
   cluster estimate.
4. `EXPERIMENTAL-AXIOM-CLASSIFICATION`: retire, reformulate, or quarantine the
   remaining Experimental axioms.
5. `OUT-CONTINUUM-BLUEPRINT`: build a formalizable continuum/OS/Wightman
   roadmap before claiming material movement on Clay-as-stated.

## Joint update protocol

1. Codex may implement a proof, script, or registry change.
2. Cowork audits the evidence and either passes it or files a repair task.
3. Gemma/Ollama may be used as a local sidecar for drafting task decompositions,
   sanity checks, and alternate proof-search ideas, but its output is never
   canonical until Codex/Cowork record it in the repo and Cowork audits it.
4. Percentage changes require:
   - an updated `registry/progress_metrics.yaml`;
   - an updated `UNCONDITIONALITY_LEDGER.md` row;
   - an `AGENT_BUS.md` handoff explaining the evidence;
   - a Cowork audit entry in `COWORK_RECOMMENDATIONS.md`;
   - README sync.

## Forbidden conclusions

- Do not claim the Clay problem is solved.
- Do not call the 50% internal metric a literal Clay percentage.
- Do not count SU(1) triviality as evidence for nonabelian SU(N), N >= 2.
- Do not count `EXP-LIEDERIVREG` until the false all-functions formulation is
  replaced.
- Do not let infrastructure progress move mathematical percentages.

## Next planner task

Cowork should audit this planner against `UNCONDITIONALITY_LEDGER.md`,
`KNOWN_ISSUES.md`, and `registry/progress_metrics.yaml`. If the 5% / 28% /
23-25% / 50% split is accepted, Cowork should mark
`COWORK-AUDIT-JOINT-PLANNER-001` as `AUDIT_PASS`; otherwise it must create a
Codex-ready correction task with exact replacement percentages and evidence.
