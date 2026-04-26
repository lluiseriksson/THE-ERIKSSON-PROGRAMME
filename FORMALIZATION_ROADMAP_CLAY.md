# FORMALIZATION_ROADMAP_CLAY.md

## Purpose

This roadmap decomposes the five-year Clay-level Yang-Mills objective into daily
actionable formalization, audit, and research tasks.

## Strategic target

Reach a fully unconditional formal proof chain for the Clay Yang-Mills Mass Gap
problem.

## Joint planner metrics

The live consensus percentages are maintained in `JOINT_AGENT_PLANNER.md` and
`registry/progress_metrics.yaml`, and can be rendered or validated with:

```powershell
python scripts\joint_planner_report.py
python scripts\joint_planner_report.py validate
```

Current planning snapshot:

| Metric | Current estimate | Meaning |
|---|---:|---|
| Clay-as-stated | ~5% | Continuum quantum Yang-Mills on R4 with OS/Wightman-compatible mass gap for SU(N), N >= 2. |
| Internal lattice small-beta subgoal | ~28% | The active formalization scope: representation theory + F3/Klarner counting + Mayer/Kotecky-Preiss at small beta. |
| Honest lattice discount | ~23-25% | Same lattice subgoal after discounting vacuous/low-content retirements. |
| Named-frontier retirement | 50% | Internal monotone accounting over `AXIOM_FRONTIER.md` and `SORRY_FRONTIER.md`; not the literal Clay percentage. |

Percentage changes require Cowork audit, `UNCONDITIONALITY_LEDGER.md` sync, and
README sync. Infrastructure progress alone does not move mathematical
percentages.

## Non-negotiable rule

This roadmap is not a proof. It is a dependency map. No item is complete until
the corresponding formal, audit, and ledger evidence exists.

## Milestones

### M0 - Agentic research infrastructure
- Codex/Cowork coordination
- task queue
- recommendation registry
- history log
- audit loop
- no generic continuation

### M1 - Formal honesty and dependency control
- unconditionality ledger
- allowed foundations
- forbidden assumptions
- proof-status taxonomy
- blocker registry

### M2 - Classical Yang-Mills geometry
- compact simple gauge groups
- bundles
- connections
- curvature
- Yang-Mills action
- gauge transformations
- classical equations

### M3 - Euclidean constructive layer
- regularization
- lattice/continuum bridge
- measures
- reflection positivity
- Schwinger functions
- correlation decay

### M4 - OS/Wightman reconstruction
- OS axioms
- Hilbert space reconstruction
- locality
- covariance
- spectral condition
- nontriviality

### M5 - Mass gap
- formal definition of mass gap
- spectral lower bound
- relation to correlation decay
- positivity of Delta

### M6 - Unconditionality closure
- remove conditional bridges
- prove or eliminate assumptions
- audit all dependencies
- align final theorem with Clay statement

## Daily work rule

Every day's work must reduce at least one of:
- ambiguity
- missing formal definition
- missing theorem
- conditional bridge
- untracked assumption
- unvalidated script
- agent coordination weakness
