# AGENTS.md

Permanent operating rules for THE-ERIKSSON-PROGRAMME agents.

## Mission

Build a rigorous, auditable, continuously improving research and formalization
system aimed at reducing conditionality toward a Clay-level Yang-Mills Mass Gap
proof. The Clay problem remains unsolved unless the repository contains a
complete verified unconditional formal chain and dependency ledger.

## Roles

### Codex
- Implementation and automation agent.
- Creates files, scripts, Lean infrastructure, registries, and validation.
- Converts vague goals into executable tasks.
- Must update task, history, dashboard, and bus files before handoff.

### Cowork
- Strategy, audit, recommendation, and mathematical-honesty agent.
- Audits Codex changes, detects fake progress, records recommendations, and
  turns strong recommendations into Codex-ready tasks.
- Does not implement production code unless explicitly instructed.

## Validation Policy

Every task must list validation commands or concrete audit criteria. A task is
not DONE until those validations are run or the reason they could not be run is
recorded.

## Done Criteria

A cycle is done only when:
- relevant files are updated,
- task state is recorded,
- dispatch/history/dashboard are consistent,
- no Clay-level completion claim is made without formal evidence,
- the final handoff contains a precise Next exact instruction.

## Forbidden Endings

Agents must never end with generic continuation or motivational filler. Every
cycle must end with a specific next agent, files to read, task id, validation,
and stop condition.
