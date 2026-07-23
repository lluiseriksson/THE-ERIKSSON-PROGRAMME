# Incident: sine-normalized finite-beta unit timed out (2026-07-23)

## Scope

The preregistered candidate unit
`beta=[3258/32,3259/32]`, with common `J1^4` scaling and exact
`sin(t)` normalization, was run at beta order 40, t order 45, and 220-bit
arb precision. The adaptive cover used `CWIN=3/2` and `min_dt=1/200000`.

## Observation

The full unit runner exceeded the 300-second wall-clock limit and emitted no
transcript. Consequently there is no production/replay pair and no row-wise
certificate for this unit.

## Disposition

This is a design incident, not evidence of a sign failure. The successful
single-box stress run was recorded separately as a candidate transcript and
validated byte-for-byte against its replay. It covers only
`t=[7817/2500,156343/50000]` at the fixed beta box and does **not** promote
G2 or G6. The unit remains uncovered until an auditable certificate or an
analytic boundary-layer lemma is produced.
