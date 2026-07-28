# Pair mean-value archive — stale dependency hashes

**Date:** 2026-07-24  
**Scope:** candidate archive only; no G2/G6 promotion

Running the independent cover validator on
`run-manifests/surface-scaled-pair-mean-value-cover-beta101p8125-101p90625-lambda150-190-20260720.json`
fails its dependency-hash assertion before any coverage claim is accepted.
The manifest therefore cannot be used as current provenance evidence without
regeneration of the affected production/replay transcripts under one frozen
source head and a fresh manifest.

This is a provenance failure, not a sign counterexample. The archived pair
rows remain useful for routing, but they are quarantined together with the
stale manifest; no finite-beta union, `H_tail`, K2, G2, or G6 state changes.
