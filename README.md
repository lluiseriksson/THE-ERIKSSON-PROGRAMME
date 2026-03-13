# The Eriksson Programme

**Formal dependency architecture and Lean 4 research program**
**4D SU(N) Yang–Mills existence and mass gap**

> **Internal lemma**: No black box counts as proof. No chat memory counts as state.

---

## Current audited state (March 2026)

| Layer | Status | Notes |
|-------|--------|-------|
| L0 (Lattice foundations) | ✅ FORMALIZED_KERNEL | 6 files, zero sorry |
| L1 (Gibbs measure) | ✅ FORMALIZED_KERNEL | gibbsMeasure, expectation, correlations |
| L2 (Bałaban decomposition) | ✅ FORMALIZED_KERNEL | small/large field split, measurability |
| L3–L8 | OPEN / BLACKBOX | Hard analysis pending |

**Progress estimate: ~12% toward unconditional Yang–Mills.**

---

## What counts as proof

- Only `theorem … := by …` closed in the Lean kernel **without `sorry`** and without unregistered axioms.
- Imports from Mathlib count.
- BLACKBOX nodes must be registered in `registry/nodes.yaml`.

---

## Architecture

The program is organized in layers L0–L8, each corresponding to a major mathematical component:

- **L0** — Finite lattice geometry, gauge configurations, Wilson action, SU(2) basics
- **L1** — Gibbs measure, partition function, expectation values, correlations
- **L2** — Bałaban small/large-field decomposition, RG flow, measurability
- **L3** — Block-spin renormalization group iteration
- **L4** — Large-field suppression bounds
- **L5** — Continuum limit infrastructure
- **L6** — Osterwalder–Schrader reconstruction
- **L7** — Spectral gap / mass gap
- **L8** — Final Yang–Mills existence and mass gap theorem

Full dependency graph: `docs/02_research_program/00_master_openings_tree.md`

---

## Repository structure
```
YangMills/
  L0_Lattice/          # Finite lattice, gauge configs, Wilson action, SU(2)
  L1_GibbsMeasure/     # Gibbs measure, expectation, correlations
  L2_Balaban/          # Small/large decomposition, RG flow, measurability
  L4_LargeField/       # Large-field suppression (stub)
registry/
  nodes.yaml           # Machine-readable node status
  critical_paths.yaml
scripts/
  validate_registry.py
dashboard/
  current_focus.json
```

---

## Getting started (AI or human)

1. Read `AI_ONBOARDING.md`
2. Check `dashboard/current_focus.json` for current focus
3. Run `scripts/validate_registry.py` to verify registry consistency
4. See `ROADMAP_MASTER.md` and `STATE_OF_THE_PROJECT.md` for full details

---

## Governance

- **CI fails** if any `sorry`, unregistered `axiom`, or inconsistent registry state is detected
- **No chat memory counts as state** — all state lives in `registry/nodes.yaml` and source files
- **No black box counts as proof** — every node must be either FORMALIZED_KERNEL or explicitly registered as BLACKBOX with justification

---

## Toolchain

- Lean 4 (`leanprover/lean4:v4.29.0-rc6`)
- Mathlib v4.29
- Lake build system

---

## License

Research program by Lluis Eriksson. All Lean proofs are verifiable in the Lean 4 kernel.
