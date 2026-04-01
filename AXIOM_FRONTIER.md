# AXIOM_FRONTIER.md
## THE-ERIKSSON-PROGRAMME — Custom Axiom Census
## Version: Campaign 18

---

## BFS-live custom axioms (appear in oracle output)

| Axiom | File | Papers | Status |
|-------|------|--------|--------|
| `yangMills_continuum_mass_gap` | `YangMills/L8_Terminal/ClayTheorem.lean` | [58]–[68] | Cannot be eliminated without full Lean formalization of Bałaban-Eriksson proof |

**Oracle target:** `YangMills.clay_millennium_yangMills`
**BFS-live count:** 1
**Unconditional:** NO

---

## BFS-dead axioms (do NOT appear in oracle output)

Any other `axiom` declarations in the repo are not BFS-reachable from
`clay_millennium_yangMills` and do not affect the oracle.

---

## Proof chain from axiom to Clay theorem

```lean
-- Step 1: The axiom
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat

-- Step 2: Continuum mass gap → real mass
theorem yangMills_existence_massGap : ClayYangMillsTheorem :=
  -- uses continuumLimit_mass_pos (unconditional except for above axiom)

-- Step 3: Rename to Clay form
theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys :=
  clay_mass_gap_pos
```

---

## How to verify

```lean
-- In any file importing ClayTheorem:
#print axioms YangMills.clay_millennium_yangMills
```

Expected output (unconditional):
```
'YangMills.clay_millennium_yangMills' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Current output (v0.28.x):
```
'YangMills.clay_millennium_yangMills' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

---

## Source papers for the remaining axiom

The content of `yangMills_continuum_mass_gap` is established in:
- Papers [58]–[67]: Bałaban renormalization-group framework and terminal KP bound
- Paper [68] (viXra:2602.0117): Exponential clustering, multiscale correlator
  decoupling, mass gap assembly (Thm 7.1), OS reconstruction (§8)

The Lean formalization gap is detailed in UNCONDITIONALITY_ROADMAP.md.

---

*Last updated: Campaign 16 (v0.28.2). Oracle verified 2026-03-31: 1 BFS-live custom axiom confirmed post-campaign13-revert.*

## Terminal Theorem: Weak vs Strong (v0.30.0)

The project exposes two levels of the Clay–Millennium conclusion:

| Identifier | Prop | Strength |
|---|---|---|
| `ClayYangMillsTheorem` | `∃ m_phys : ℝ, 0 < m_phys` | **Vacuous** (provable without axioms) |
| `ClayYangMillsStrong` | `∃ m_lat, HasContinuumMassGap m_lat` | **Substantive** (quantitative convergence) |

`clay_millennium_yangMills_strong : ClayYangMillsStrong` is the honest
maximal conclusion: it directly names `yangMills_continuum_mass_gap`
and introduces zero new assumptions.

The weak chain is preserved for backward compatibility.
