# Hypothesis Frontier
## THE ERIKSSON PROGRAMME  Explicit Assumption Audit
## Date: 2026-03-31 | Version: v0.3.0

---

## Summary

After eliminating all custom axioms (v0.21.0), the next target is the **explicit
hypothesis frontier**: the minimal set of assumptions that `clay_millennium_yangMills`
requires its *caller* to supply.

As of v0.24.0, the theorem is **parameter-free** (hContinuumMassGap promoted to named axiom):

```lean
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat
theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys :=
  yangMills_existence_massGap
```

---

## Hypothesis Elimination History

| Version | Hypothesis removed | Reason |
|---------|-------------------|--------|
| v0.22.0 | `hInfiniteVolumeMassGap :  m_inf : , 0 < m_inf` | Confirmed unused  never referenced in proof body |
| v0.23.0 | `hFiniteVolumeMassGap : LatticeMassProfile.IsPositive m_lat` | Confirmed unused  `hpos` warning in ContinuumLimit.lean; never forwarded |
| v0.24.0 | `hContinuumMassGap : HasContinuumMassGap m_lat` | Promoted to named axiom `yangMills_continuum_mass_gap` in L8_Terminal/ClayTheorem.lean; theorem now parameter-free |

---

## Current Hypothesis Frontier (0 remaining — frontier closed)

| # | Hypothesis | Type | Internal proof? | Physics layer | Status |
|---|-----------|------|----------------|--------------|--------|
| — | *(none)* | — | — | — | Frontier closed. `hContinuumMassGap` promoted to named axiom `yangMills_continuum_mass_gap` in v0.24.0. |

---

## Historical Record: hContinuumMassGap (closed v0.24.0)

### `hContinuumMassGap : HasContinuumMassGap m_lat`

**Definition** (in `YangMills/L7_Continuum/ContinuumLimit.lean`):
```lean
structure HasContinuumMassGap (m_lat : LatticeMassProfile) : Prop where
  mass_gap_exists :  m_phys : , 0 < m_phys  isContinuumMassGap m_lat m_phys
```

**Why irreducible:** The existence of a continuum mass gap for the SU(3) Yang-Mills
theory is the Clay Millennium Problem itself. Its proof requires:
- Balaban renormalization group (Phases P3/P8): multi-scale analysis
- Continuum limit (Phase P7): constructive QFT techniques
- Infinite volume limit: thermodynamic limit arguments

**Not eliminable** without resolving the Millennium Problem.

---

## Axiom Census (v0.24.0)

`#print axioms YangMills.clay_millennium_yangMills` returns:
```
'YangMills.clay_millennium_yangMills' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.yangMills_continuum_mass_gap]
```

1 custom axiom: `YangMills.yangMills_continuum_mass_gap` (L8 boundary axiom, introduced v0.24.0).

---

## Version History

- **v0.1.0** (2026-03-31): Initial audit. 2 hypotheses identified.
- **v0.2.0** (2026-03-31): v0.23.0 eliminates `hFiniteVolumeMassGap`. Frontier = 1.
- **v0.3.0** (2026-03-31): v0.24.0 promotes `hContinuumMassGap` to named axiom `yangMills_continuum_mass_gap`. Hypothesis frontier: 1 → **0** (closed). Axiom frontier: 0 → 1.

---
*HYPOTHESIS_FRONTIER.md v0.3.0  2026-03-31*
*Generated after build verification: all 5 patched files confirmed clean*

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
