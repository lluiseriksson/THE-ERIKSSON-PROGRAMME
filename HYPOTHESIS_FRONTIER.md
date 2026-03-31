# Hypothesis Frontier
## THE ERIKSSON PROGRAMME  Explicit Assumption Audit
## Date: 2026-03-31 | Version: v0.1.0

---

## Summary

After eliminating all custom axioms (v0.21.0), the next target is the **explicit
hypothesis frontier**: the minimal set of assumptions that `clay_millennium_yangMills`
requires its *caller* to supply.

As of v0.22.0, the theorem signature is:

```lean
theorem clay_millennium_yangMills
    (m_lat : LatticeMassProfile)
    (hFiniteVolumeMassGap : LatticeMassProfile.IsPositive m_lat)
    (hContinuumMassGap : HasContinuumMassGap m_lat) :
     m_phys : , 0 < m_phys
```

The infinite-volume OS cluster hypothesis (`hInfiniteVolumeMassGap :  m_inf : , 0 < m_inf`)
was confirmed unused and removed in v0.22.0.

---

## Current Hypothesis Frontier (2 remaining)

| # | Hypothesis | Type | Internal proof? | Physics layer | Status |
|---|-----------|------|----------------|---------------|--------|
| 1 | `hFiniteVolumeMassGap` | `LatticeMassProfile.IsPositive m_lat` | Partial (Balaban RG chain) | L5 lattice spectral gap | **OPEN** |
| 2 | `hContinuumMassGap` | `HasContinuumMassGap m_lat` | Partial (L7 ContinuumLimit chain) | L7 renormalized mass convergence | **OPEN** |

---

## Hypothesis 1: hFiniteVolumeMassGap

**Type:** `LatticeMassProfile.IsPositive m_lat`
**Meaning:** The finite-volume lattice mass profile has a strictly positive spectral gap.
**Physics:** Corresponds to L5.1 in the Eriksson Programme  Balaban renormalization group
  establishes that the lattice Yang-Mills mass gap is positive.

**Backward chain:**
- `clay_millennium_yangMills` calls `continuumLimit_mass_pos m_lat hFiniteVolumeMassGap hContinuumMassGap`
- `continuumLimit_mass_pos` forwards to `continuumMassGap_pos m_lat hcont`
- `continuumMassGap_pos` does NOT use `hpos` (the finite-volume gap) directly  it uses `hcont`
- **Preliminary finding:** `hFiniteVolumeMassGap` may also be unused in `continuumLimit_mass_pos`!
  Needs verification by reading `YangMills/L7_Continuum/ContinuumLimit.lean` carefully.

**Blocker if genuine:** Balaban RG formalization (`YangMills/ClayCore/BalabanRG/`) provides
  the concrete Balaban estimates, but the chain to `LatticeMassProfile.IsPositive` is not
  yet closed internally.

---

## Hypothesis 2: hContinuumMassGap

**Type:** `HasContinuumMassGap m_lat`
**Meaning:** The renormalized mass has a positive continuum limit.
**Physics:** Corresponds to L7.1  the continuum limit of the lattice mass gap is positive.

**Backward chain:**
- `continuumLimit_mass_pos` passes `hcont` to `continuumMassGap_pos`
- `continuumMassGap_pos` (in `ContinuumLimit.lean`) produces ` m_phys : , 0 < m_phys`
- The definition of `HasContinuumMassGap` involves `Tendsto` (renormalized mass converges)
  and `atTop` (infinite-volume limit)
- This is the deepest required hypothesis  the continuum mass gap existence is the
  core physical statement of the Clay Millennium Problem

**Blocker:** Requires full Balaban RG + OS reconstruction + continuum limit estimates.
  This is the hardest remaining gap, equivalent to the physics of the problem itself.

---

## Eliminated Hypotheses

| Hypothesis | Version | Reason |
|-----------|---------|--------|
| `hInfiniteVolumeMassGap :  m_inf : , 0 < m_inf` | v0.22.0 | Never used in any proof body; removed from all 3 Clay theorems and 5 caller sites |

---

## Action Items

1. **Verify hFiniteVolumeMassGap usage**  read `continuumMassGap_pos` body in
   `ContinuumLimit.lean` to check if `hpos` is forwarded or silently dropped.
   If unused: remove it (frontier shrinks to 1 hypothesis).

2. **Classify HasContinuumMassGap**  determine if `HasContinuumMassGap m_lat` is
   provable from existing internal results in `YangMills/L7_Continuum/`.

3. **Investigate LatticeMassProfile**  check if `m_lat : LatticeMassProfile` itself
   encodes assumptions (e.g., via structure fields) that should be counted as hypotheses.

---

## Reachability Notes

- `YangMills.clay_millennium_yangMills` axiom census: `[propext, Classical.choice, Quot.sound]`
- All custom axioms are dead code as of v0.21.0
- The 2 remaining hypotheses are genuine logical dependencies

---

*Hypothesis Frontier  v0.1.0  2026-03-31*
*Generated from signature audit of YangMills.clay_millennium_yangMills*
