# Clay Core — BalabanRG Status (v0.8.58, 2026-03-19)

**17 files · 0 errors · 0 sorrys · 1 axiom remaining**

## Mechanized chain (0 sorrys end-to-end)

```
physical_rg_rates_from_E26  (axiom — 4 quantitative targets)
  → physicalRGRates_to_balabanRGPackage   THEOREM ✅
  → uniform_lsi_of_balaban_rg_package     THEOREM ✅
  → ClayCoreLSI
  → LSItoSpectralGap                       P8 ✅
  → ClayYangMillsTheorem                   ErikssonBridge ✅
```

## File inventory

| Layer | File | Key content | Status |
|---|---|---|---|
| 0A | BlockSpin.lean | lattice geometry | ✅ |
| 0B | FiniteBlocks.lean | block-spin averaging | ✅ |
| 1  | PolymerCombinatorics.lean | Polymer, KP criterion | ✅ |
| 2  | PolymerPartitionFunction.lean | Z, Ztail, \|Z-1\|≤B | ✅ |
| 3A | KPFiniteTailBound.lean | KPOnGamma, theoreticalBudget | ✅ |
| 3B | KPBudgetBridge.lean | KP → exp(B)-1 majorant | ✅ |
| 4A | KPConsequences.lean | \|Z-1\|, 0<Z, log Z | ✅ |
| 4B | PolymerLogBound.lean | log Z ≤ exp(B)-1 | ✅ |
| 4C | PolymerLogLowerBound.lean | \|log Z\| ≤ 2(exp(B)-1) | ✅ |
| 5  | KPToLSIBridge.lean | clayCore_free_energy_ready | ✅ |
| 6A | BalabanRGPackage.lean | 3-field RG structure | ✅ |
| 6B | UniformLSITransfer.lean | LSI from package | ✅ |
| 6C | BalabanRGAxiomReduction.lean | reduced axiom chain | ✅ |
| 7A | FreeEnergyControlReduction.lean | freeEnergyControl = THEOREM | ✅ |
| 7B | EntropyCouplingReduction.lean | entropyCoupling satisfiable | ✅ |
| 7C | ContractiveMapReduction.lean | trivialBalabanRGPackage (0 axioms) | ✅ |
| 8A | PhysicalRGRates.lean | quantitative rates structure | ✅ |

## Remaining axiom: physical_rg_rates_from_E26

4 quantitative discharge targets:

| Field | Claim | Source |
|---|---|---|
| rho_exp_contractive | rho(β) ≤ C·exp(-c·β) | P81, P82 |
| rho_in_unit_interval | rho(β) ∈ (0,1) for β ≥ β₀ | P81 |
| cP_linear_lb | cP(β) ≥ c·β for β ≥ β₀ | P69, P70 |
| cLSI_linear_lb | cLSI(β) ≥ c·β for β ≥ β₀ | P67, P74 |

## Key theorems proved this session

- `kpOnGamma_implies_compatibleFamilyMajorant` — KP induction (Layer 3B)
- `kpOnGamma_implies_abs_Z_sub_one_le` — \|Z-1\| bound (Layer 4A)
- `log_polymerPartitionFunction_abs_le` — \|log Z\| ≤ 2t (Layer 4C)
- `clayCore_free_energy_ready` — 0<Z ∧ log Z bounded (Layer 5)
- `freeEnergyControl_discharged` — Clay Core discharges freeEnergyControl (Layer 7A)
- `trivialBalabanRGPackage` — BalabanRGPackage with 0 axioms (Layer 7C)
- `physicalRGRates_to_balabanRGPackage` — rates → package (Layer 8A)
- `physicalRGRates_to_lsi` — rates → ClayCoreLSI (Layer 8A)

## Key tactic lessons (session summary)

| Problem | Solution |
|---|---|
| `positivity` fails on `a * X.size` | Add `(ha : 0 ≤ a)` explicitly |
| `rw [set_var]` after `set` | Use `change` instead |
| `Finset.not_mem_erase` not a constant | `have hne := Finset.not_mem_erase ∅ ...` |
| `add_one_le_exp` orientation | `simpa [add_comm] using Real.add_one_le_exp w` |
| `linarith` vs `add_le_add_left` | `linarith [hrec, hmul]` more robust |
| `field_simp` leaves `1 ≤ 1` | `rw [one_div, inv_mul_cancel₀ hβne]` closes |
| `/-- ... --/` before `end` | Use `-- ...` (normal comment) |
| `λ_P` reserved token | Use `lambdaP` (ASCII) |
| `∃ x > 0,` in structure field | Use `∃ x : ℝ, 0 < x ∧` |
| `rw [t]` after `set t :=` | Use `change` |
| `exact ⟨beta0P, hbP, cP0, hcP0, ...⟩` type mismatch | Use `beta0P` as constant witness |
