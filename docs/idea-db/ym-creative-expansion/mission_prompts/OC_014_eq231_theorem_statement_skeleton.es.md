# Prompt de misión — OC_014_eq231_theorem_statement_skeleton

Misión: Generate exact theorem statements for the three Eq. (2.31) package fields before attempting proofs.

Proof card: `proof.eq231.membership-iff.source-package`

Source keys permitidas:
- `cmp116.eq231.p-family-carrier-source-target`
- `cmp109.bond-convention.positive-oriented`

Target shape:

```text
field theorem skeletons for mem_iff_source, source_subset_gapCarrier, admissible_iff_source
```

Éxito mínimo:

```text
One theorem_skeletons/eq231_*.lean.md file with inputs, conclusion and prohibited shortcuts.
```

Rechaza si:
- admissible is defined as membership
- all three fields are merged into one opaque Prop

Entrega un patch intake JSON. No añadas consumidores downstream si no hay delta
positivo real.
