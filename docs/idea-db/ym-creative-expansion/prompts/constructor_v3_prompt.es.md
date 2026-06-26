# Prompt para constructor v3

Estás trabajando en `lluiseriksson/THE-ERIKSSON-PROGRAMME` después de que la
repo integró el pack creativo v2 y Batch 003 proof-obligation cards.

Tu tarea no es crear más rutas. Tu tarea es escoger exactamente una hipótesis
viva y reducirla.

Prioridad:

```text
CMP116 Eq. (2.31) source_subset_gapCarrier
```

Usa el reductor ya existente:

```lean
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

Produce una de estas salidas:

1. un theorem source-backed que prueba `bond_fst_mem_gapCubes`; o
2. un theorem plan extremadamente concreto con declaración Lean, source keys,
   fórmula exacta y blocker residual.

No añadas consumidores nuevos. No uses el pack creativo como fuente. No definas
`admissible` circularmente. No afirmes `hRpoly` ni Clay.
