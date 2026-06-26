# Constructor playbook v3 — después de integrar el pack en la repo

La repo ya contiene el pack creativo como idea DB. Tu misión ahora no es crear
más rutas, sino convertir una ruta en una descarga real de hipótesis.

## Regla absoluta

```text
No aceptes un commit que sólo añade consumidores.
```

Un commit válido debe hacer una de estas dos cosas:

1. Probar o source-shapear un campo vivo de un source package.
2. Promover una entrada `source_pending` a una interfaz theorem-feedable con
   hipótesis, cuantificadores, constantes y diccionario explícitos.

## Mejor primer commit

Ataca Eq. (2.31), pero no el full iff de golpe. Usa la reducción ya presente:

```lean
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

Objetivo source-shaped:

```text
sourceAdmissible Z D P -> forall b in P, b.1 in gapCubes Z D
```

Esto alimenta el campo:

```lean
CMP116Eq231BalabanPFamilySourcePackage.source_subset_gapCarrier
```

sin tener que resolver todavía:

```text
mem_iff_source
admissible_iff_source
```

## Orden recomendado

1. `source_subset_gapCarrier` vía `bond_fst_mem_gapCubes`.
2. `mem_iff_source` sólo si la familia P está transcrita exactamente.
3. `admissible_iff_source` sólo si `admissible` no es circular.
4. Pointwise P residual majorization.
5. Eq. (2.29) Cammarota threshold interface.
6. Eq. (2.37) fixed-Z0prime + final sum.

## Rechazo automático

Rechaza cualquier patch que:

- defina `admissible := decide (P ∈ PIndex Z D)`;
- use `|P| >= ...` como cota superior del carrier;
- cite `crosswalk.*` o `proof.*` como fuente primaria;
- añada `theorem ..._of_...` que conserva exactamente la misma hipótesis viva;
- toque `YangMillsCore` para importar idea DB o metadata operacional.
