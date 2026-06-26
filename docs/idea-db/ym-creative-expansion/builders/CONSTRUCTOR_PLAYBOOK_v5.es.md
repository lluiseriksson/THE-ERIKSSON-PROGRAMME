# Playbook del constructor v5

Objetivo: convertir una misión en un patch pequeño que reduzca una hipótesis o
una obligación exacta.  No escribas wrappers nuevos si el patch no elimina un
campo real.

## Ciclo obligatorio

1. Elige una misión con `python scripts/mission_board.py`.
2. Compila el prompt de misión.
3. Rellena un `patch_intake/*.json` antes de editar código.
4. Ataca una sola fuente/hipótesis.
5. Ejecuta `score_patch_intake.py`.
6. Si el score falla, convierte el resultado en un blocker más preciso, no en un
   theorem hueco.

## Regla de aceptación

Un patch debe tener al menos uno:

- `removed_fields >= 1`;
- `source_promotions >= 1` con locator exacto y source lock;
- `toy_theorems >= 1` que reduzcan una misión concreta sin tocar core.

Y debe tener cero:

- consumidores nuevos sin campo removido;
- definiciones tautológicas de `admissible`;
- OCR usado para signos/constantes/exponentes;
- imports nuevos en `YangMillsCore` desde la idea DB.

## Ruta recomendada

Primero `OC_001`, luego `OC_010`, después `OC_004` o `OC_006` según el source
material disponible.  `OC_002` y `OC_003` son más ambiciosas: no las intentes si
`source_subset_gapCarrier` aún no está claro.
