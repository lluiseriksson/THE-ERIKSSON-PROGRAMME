# Constructor playbook v2

## Objetivo

Usar este paquete como motor de creatividad controlada para reducir hipótesis reales en `THE-ERIKSSON-PROGRAMME`.

## Orden recomendado

1. Lee `rankings/BUILDER_PRIORITY.md`.
2. Ejecuta `python scripts/query_expansion_db.py --list-cards`.
3. Escoge solo una carta.
4. Pasa la carta por `agent_modes/falsifier.md`.
5. Si sobrevive, crea un Lean stub en una carpeta experimental.
6. Solo si compila, prepara un commit pequeño.

## Prohibiciones

- No añadir nuevos consumidores para Eq. (2.31) sin descargar un campo fuente.
- No declarar `admissible := fun _ _ _ => true` salvo prueba textual de que la fuente usa todos los subconjuntos.
- No usar Catalan closure para Appendix F hasta comprobar la misma clase de árboles.
- No promover `source_db_patch.experimental.json` ni `source_patch_templates/*` sin revisión fuente.

## Señal de éxito real

Un commit cuenta como avance si elimina o debilita una hipótesis viva, o si prueba un toy theorem reusable que bloqueaba una ruta concreta.
