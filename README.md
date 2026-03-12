# programa-eriksson

**Formal dependency architecture and Lean 4 research program**  
**4D SU(N) Yang–Mills existence and mass gap (Eriksson programme)**

Lema interno:  
**No black box counts as proof. No chat memory counts as state.**

## Estado auditado actual (12 marzo 2026)
- Repositorios anteriores: solo scaffolds de auditoría (0 teoremas cerrados en Lean kernel).
- Este repo: máquina de estado investigadora de 10–15 años.
- Objetivo terminal: cerrar la cadena crítica L0 → L8 sin axiomas no registrados.

## Arquitectura
- Capas L0–L8 (ver `docs/02_research_program/00_master_openings_tree.md`)
- Registro máquina-legible: `registry/nodes.yaml`
- Dashboard generado automáticamente
- CI que falla si aparece `sorry`, `axiom` no registrado o estado inconsistente

## Qué cuenta como prueba
- Solo `theorem … := by …` cerrado en el kernel Lean sin `sorry` ni axiomas externos no registrados.
- IMPORTED desde Mathlib cuenta.
- BLACKBOX debe estar registrado en `nodes.yaml`.

## Cómo empezar (IA o humano)
1. Lee `AI_ONBOARDING.md`
2. Mira `dashboard/current_focus.json`
3. Ejecuta `scripts/validate_registry.py`

Ver `ROADMAP_MASTER.md` y `STATE_OF_THE_PROJECT.md` para detalles.
