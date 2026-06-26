# Cobertura de fuentes — Batch 001

**Fecha:** 2026-06-26
**Estado:** primera tanda verificable, no cobertura total del programa.

| Fuente | Cobertura estructurada actual | Estado | Siguiente extracción prioritaria |
|---|---|---|---|
| Dimock I | Normalización (66–74), random walk/Green (84–85), cluster local (235–238), sumabilidad (289–295), Theorem 27 (296–301), resolvente (334–335) | `source_extracted` parcial | Vincular consumidores Lean concretos y guardar PDF/renders privados con SHA-256 |
| Dimock II | Theorem 3.1 (201–205), covarianza/raíz (271–276), holes aplicado (501–510), métrica modificada (627–632), Appendix F (633–646) | `source_extracted` parcial | Cerrar entropía de cubiertas de (642), diccionario de `Ω` y actividad física |
| Dimock III | Theorem 1: bounds locales `E/R/B` (14–25); estabilidad final (224–226) | `source_extracted` parcial | Usar solo como arquitectura escalar; localizar análogos Yang–Mills legítimos |
| Balaban CMP116 | Catálogo estructurado amplio del frente Lemma 3 | Parcial | `P`-family, Eq. (2.29), fixed-`Z0'` Eq. (2.37), actividad/termwise |
| Balaban CMP109 | Referencia 26 y convención general de bonds | Parcial | Extraer jerarquía de parámetros y puente CMP116 específico |
| Balaban CMP119 | Bound `R` y notas de localidad | Parcial | E/R/B, Eq. (2.42), diccionario al raw activity |
| Cammarota CMP85 | Bibliografía y acceso identificados | `source_pending` | Obtener PDF primario limpio y teorema Mayer exacto |
| Balaban CMP95 | Bibliografía verificada; fórmulas narrativas (1.89), (1.114) | `source_pending` | Abrir PDF primario y extraer hipótesis/cuántificadores/uniformidad |
| Balaban CMP96 | Bibliografía verificada | `source_pending` | Ley de covarianza de un paso y normalización |
| Balaban CMP98 | Bibliografía verificada; target pp. 19–20, (14)–(15) | `source_pending` | Transcripción visual exacta y diccionario de símbolos |
| Balaban CMP99 | Bibliografía verificada | `source_pending` | Propagador en background field, decay y small-field hypotheses |
| Balaban CMP122-I | Eq. (1.70) localizada narrativamente | `located` | Verificación visual y restricciones completas |
| Balaban CMP122-II | Eqs. (1.98)–(1.100) localizadas narrativamente | `located` | Theorem 1 completo y diccionario de términos `R'` |

## Regla de uso

Solo las entradas `source_extracted`, `lean_linked` o `theorem_checked` pueden alimentar un objetivo Lean sin reabrir antes la página. `visual_confirmed` conserva una fórmula localizada, pero puede seguir necesitando hipótesis o diccionario. `source_pending` y `ocr_corrupted` son bloqueadores explícitos.
