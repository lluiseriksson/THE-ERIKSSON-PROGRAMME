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
| Balaban CMP95 | PDF primario y renders privados registrados; Prop. 1.1 (1.89) y Prop. 1.2 (1.110)-(1.114) visualmente confirmadas | `visual_confirmed` | Mapear los bounds de `G/G_k` al certificado de covarianza/raíz de Lean y al transporte CMP96/CMP99 |
| Balaban CMP96 | Bibliografía verificada; label/page map de propagador y covarianza de un paso localizado | `located` | Elegir la ventana exacta CMP96, confirmar visualmente el cuerpo de fórmula y mapear normalización/escala |
| Balaban CMP98 | Bibliografía verificada; label/page map Q_k localizado para la ruta de `gaussian_pushforward` | `located` | Elegir la ventana exacta CMP98, confirmar visualmente el cuerpo de fórmula y diccionario de símbolos |
| Balaban CMP99 | PDF primario y renders privados registrados; `G(U)`, Theorems 3.3/3.11/3.12 y Theorem 3.15 visualmente confirmados | `visual_confirmed` | Diccionario `Delta_a/G(U)` hacia covarianza/raíz/Hessiano físico de Lean |
| Balaban CMP102 | PDF primario y renders privados registrados; Eq. (22), Eqs. (44)-(46) y Eq. (142) visualmente confirmadas | `visual_confirmed` | Diccionario `A'`, `Delta_1`, `H`, `U_k` hacia `wilson_hessian_identification` |
| Balaban CMP122-I | Eq. (1.70) localizada narrativamente | `located` | Verificación visual y restricciones completas |
| Balaban CMP122-II | Eqs. (1.98)–(1.100) localizadas narrativamente | `located` | Theorem 1 completo y diccionario de términos `R'` |

## Regla de uso

Solo las entradas `source_extracted`, `lean_linked` o `theorem_checked` pueden alimentar un objetivo Lean sin reabrir antes la página. `visual_confirmed` conserva una fórmula localizada, pero puede seguir necesitando hipótesis o diccionario. `source_pending` y `ocr_corrupted` son bloqueadores explícitos.
