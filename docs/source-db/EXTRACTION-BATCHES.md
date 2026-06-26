# Lotes de extracción

| Lote | Fuentes | Resultado |
|---|---|---|
| 001 | Dimock RG I–III | Normalización, covarianza/root, cluster expansion ordinaria y con holes, E/R/B y estabilidad |
| 002 | LLM operational context | Crosswalk Lean↔fuente, fórmulas planas, blockers, cobertura, símbolos y grafo de dependencias |
| 003 | Proof-obligation routing | Cards operativas, cola de eliminación de hipótesis, source-key router y checklists anti-falso-avance |

Detalle: [`reports/BATCH-001-DIMOCK-RG.md`](reports/BATCH-001-DIMOCK-RG.md).

Detalle Batch 002:
[`reports/BATCH-002-LLM-CONTEXT-INDICES.md`](reports/BATCH-002-LLM-CONTEXT-INDICES.md).

Batch 002 no promueve ninguna fuente primaria. Sus entradas `crosswalk.*`
son navegación operacional para agentes y deben usarse para encontrar las
fuentes primarias y declaraciones Lean relevantes, no como evidencia matemática.

Detalle Batch 003:
[`reports/BATCH-003-PROOF-OBLIGATION-INDEX.md`](reports/BATCH-003-PROOF-OBLIGATION-INDEX.md).

Batch 003 tampoco promueve fuentes primarias. Sus entradas `proof.*` son cards
operativas para decidir qué source keys abrir, qué hipótesis viva se elimina y
qué errores evitar antes de intentar una declaración Lean.
