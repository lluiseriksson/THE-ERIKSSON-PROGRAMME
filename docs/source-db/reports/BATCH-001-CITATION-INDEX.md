# Batch 001 — índice rápido de citas

Este índice apunta a las fichas JSON canónicas. Las fórmulas completas, hipótesis,
`use_for`, `do_not_use_for`, preguntas abiertas y objetivos Lean están en
`docs/source-db/catalogs/dimock-rg-i-iii-extracted.json`.

| Clave | Fuente | Páginas impresas | Ecuaciones | Estado |
|---|---|---:|---|---|
| `dimocki.cluster-expansion.theorem27.296-299` | `dimock_i` | 39 | 296, 297, 298, 299 | `source_extracted` |
| `dimocki.covariance-resolvent.334-335` | `dimock_i` | 44 | 334, 335 | `source_extracted` |
| `dimocki.gaussian-normalization.66-74` | `dimock_i` | 9-10 | 66, 67, 68, 69, 70, 72, 73, 74 | `source_extracted` |
| `dimocki.lemma25.polymer-summability.289-290` | `dimock_i` | 37 | 289, 290 | `source_extracted` |
| `dimocki.lemma6.random-walk-green.84-85` | `dimock_i` | 11 | 84, 85 | `source_extracted` |
| `dimocki.polymer-summability.corollary26.292-295` | `dimock_i` | 38-39 | 292, 293, 294, 295 | `source_extracted` |
| `dimocki.references.balaban-primary-spine` | `dimock_i` | 50-51 | — | `source_extracted` |
| `dimocki.small-field-cluster.235-237` | `dimock_i` | 30 | 235, 236, 237 | `source_extracted` |
| `dimockii.appendix-f.metric-first-activity.637-644` | `dimock_ii` | 91-92 | 637, 638, 639, 640, 641, 642, 643, 644 | `source_extracted` |
| `dimockii.appendix-f.second-ursell.645-646` | `dimock_ii` | 92 | 645, 646 | `source_extracted` |
| `dimockii.cluster-with-holes.501-506` | `dimock_ii` | 69-70 | 501, 502, 503, 504, 505, 506 | `source_extracted` |
| `dimockii.fluctuation-covariance.271-276` | `dimock_ii` | 38-39 | 271, 272, 273, 274, 275, 276 | `source_extracted` |
| `dimockii.lemma3.19.boundary-removal.507-510` | `dimock_ii` | 69-70 | 507, 508, 509, 510 | `source_extracted` |
| `dimockii.lemmaE.3.modified-metric-summability.627-632` | `dimock_ii` | 89-90 | 627, 628, 629, 630, 631, 632 | `source_extracted` |
| `dimockii.theorem3.1.normalization.201-205` | `dimock_ii` | 29 | 201, 202, 205 | `source_extracted` |
| `dimockiii.final-stability.224-226` | `dimock_iii` | 33 | 224, 225, 226 | `source_extracted` |
| `dimockiii.theorem1.local-e-r-b-bounds.14-25` | `dimock_iii` | 3-4 | 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25 | `source_extracted` |

## Consultas útiles

```powershell
python scripts/source_db.py search "Appendix F"
python scripts/source_db.py search "covariance resolvent"
python scripts/source_db.py search "E R B bounds"
python scripts/source_db.py show dimockii.appendix-f.second-ursell.645-646
python scripts/source_db.py lean PhysicalLocalizedCovarianceRootCertificate
```
