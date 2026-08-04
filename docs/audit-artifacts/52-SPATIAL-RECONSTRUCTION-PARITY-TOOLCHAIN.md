# (52) Limpieza spatial-reconstruction y toolchain

Estado del draft: **documental/instrumental; separado de los carriles
matemáticos**. No modifica ningún enunciado Lean. No se ejecutó Lean, Lake,
oráculo ni carga sostenida local. Tampoco se abrió Colab: esta auditoría pudo
cerrar la clasificación con objetos y registros ya existentes.

## Dictamen operativo

1. `papers/spatial-reconstruction/spatial_reconstruction.tex` no está en
   `origin/main`; se localizó en la procedencia lateral `origin/d3-closure`.
   En la captura `c76b790505268eedcb8fe126bc399ccab82baa4f`, su blob es
   `92c8bbd31eee16d908c82073add3b71f9c4d656d` (40049 bytes).
2. El TeX contiene **32 placeholders publicables sin resolver**: 20 anclas
   `\osline` no numéricas y 12 celdas de medida. El inventario canónico y
   exhaustivo es
   `docs/audit-artifacts/52-spatial-placeholder-inventory.json`.
3. El artefacto queda **QUARANTINED / NOT FROZEN**. No debe citarse como
   artefacto congelado, ni su PDF como render reproducible del TeX, hasta que
   exista un único anchor final, una medición perteneciente a ese anchor y un
   relleno fail-closed que termine sin marcadores.
4. `papers/parity-barriers` sí está en el árbol principal, pero su verificación
   pertenece a Lean `4.30.0-rc2` + Mathlib
   `cd3b69baae9cd81a572a3720f2372655eca39038`. El árbol principal fija Lean
   `4.29.0-rc6` + Mathlib
   `07642720480157414db592fa85b626dafb71355b`. La fuente presente no equivale
   a `.olean` materializado ni a verificación en el pin principal.
5. La migración de parity **no está demostrada y no queda autorizada**. No hay
   evidencia para afirmar que requiera o no cambios de enunciado. Por ello esta
   tarea se detiene antes de tocar Lean y entrega el plan de gate de migración.

## Inventario exhaustivo de spatial-reconstruction

La captura tiene 42 usos de `\osline`: 22 numéricos y 20 no numéricos. Los 20
marcadores no numéricos y la línea candidata observada en el blob Lean
`33b5534589b3a22cd3b7bfd4f4592f3e66462252` son:

| Token | Línea TeX | Declaración | Línea candidata del blob |
|---|---:|---|---:|
| `SITENNVEC` | 353 | `siteForm_self_nonneg` | 216 |
| `DEFLINE` | 361 | `siteForm_self_eq_zero_iff` | 372 |
| `SEPLINE` | 363 | `siteForm_right_ext` | 399 |
| `UNIQLINE` | 370 | `transferOp_unique` | 409 |
| `OPLLINE` | 373 | `transferOpL` | 459 |
| `QEQUIVLINE` | 379 | `sqrtWeightEquiv` | 536 |
| `SIMILARLINE` | 387 | `transferOpL_comp_sqrtWeightEquiv` | 606 |
| `EIGIFFLINE` | 394 | `transferOp_eigenvalue_iff` | 615 |
| `FWDEIGLINE` | 409 | `transferOp_eigen_of_symWeighted` | 505 |
| `KERLINE` | 432 | `mem_ker_collapseL_iff` | 1699 |
| `PHYSLINE` | 435 | `physicalEquiv` | 1718 |
| `NORMLELINE` | 521 | `siteQ_transferOp_le` | 959 |
| `NORMATTLINE` | 522 | `siteQ_transferOp_perron` | 1116 |
| `NORMMINLINE` | 523 | `perron_norm_constant_minimal` | 1137 |
| `NORMGENLINE` | 525 | `norm_sq_le_perron` | 891 |
| `COERCLINE` | 542 | `bondQ_ge_siteQ` | 1320 |
| `COERGENLINE` | 543 | `spatialKernel_coercive` | 1208 |
| `INJLINE` | 551 | `transferOp_injective` | 1454 |
| `NORMTWOLINE` | 553 | `normalised_two_sided` | 1654 |
| `NORMBRIDGELINE` | 555 | `siteForm_normalisedTransferOpL_self` | 1614 |

Estas líneas candidatas son una observación del blob capturado, **no** valores
publicables: el TeX no declara ese commit como su anchor final y el filler exige
que medición, HEAD, blobs y anchor sean el mismo objeto. Además, los 22 anchors
ya numéricos también deben revalidarse contra el anchor final; no se heredan.

Las 12 celdas sin rellenar son:

| Token | Línea TeX | Evidencia existente | Decisión |
|---|---:|---|---|
| `JOBSAFTER` | 695 | 8469 en `c90dc745`/`28d772e9`; 8475 en `8e8375d3` incluye otro carril | no rellenar |
| `JOBSBEFORE` | 696 | 8468 en `345479fa`; 8469 en el anchor v1 | no rellenar |
| `JOBSDELTA` | 697 | +1 en campaña v1; 0 en replay `28d772e9` | ambiguo; no rellenar |
| `JOBSCAMPAIGNBASE` | 698 | 8468 en `345479fa` | histórico, no ligado al TeX final |
| `ORACLETOTAL` | 699 | 2883 / 2911 / 2980 en tres árboles distintos | ambiguo; no rellenar |
| `ORACLENONSTD` | 700 | 0 en los tres registros | no ligado a un anchor final |
| `DECLSOS` | 701 | sin valor final medido localizado | no verificado |
| `DECLSOSORACLE` | 702 | sin valor final medido localizado | no verificado |
| `DECLSREC` | 703 | sin valor final medido localizado | no verificado |
| `DECLSRECORACLE` | 704 | sin valor final medido localizado | no verificado |
| `SORRYCOUNT` | 707 | 0 en registros históricos y core `8e8375d3` | no ligado al TeX final |
| `COREERRORS` | 709 | 0 en `c90dc745`, `28d772e9`; core verde en `8e8375d3` | no ligado al TeX final |

El `measurements.json` del artefacto (blob
`44934393fdab2e77bec34c86fa6107364f8b2cae`, 777 bytes) es de v1 y no satisface
el esquema actual de `scripts/fill_p14.py`: usa `campaign_base`,
`main_merge_base` y `jobs_at_main_merge_base`, mientras el filler exige
`baseline_anchor`, `campaign_base_anchor` y `jobs_campaign_base`. El propio
handoff ordena regenerarlo desde un run, no traducirlo a mano.

## Evidencia medida que sí existe

- `c90dc745ab8cd1ba7ddc02aa16fed3de339bf958`: Colab, 8468→8469,
  oracle 2883, cero no estándar y cero `sorryAx` (ledger, Addendum 580).
- `28d772e9ddfe1f0cf6cffbba84db2e8309e2065a`: run terminal de 15 hijos,
  8469 jobs, delta 0, oracle 2911 y cero errores (handoff §1).
- `8e8375d3415575e997765e61515e1a8af283df97`: fresh clone Colab, core verde
  8475 y oracle 2980; el blob final de `SpatialReconstruction.lean` quedó
  compilado, pero el total incluye el carril Dobrushin (ledger, Addendum 590).

Ninguno de esos registros es una medición final generada para el TeX capturado.
Combinar sus números produciría una tabla sintética y queda expresamente
prohibido.

## Toolchain real de parity-barriers

El registro primario interno es
`papers/parity-barriers/LEAN-VERIFICATION-LOG.txt` (blob
`d79c65b32d0890cb95cd33861422432da763f231`): fecha 2026-07-09, comando
`lake env lean ParityBarrier.lean`, Lean `4.30.0-rc2`, Mathlib `cd3b69b…`,
exit 0 y oracle estándar. El commit de incorporación
`469495afee0a03aa887622888d3ea5d6a2f84f81` no cambió `lean-toolchain` ni
`lake-manifest.json`; ambos seguían declarando los pins 4.29/`0764272…`.
Por tanto, el log prueba un pase en otro entorno, pero el repositorio no
conservaba la configuración que lo produjo. `ARTIFACT-TOOLCHAIN.json` registra
ahora esa diferencia sin reetiquetarla como compatibilidad.

No se añade ninguna afirmación de prioridad bibliográfica en esta tarea; por
ello no se amplía la bibliografía ni se sustituyen fuentes primarias.

## Decisión y plan de migración

**Decisión actual:** no migrar y no cambiar enunciados en silencio. El estado es
`not_reproduced_on_main_tree`; `statement_change_requirement` queda
`not_determined`.

Gate para una tarea posterior:

1. Congelar `ParityBarrier.lean` por commit, blob, bytes y SHA-256 LF/CRLF,
   junto con los pins exactos del árbol principal.
2. Abrir un Colab Pro+ CPU/alta RAM, sin GPU, con runtime inicialmente
   desconectado; capturar hora de apertura, bootstrap y cierre.
3. Materializar exactamente el blob congelado y ejecutar primero
   `lake env lean papers/parity-barriers/ParityBarrier.lean`, sin editarlo.
4. Si pasa, registrar log, exit, hashes y objeto `.olean` materializado; solo
   entonces cambiar `migration_authorized` mediante otra tarea/auditoría.
5. Si falla, conservar el log completo y detenerse. Antes de reparar, producir
   un diff de firmas/enunciados. Si cualquier reparación exige cambiar una
   firma, entregar plan separado y pedir autorización; no aplicarla.

## Guards y ataques intentados

`scripts/check_publication_provenance.py` es local-light: solo lee TeX/JSON,
normaliza EOL y calcula hashes. En los carriles gobernados:

- falla si el segundo argumento de `\osline` no es numérico;
- falla si una celda `@@TOKEN@@` conserva un token publicable;
- falla ante placeholders explícitos;
- falla si un artefacto Lean gobernado carece de
  `ARTIFACT-TOOLCHAIN.json`, si los pins principales declarados derivan, o si
  cambian el source/log respecto de sus hashes.

CI ejecuta el guard, pero no Lean/Lake. Ataques reproducidos por tests: variantes
`DEFLINE`/`SITENNVEC`, `JOBSAFTER` en celda marcada, ausencia de declaración y
drift del hash de la fuente. Un barrido inicial de todos los refs agotó el límite
local-light a ~34 s y se abandonó; las consultas posteriores fueron dirigidas y
menores de 30 s. No se usó ese barrido truncado como evidencia.
