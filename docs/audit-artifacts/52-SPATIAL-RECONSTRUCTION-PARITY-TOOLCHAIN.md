# (52) Limpieza spatial-reconstruction y toolchain

Estado del draft: **documental/instrumental; separado de los carriles
matemáticos**. No modifica ningún enunciado Lean. No se ejecutó Lean, Lake,
oráculo ni carga sostenida local. Tampoco se abrió Colab: esta auditoría pudo
cerrar la clasificación con objetos y registros ya existentes.

## Dictamen operativo

1. La captura original `papers/spatial-reconstruction/spatial_reconstruction.tex`
   no está en
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
   relleno fail-closed que termine sin marcadores. Tras integrar la procedencia
   lateral en la rama de trabajo, ambos archivos se conservan con los nombres
   `spatial_reconstruction.tex.unverified` y
   `spatial_reconstruction.pdf.unverified`; esos sufijos son parte del bloqueo
   de publicación y no alteran sus bytes capturados.
4. `papers/parity-barriers` sí está en el árbol principal. Su verificación
   histórica pertenece a Lean `4.30.0-rc2` + Mathlib
   `cd3b69baae9cd81a572a3720f2372655eca39038`. El árbol principal fija Lean
   `4.29.0-rc6` + Mathlib
   `07642720480157414db592fa85b626dafb71355b`; la mera fuente presente no
   equivalía a `.olean` materializado ni a verificación en ese pin.
5. El gate posterior ya fue ejecutado en Colab sobre el blob exacto. Pasó y
   materializó `.olean` sin cambios de fuente ni enunciados, por lo que la
   migración técnica queda autorizada con procedencia dual explícita.

## Separación del nuevo carril matemático y del paper

La ampliación posterior solicitada por el owner se mantiene fuera de esta
limpieza de procedencia. `YangMills/OS/OSReconstructionUniform.lean` compone
resultados Lean ya existentes sin rellenar ninguna medida de
spatial-reconstruction ni migrar parity-barriers. El manuscrito independiente
`papers/os-reconstruction-uniform/os_reconstruction_uniform.tex` documenta esa
composición; es un paper nuevo, no una revisión ni una resubida de los papers
preexistentes. Su validación Colab y su objeto congelado se registran en
artefactos de auditoría separados.

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

## Decisión de migración

**Decisión medida:** se puede migrar el artefacto Lean a los pins principales
sin cambiar un byte de fuente, prueba, firma o enunciado. El blob LF
`3d341e22…` pasó sin edición con `lake env lean
papers/parity-barriers/ParityBarrier.lean` (exit 0, 17:17:26Z--17:17:35Z) en
Lean 4.29.0-rc6/Mathlib `0764272…`. Una segunda invocación explícita con `-o`
materializó un `.olean` de 270184 bytes, SHA-256 `7cb4d44f…`, también con exit
0. El estado queda `reproduced_unchanged_on_main_tree`,
`statement_change_requirement=none` y `migration_authorized=true`.

Esto no reescribe la procedencia histórica: el PDF enviado conserva su pase
registrado en 4.30.0-rc2/`cd3b69b…`; la reproducción en pins principales es una
evidencia posterior y separada. El transcript queda en
`papers/parity-barriers/MAIN-TREE-REPRODUCTION-LOG.txt`. Ningún paper existente
necesita resubirse por este saneamiento.

## Guards y ataques intentados

`scripts/check_publication_provenance.py` es local-light: solo lee TeX/JSON,
normaliza EOL y calcula hashes. En los carriles gobernados:

- falla si el segundo argumento de `\osline` no es numérico;
- falla si una celda `@@TOKEN@@` conserva un token publicable;
- falla ante placeholders explícitos;
- falla si un artefacto Lean gobernado carece de
  `ARTIFACT-TOOLCHAIN.json`, si los pins principales declarados derivan, o si
  cambian el source/log respecto de sus hashes;
- una autorización de migración solo es aceptada si declara reproducción
  inalterada, exit 0, pins principales, hash de fuente y evidencia adyacente.

CI ejecuta el guard, pero no Lean/Lake. Ataques reproducidos por tests: variantes
`DEFLINE`/`SITENNVEC`, `JOBSAFTER` en celda marcada, ausencia de declaración y
drift del hash de la fuente y una autorización sin evidencia de reproducción.
Un barrido inicial de todos los refs agotó el límite
local-light a ~34 s y se abandonó; las consultas posteriores fueron dirigidas y
menores de 30 s. No se usó ese barrido truncado como evidencia.

El oráculo exhaustivo del carril del paper añadió ataques instrumentales: una
fuente presente sin `.olean`, cuerpo transferido con 302 bytes LF de drift,
tres consultas a constantes sin import del bridge, y un proceso secuencial
huérfano que seguía escribiendo el primer log combinado. El escritor fue
identificado con `fuser`, detenido y descartado; el log aceptado se reconstruyó
solo desde los cuatro chunks completos y produjo 3046 informes, cero `sorry` y
cero axiomas no estándar. El detalle y los hashes están en
`52-os-reconstruction-uniform-verification.json`.
