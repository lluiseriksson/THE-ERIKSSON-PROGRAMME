# Auditoría independiente final — paquetes históricos A

Fecha: 2026-08-01 (Europe/Stockholm)  
Alcance read-only: `output/publication-audit/2602.0052-v3`, `2602.0036-v3` y `2602.0035-v2`.  
Fuentes de contraste: censo público congelado, ledger y `tmp/publication-audit/legacy-packages-a/LEGACY-PACKAGES-A-AUDIT.*`.

## Dictamen ejecutivo

| Paquete | Acción | Auditoría matemática | Estado tras reauditoría | Restricción restante |
|---|---|---|---|---|
| `2602.0052-v3` | `REPLACE-VERSION` | **PASS**: restauración auténtica y retractación prudente | **LISTO-LOCAL / INDEPENDENT-AUDIT-PASS** | Mantener HOLD de envío hasta que el owner congele el manifiesto global. No hay deuda matemática ni de paquete. |
| `2602.0036-v3` | `REPLACE-VERSION` | **PASS**: retirada correcta de Theorem 3.1/Corollaries 3.2–3.3 | **LISTO-LOCAL / INDEPENDENT-AUDIT-PASS** | Enviar después de `0052`; no queda bloqueo propio. |
| `2602.0035-v2` | `REPLACE-VERSION` | **PASS** dentro del scope explícito de la nota | **LISTO-LOCAL / INDEPENDENT-AUDIT-PASS** | Es un gate de orden, no de preparación local: debe ir después de `0052`, `0036` y `0033` R30. |

**Separación de estados.** La capa matemática y la capa de paquete pasan en los tres casos. `LISTO-LOCAL` no autoriza envío: `0035` conserva su dependencia de orden y los tres permanecen bajo el HOLD global del owner.

## Reauditoría de la corrección del hallazgo P1

El hallazgo de la primera pasada era real: `LOCK.json` fijaba el SHA de un PDF TeX intermedio sensible a la ruta, por lo que un paquete congelado verificaba pero `build -> verify` fallaba en otra ruta. La corrección elimina únicamente ese intermedio del lock y desacopla el verificador del manifiesto distribuible estático. El builder global será el responsable de producir el manifiesto canónico del conjunto.

Se copiaron de nuevo los tres paquetes a un directorio temporal aislado **sin ningún directorio `artifacts`**. En cada copia se ejecutó `python build_package.py`, seguido inmediatamente por `python verify_package.py` y `python -O verify_package.py`. Los builds terminaron con código 0, `overfull=0`, reprodujeron el SHA final exacto, y ambos modos del verificador pasaron:

| Paquete | SHA-256 final | Build | O0 | O1 | Checks | Pixels | `assert` |
|---|---|---|---|---|---:|---:|---:|
| `2602.0052-v3` | `4ce8cb39d5e47b59c27c88a3398660ca61985dff1f7589cf04c8ea472e09733b` | PASS | PASS | PASS | 32 | 16/16 | 0 |
| `2602.0036-v3` | `7e86eb7ba4e3ac1d79345632d20140b4b5fc8407fb9f55a171ec2bf79dd0b12f` | PASS | PASS | PASS | 36 | 19/19 | 0 |
| `2602.0035-v2` | `053107800c2b81f2f6649016f095f748146acf5af073eea0a7776ab7da575db8` | PASS | PASS | PASS | 38 | 21/21 | 0 |

### Scope del lock corregido

| Paquete | Objetos locales bloqueados |
|---|---|
| `0052` | PDF final; v1 público auténtico; fuente TeX de la nota |
| `0036` | PDF final; provenance PDF; v2 público; fuente TeX de la nota |
| `0035` | PDF final; provenance PDF; `0052v2` público mal archivado; fuente TeX de la nota |

El diff de `build_package.py` es vacío. En `verify_package.py` sólo se retiró el bloque que releía `MANIFEST.txt`; permanecen: hashes del lock, hash canónico del PDF final, páginas/cifrado, límites y HOLD de la ficha, frases de claims, render completo y comparación pixel de cada página contra sus segmentos. No se ocultó ni se debilitó un check canónico sobre el PDF distribuible.

La reducción del número de checks (67→32, 77→36, 79→38) corresponde a dejar de verificar dentro del paquete las filas del manifiesto estático. No corresponde a suprimir controles de contenido: fuente, inputs y final siguen bloqueados; composición y 56 páginas siguen verificadas. Los demás ficheros distribuibles —builder, verificador, ficha, informes y transcripts— deben quedar cubiertos por el manifiesto canónico global, como se ha especificado.

## Verificación congelada previa y ausencia de `assert`

Sobre copias nuevas de los paquetes congelados, antes de reconstruir:

| Paquete | O0 | O1 | Checks | Páginas pixel-comparadas | `assert` activo |
|---|---|---|---:|---:|---:|
| `0052` | PASS | PASS | 67 | 16/16 | 0 |
| `0036` | PASS | PASS | 77 | 19/19 | 0 |
| `0035` | PASS | PASS | 79 | 21/21 | 0 |

La tabla anterior pertenece a la primera pasada sobre el objeto congelado. La reauditoría limpia de esta corrección, documentada arriba, cierra el fallo post-build.

## Auditoría matemática por paquete

### `2602.0052-v3`: restauración de *Interface Lemmas* y retractación

**Identidad.** La nota, p. 1, restaura el v1 auténtico `Interface Lemmas...` (SHA público congelado `2ef7856e...`) y documenta que el v2 público del registro sirve el Morse–Bott de `0035`. La acción preservadora correcta es `REPLACE-VERSION`, no `WITHDRAW-RECOMMENDED`.

**Claims.** El diagnóstico matemático es suficiente y está formulado con la clase correcta:

- pp. 2–3: para `-I in SU(2)`, el logaritmo principal impreso da `i*pi*I`, de traza no nula, fuera de `su(2)`. Además, una sección global `su(2)`-valuada y equivariante por conjugación no puede existir en `-I`: centralidad fuerza que su valor sea invariante por adjoint, luego cero, cuya exponencial no es `-I`. Esto refuta la construcción, no el enunciado abstracto de medibilidad; la nota lo distingue correctamente.
- pp. 2–3: sustituir `beta_0` en una cota superior creciente en `beta` no produce uniformidad para `beta >= beta_0`. Holley–Stroock puede dar una cota uniforme en una ventana acotada, pero no demuestra Lemma 6.3 sin el input interbloque. Las tres muestras numéricas se presentan sólo como evidencia.
- pp. 3–4: los puentes RCP/RG, el componente de horizonte aleatorio, la suma sobre animales y la analiticidad/decay de boundary terms quedan como no establecidos; no se venden como contraejemplos a los enunciados.
- p. 4: el contra-modelo `beta_k=beta_0+Ck`, `g_k=(beta_0+Ck)^(-1/2)`, `p_0(g)=c_0|log g|^(1+epsilon_0)` muestra que las hipótesis impresas no implican decaimiento geométrico en `k`.

**Decisión matemática:** PASS. Es una retractación completa y prudente; no necesita recuperar un verificador externo para justificar que retira los claims. Tras reparar el P1 común puede marcarse `LISTO-LOCAL`.

### `2602.0036-v3`: traza de O’Neill y retirada Ricci

- p. 1 retira Corollaries 3.2–3.3 y separa el problema de la realización global del operador.
- p. 2 rederiva la identidad correcta. `Ric_A(X^h,X^h)` traza curvaturas seccionales horizontales y verticales, mientras que `Ric_B` suma las horizontales y añade el término de O’Neill. Al expresar `Ric_B` mediante `Ric_A` aparece `-sum_a K_A(X^h,V_a)` además del término positivo horizontal. Para la métrica bi-invariante del producto, los términos mixtos son no negativos antes de la resta; omitirlos tiene signo favorable espurio. Esto invalida la derivación impresa sin demostrar que la cota puntual sea falsa.
- p. 3 separa correctamente el resultado RCD de `2602.0046`, que vive sobre otra medida y otro operador, y p. 4 limita el alcance de la nota.

**Decisión matemática:** PASS. Theorem 3.1 queda `not established`, no `false`; los dependientes `0033` y `0035` ya no pueden citar la cota. Tras reparar el P1 común puede marcarse `LISTO-LOCAL`.

### `2602.0035-v2`: Morse–Bott corregido y propagación upstream

- pp. 1–4 distinguen ángulo de holonomía total y ángulo por enlace. La métrica inducida escala como `L^(d-2)`, no `L^d`. El test `L=6`, `Theta=pi/2`, `alpha=2`, `k=pi/3` da lado izquierdo `2` y derecho `3-sqrt(3)`, refutando la igualdad de senos impresa. La acción de Weyl de `SU(2)` es simultánea, los labels de Fourier dependen del holonomy y el recuento depende del centralizador; no hay bundle normal ordinario en el locus singular. El gap normal se cierra al aproximarse al locus de estabilizador aumentado, de modo que no hay cota uniforme sobre todo el estrato suave.
- pp. 4–7 retiran que H1 esté descargada y que H-FACT sustituya por sí sola H2; registran el loop con `0033` y mantienen Theorem 6.3 sólo como implicación condicional bajo hipótesis nombradas.
- pp. 5–7 separan `dVol_B`, la pushforward `nu` y la medida de ground state. En el estrato regular `dnu=w dVol_B`, por lo que los generadores difieren por drift salvo una identificación adicional. También corrigen el doble conteo de `det M`.
- La positividad cualitativa a volumen fijo sobre el sector gauge-invariant sí sigue de compacidad, conectividad, elípticidad y positivity improving. La nota no la convierte en cota uniforme ni continuum theorem.
- pp. 8–11 fijan el objeto/medida/operador y advierten que cambiar uno no descarga automáticamente un claim sobre otro. Las pp. 12–21 son la revisión Morse–Bott que estaba mal archivada como `0052v2`, preservada y expresamente subordinada a la nota.

**Decisión matemática:** PASS dentro del scope literal. No hay que exigir el antiguo verificador de 14 checks para aceptar una nota que reclasifica esos checks como author-reported y retira los claims que exceden lo probado. El paquete sólo puede pasar a `LISTO-LOCAL` después de reparar el P1 común y después de `0052`, `0036` y R30.

## Ficha de envío y orden

Las tres fichas tienen categoría `Quantum Physics`, autor `Lluis Eriksson` y títulos coherentes con el censo/restauración. Los límites son admisibles:

| Paquete | Abstract | Comments |
|---|---:|---:|
| `0052` | 180 palabras | 24 palabras |
| `0036` | 154 palabras | 24 palabras |
| `0035` | 156 palabras | 26 palabras |

Los abstracts mantienen las clases `false construction`, `proof invalid/not established`, `conditional`, `qualitative fixed-volume` y `numerical evidence`. Los comments son breves y técnicos. El orden relativo inscrito es correcto:

1. `2602.0052-v3` — restaura primero el registro auténtico y elimina la duplicación cruzada.
2. `2602.0036-v3` — retira la cota Ricci antes de sus consumidores.
3. `2602.0033` R30 — fuera de este sublote.
4. `2602.0035-v2` — último de esta cadena.

## Preflight PDF, preservación e inspección visual

Se renderizaron de nuevo los tres finales a 140 dpi y se inspeccionaron visualmente **56/56 páginas** en 15 hojas de contacto.

| Paquete | Cifrado | Fonts | MediaBoxes | Content streams preservados | Pixel preservation | Resultado visual |
|---|---|---|---|---:|---:|---|
| `0052` | no | todos embebidos | A4 pp. 1–16 | 16/16 | 16/16 | sin defectos |
| `0036` | no | todos embebidos | A4 pp. 1–8; Letter pp. 9–19 | 19/19 | 19/19 | sin defectos |
| `0035` | no | todos embebidos | A4 pp. 1–11; Letter pp. 12–21 | 21/21 | 21/21 | sin defectos |

No se observaron recortes, solapamientos, glifos rotos, ecuaciones o tablas ilegibles, ni transiciones corruptas. Los cambios A4/Letter son consecuencia explícita de preservar los tramos históricos. Los Type 3 antiguos están embebidos pero algunos carecen de ToUnicode; por ello la inspección visual y la comparación de pixels/streams, no sólo `pdftotext`, son la evidencia apropiada.

La composición queda verificada por streams, cajas y pixels:

- `0052`: pp. 1–5 = nota; pp. 6–16 = v1 público auténtico.
- `0036`: pp. 1–4 = nota; pp. 5–8 = provenance; pp. 9–19 = v2 público.
- `0035`: pp. 1–7 = nota; pp. 8–11 = provenance; pp. 12–21 = `0052v2` público mal archivado.

## Obligaciones restantes

1. Hacer que el builder global incluya builder, verificador, ficha, informes y transcripts en su manifiesto canónico distribuible; esta obligación es global, no un bloqueo propio de los tres PDFs.
2. Mantener `0035` después de `0052`, `0036` y `0033` R30 en el manifiesto/orden del owner.
3. No convertir `LISTO-LOCAL` en autorización de click: el envío continúa reservado al owner.

No queda obligación matemática ni fallo de reproducibilidad dentro del scope local de estos tres paquetes. `0035` conserva sólo un gate causal de orden.

**NO ENVIAR TODAVÍA.**
