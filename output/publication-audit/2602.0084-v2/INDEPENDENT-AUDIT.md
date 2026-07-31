# Auditoría independiente adversarial de 2602.0085-v2 y 2602.0084-v2

Fecha: 2026-08-01 (Europe/Stockholm)  
Alcance: sólo lectura sobre `output/publication-audit/2602.0085-v2` y
`output/publication-audit/2602.0084-v2`; las reconstrucciones y renders se hicieron
en copias bajo este directorio temporal.  
Fuente de contraste: PDFs públicos v1 congelados dentro de cada paquete y
`tmp/publication-audit/legacy-packages-b/LEGACY-PACKAGES-B-AUDIT.md/.json`.

## Cierre posterior de paquete

Los bloqueos de distribucion se cerraron sin modificar los PDFs auditados: el
informe actualizado sustituyo al informe obsoleto, cada ficha apunta al commit
inmutable `47e2ba538229c9a926c913edac78e31b47285977`, y los ZIPs deterministas excluyen
los PDFs intermedios no reproducibles. El estado final de ambos paquetes es
**LISTO-LOCAL**. La tabla siguiente conserva el dictamen previo al cierre.

## Dictamen ejecutivo previo al cierre

| Referencia | Acción matemática | Dictamen del PDF candidato | Dictamen del paquete | Riesgo / bloqueo |
|---|---|---|---|---|
| `ai.viXra:2602.0085v1` | **REPLACE-VERSION** por `2602.0085v2` | **PASS independiente**: la retractación es matemáticamente correcta, el PDF final es reproducible, uniforme A4 y visualmente íntegro | **REVIEW-PENDING**; no está distribuible todavía | Faltan manifiesto, ZIP, enlace GitHub inmutable y orden global; el PDF intermedio de la errata no es byte-reproducible y debe excluirse de distribución |
| `ai.viXra:2602.0084v1` | **REPLACE-VERSION** por `2602.0084v2`, siempre después de 0085 | **PASS independiente** tras la reconstrucción uniforme en US Letter: contenido, preservación, preflight y las 21 páginas visuales pasan | **REVIEW-PENDING**; no está distribuible todavía | Faltan manifiesto, ZIP, enlace GitHub inmutable y orden global; el informe de auditoría dentro del paquete aún cita el candidato obsoleto `730eb00b`; el PDF intermedio no es byte-reproducible y debe excluirse |

No se pulsó ni se envió nada a viXra/arXiv.

## 1. Integridad, reconstrucción y verificadores

### 2602.0085-v2

- PDF final: `artifacts/2602.0085v2-deff7be4-26pp.pdf`.
- SHA-256: `deff7be46aa56ddfbcac63addce730a4bc4449768e5920951d1a304912525518`.
- Tamaño: 816,370 bytes; 26 páginas; no cifrado; rotación 0; A4 uniforme
  (`595.276 x 841.890 pt`) en las 26 páginas.
- Composición: 5 páginas nuevas de errata + 21 páginas públicas v1 preservadas.
- Input público v1: 458,519 bytes; SHA-256
  `930e7ea90a21b78a71fe73bfcc48519b0ee17c66f9fe23bdf7fead21829dfd8d`.
- Fuente de errata: 17,185 bytes; SHA-256
  `2b19be4b5a429dd1abd94927e41cc08fd1e82e80181c57b06f54cce18a0f3c86`.
- `build.py`: SHA-256
  `651d80f90e97b2aac9e00e9e51a4674c17be4df1f912bd32ae5d2a6d49c66683`.
- `verify.py`: SHA-256
  `f0da44060b05aa2d0cb5f0c6ebde821d72969ae1ccbfed97220e2fbd2439f0eb`.
- Dos builds desde copias limpias produjeron exactamente el mismo nombre, número de
  páginas y SHA del PDF final, coincidente además con el candidato del paquete.
- `python verify.py` y `python -O verify.py`: PASS completos; niveles de optimización
  observados 0 y 1. Un barrido independiente encontró cero sentencias `assert` en
  los dos paquetes.
- Los cuatro logs limpios (dos builds por paquete) no contienen `Overfull`,
  `Underfull`, warning LaTeX, referencia indefinida ni error.
- Inventario de fuentes: 50 filas; cero fuentes no incrustadas.

Hallazgo de reproducibilidad limitado: los PDFs intermedios
`erratum_2602_0085.pdf` de los dos builds tienen SHA distintos
(`2738f009...` y `4369c61d...`). El ensamblaje final con `pypdf` sí es
byte-determinista. Por tanto, el PDF intermedio, AUX y LOG no deben formar parte del
paquete de distribución ni de su manifiesto de artefactos finales.

### 2602.0084-v2

- PDF final actual: `artifacts/2602.0084v2-4099349d-21pp.pdf`.
- SHA-256: `4099349dc23496d5938e5dee8092de991083c92dea15481a3a69d2c1ba008bc9`.
- Tamaño: 667,188 bytes; 21 páginas; no cifrado; rotación 0; US Letter
  uniforme (`612 x 792 pt`) en las 21 páginas.
- Composición: 6 páginas nuevas de errata + 15 páginas públicas v1 preservadas.
- Input público v1: 324,928 bytes; SHA-256
  `633c08d3f3528b60cdbcaf0d13c257aa49f6df68f4717802170dc50beeb52211`.
- Fuente de errata: 22,282 bytes; SHA-256
  `a4cfb23906c88a35370aca44072c5ca5e0aaf77089ebaf59c7e58ba5ebf15e6a`.
- `build.py`: SHA-256
  `66d1611c5efa104928bdcd4877a5d7359a9ef4883352259181692a449792e1ed`.
- `verify.py`: SHA-256
  `b529ce909799e48b11afd1d04b2085fad8ace03341f403b58c0d48f570eec62f`.
- `SUBMISSION-ID.txt`: SHA-256
  `41549b55f9b1a22435ff98bd4f2ca795a3a7565c83e328b68eb291b64c8fe0c1`.
- `artifacts/build-result.json`: SHA-256
  `6e85fda6b93c14caa36f431af2657134feedf3e8b55b4eb3c4ff3d5908763f50`;
  nombre, SHA, páginas, composición, SHA del v1 y SHA de fuente coinciden con los
  ficheros recontados independientemente.
- Dos builds desde copias limpias produjeron exactamente el mismo PDF final y el
  mismo SHA que el candidato del paquete.
- `python verify.py` y `python -O verify.py`: PASS completos; cero `assert`.
- Inventario de fuentes: 50 filas; cero fuentes no incrustadas.

El control independiente con `pypdf` en modo estricto confirmó 21 cajas idénticas,
sin rotación ni cifrado. La fuente declara `letterpaper`, márgenes horizontales de
2.4 cm, verticales de 1.5 cm y `emergencystretch` de 3 em. Los dos logs de las builds
limpias no contienen `Overfull`, `Underfull`, warning, referencia indefinida ni
error. Los candidatos finales obsoletos ya no existen en `artifacts`; `build-result.json`
y `SUBMISSION-ID.txt` apuntan al único PDF final nuevo.

También aquí los intermedios `erratum_2602_0084.pdf` de dos builds tienen SHA
distintos (`c7f3ab24...` y `e0d01cf8...`), aunque el PDF final actual sea
byte-determinista. Se aplica la misma exclusión de distribución.

Hallazgo de coherencia de paquete: `output/publication-audit/2602.0084-v2/INDEPENDENT-AUDIT.md`
sigue citando el candidato retirado `730eb00b...` y el bloqueo MediaBox ya corregido.
Ese informe congelado no invalida el PDF nuevo, pero sí impide considerar cerrado el
paquete hasta reemplazarlo por este dictamen actualizado y volver a fijar hashes.

## 2. Preservación y auditoría visual completa

Se renderizaron de nuevo los dos PDFs finales y los dos inputs públicos a 150 dpi.
La comparación independiente de hashes PNG dio identidad exacta en las 36 páginas
preservadas:

- 0085 final pp. 6-26 = v1 pp. 1-21, 21/21 pixel-idénticas.
- 0084 final pp. 7-21 = v1 pp. 1-15, 15/15 pixel-idénticas.

Después se inspeccionaron visualmente las 47 páginas finales, no sólo el texto
extraído:

| PDF | Páginas inspeccionadas | Resultado visual |
|---|---|---|
| 0085 | 1, 2, 3, 4, 5 | Errata legible; tabla, ecuaciones, pies y nota de provenance completos; sin cortes, solapes ni glifos rotos |
| 0085 | 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26 | V1 preservado completo; ecuaciones, tablas, referencias y pies visibles; sin regresiones de render |
| 0084 | 1, 2, 3, 4, 5, 6 | Errata legible; la tabla de estado y todos los contraejemplos caben; sin cortes, solapes ni glifos rotos |
| 0084 | 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21 | V1 preservado completo; los marcos rojos/verdes de hipervínculo ya presentes en el PDF público siguen visibles y son pixel-idénticos, no una nueva corrupción; sin recortes ni glifos rotos |

La reauditoría visual posterior a la reconstrucción no encontró cortes, solapes,
tablas truncadas, ecuaciones salidas de página ni glifos rotos. El cambio de página
6 (fin de la retractación) a página 7 (portada del v1 preservado) es limpio. Los
marcos de hipervínculo coloreados del v1 siguen siendo una característica heredada,
no una regresión del ensamblaje.

## 3. Contraste matemático: 2602.0085

La acción **REPLACE-VERSION** está justificada por relación exacta de claims, no por
afinidad temática.

1. El v1 afirma la identidad de linealización en Lemma 3.6, Eq. (16), p. 9 del v1
   (p. 14 del PDF compuesto), y la usa en Lemma 3.8, Proposition 3.9 y Theorem 3.11
   (v1 pp. 10-12; compuesto pp. 15-17), culminando en Theorem 1.1 y su cierre
   (v1 pp. 4 y 16; compuesto pp. 9 y 21).
2. La errata pp. 1-2 da una refutación exacta en `U=1`. Por invariancia gauge, la
   Hessiana verdadera anula el subespacio tangente gauge de dimensión al menos
   `(|V|-1)(N^2-1)`. Si el grafo de pesos positivos es conexo, el Laplaciano escalar
   impreso sólo tiene un núcleo constante de dimensión `N^2-1`: las dos dimensiones
   son incompatibles para `|V|>2`.
3. Si el grafo de pesos positivos es disconexo, la cota con un único término
   estacionario `1/|G_k|` es falsa porque el kernel converge a
   `1/|C(e_0)| > 1/|G_k|`. El caso disconexo no rescata la cadena.
4. El test gauge soportado en un vértice también contradice la cota de columna de
   Proposition 3.9. Al escoger el tiempo de modo que el término transitorio no exceda
   `1/|G_k|`, la desigualdad impresa fuerza `|G_k| <= 4d`; en dimensión 4 falla para
   cualquier torus de la secuencia con más de 16 links. La constante `4d` es correcta
   en esa elección (incluye los dos términos iguales dentro de la raíz).
5. La propagación está bien delimitada: se retiran Lemma 3.6, Lemma 3.8,
   Proposition 3.9, Theorem 3.11 y Theorem 1.1. No se declara cerrado OS, límite
   termodinámico ni mass gap.
6. Los supervivientes no están inflados: Lemma 2.2 (covariancia gauge) y
   Proposition 1.3 (conmutación flujo-reflexión) no dependen de Eq. (16). Lemma 3.2
   sólo se describe como recuperable tras especificar por separado un kernel escalar;
   su instanciación original se retira.

El abstract y la change note de envío reproducen estas distinciones. No queda deuda
matemática detectada dentro de la retractación misma.

## 4. Contraste matemático: 2602.0084

La errata cubre correctamente los defectos A-G del informe legacy B y los contrasta
con las páginas impresas originales:

| Defecto | Claim original | Evidencia exacta y dictamen |
|---|---|---|
| A | `omega_L^t` existe por 0085 Theorem 1.1; v1 pp. 1-2 y Step 4 de Theorem 4.4, p. 10 | 0085 retira ese teorema; el objeto no queda construido por la cita. Theorem 4.4 y Proposition 5.3 se retiran |
| B | Lemma 3.1 importa la dominación de 0085; v1 p. 4 | Es exactamente la cadena refutada en 0085. El modo gauge estacionario da además contradicción puntual para un grafo conexo grande |
| C | Lemma A.1, v1 p. 14, afirma una cota varianza-oscilación para cualquier medida | La medida correlacionada en dos puntos y `Phi=(f(U1)+f(U2))/2` da varianza 1 frente a RHS 1/2. La desigualdad, no sólo la prueba, es falsa |
| D | Theorem 5.1, v1 pp. 11-12, deduce un generador positivo autoadjunto de Hille-Yosida | Las hipótesis impresas hacen al semigrupo inducido isométrico, no autoadjunto. La conjugación no trivial en `M_2(C)` con traza es un contraejemplo exacto |
| E | Lemma 3.3, v1 p. 5, convierte diferencia de representantes temporales en distancia de grafo | En el corte periódico, un link espacial en el representante máximo y el link temporal que envuelve son adyacentes pero sus mínimos temporales difieren `L-a_k`. Afecta también a la hipótesis de soporte de Theorem 4.4 |
| F | Lemma 3.5, v1 pp. 5-6, usa el Jacobiano en un endpoint para una aplicación no lineal | La regla correcta integra el Jacobiano a lo largo de la geodésica o usa un supremo uniforme. El claim impreso omite ambos y es falso tal como está |
| G | Lemma 3.1, v1 p. 4, da una cota gaussiana sin término estacionario para todo tiempo | En un grafo finito conexo, `p_tau` tiende a `1/|G_k|` mientras el RHS tiende a cero. El bound es falso aun antes de considerar modos gauge |

La nota no sobreafirma el resultado negativo: declara expresamente que estos defectos
invalidan la prueba y varios enunciados impresos, pero no prueban falsa la conclusión
deseada de casi-positividad por reflexión. Las tres rutas de reparación se presentan
como rutas que requieren pruebas nuevas.

La lista positiva queda prudentemente limitada a Definitions 2.2, 2.5 y 2.6 como
definiciones, y Theorem 4.1 como resultado citado de Osterwalder-Seiler. No se intenta
salvar Lemma 3.3 ni Theorem 5.1 por inercia.

## 5. Campos de envío y límites

| Paquete | Abstract | Comments | PDF | Resultado |
|---|---:|---:|---:|---|
| 0085 | 144 palabras / 979 caracteres | 31 palabras / 192 caracteres | 816,370 bytes | Abstract < 400 palabras; comments breves; PDF < 5 MB |
| 0084 | 156 palabras / 988 caracteres | 28 palabras / 159 caracteres | 667,188 bytes | Abstract < 400 palabras; comments breves; PDF < 5 MB |

Categoría, título, autor, número de páginas, acción de reemplazo, URL pública y SHA
del v1 son internamente consistentes en ambos `SUBMISSION-ID.txt`. El orden causal
local también es correcto: 0085 primero, 0084 después. No se comprobó contra un
formulario autenticado un límite de caracteres distinto del checklist local; el
owner debe repetir el recuento después de pegar.

## 6. Bloqueos y condición de promoción

### 0085

Puede promoverse el PDF candidato a `LISTO-LOCAL` sólo después de:

1. incorporar este dictamen independiente al paquete y cambiar de forma explícita
   los estados `BUILT-NOT-INDEPENDENTLY-AUDITED` / `HOLD`;
2. crear manifiesto completo y ZIP determinista, con manifiestos interno y externo
   byte-idénticos y SHA del ZIP;
3. excluir PDF intermedio, AUX, LOG y QA del payload distribuible;
4. fijar enlace GitHub inmutable y orden global literal en `SUBMISSION-ID.txt`;
5. verificar de nuevo los hashes después de esos cambios de metadatos.

### 0084

El PDF candidato ya supera la reconstrucción y reauditoría que exigía el dictamen
anterior. Para promover el paquete requiere los mismos cinco cierres enumerados para
0085 y, además, sustituir el `INDEPENDENT-AUDIT.md` interno obsoleto, recalcular el
manifiesto con el informe correcto y comprobar que no sobreviva ninguna referencia
al SHA `730eb00b...`.

Hasta esos cierres de empaquetado, el orden correcto permanece **0085 -> 0084** y
ambos paquetes deben quedar fuera de cualquier cola de envío. No queda bloqueo de
preflight ni deuda matemática detectada en el PDF candidato nuevo de 0084.
