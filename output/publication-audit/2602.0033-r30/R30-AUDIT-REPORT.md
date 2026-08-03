# Auditoria independiente adversarial de R30

Fecha: 2026-07-31  
Objeto: reemplazo local de `ai.viXra:2602.0033` en
`output/publication-audit/2602.0033-r30`  
Alcance: solo lectura sobre el paquete fuente; las ejecuciones se hicieron sobre
copias byte-identicas bajo `tmp/publication-audit/r30-independent`.

## Cierre posterior de paquete

Los cuatro bloqueos de empaquetado detectados abajo se cerraron sin cambiar el PDF
auditado: se genero `MANIFEST-R30.txt` y un ZIP determinista con manifiesto interno
y externo byte-identicos; la ficha apunta al commit inmutable `cae239d1`; el orden
global es 3 de 9; y el PDF intermedio no forma parte del ZIP distribuible.  El
estado final del paquete es **LISTO-LOCAL**.  La seccion siguiente conserva el
veredicto adversarial emitido antes de esos cierres para no reescribir la historia.

## Veredicto previo al cierre de paquete

**REVIEW-PENDING.** El nucleo matematico corregido, el PDF final y la ficha activa
superan esta auditoria. No queda una deuda matematica R29->R30 detectada. El paquete
completo no puede marcarse `LISTO-LOCAL` todavia porque:

1. no existe `MANIFEST-R30.txt` ni ZIP R30 con manifiestos interno/externo
   byte-identicos;
2. `SUBMISSION-ID.txt` deja pendiente el enlace GitHub inmutable y el orden global;
3. `SUBMISSION-ID.txt` conserva `HOLD - BUILT, NOT YET INDEPENDENTLY AUDITED` y
   `build-result.json` conserva `BUILT-NOT-AUDITED`;
4. el PDF intermedio del erratum no es byte-reproducible entre compilaciones, aunque
   el PDF final ensamblado si lo es. Si el intermedio se distribuye o manifiesta, esta
   diferencia debe documentarse o eliminarse del paquete de envio.

Estos son cierres P1/P2 de paquete, no una obligacion matematica nueva. Si solo se
considera el PDF final y su fuente activa, el resultado material es apto para pasar a
`LISTO-LOCAL` una vez cerrados los cuatro puntos anteriores y repetido el barrido de
metadatos/hashes.

## 1. Identidad e integridad

| Objeto | Bytes | Paginas | SHA-256 | Resultado |
|---|---:|---:|---|---|
| `artifacts/2602.0033v3-R30-878dba7c-25pp.pdf` | 1,187,585 | 25 | `878dba7cc659477ea9172a24f9dba88498d41ba49af44cfdcb1a73baa13f6285` | PASS |
| `artifacts/erratum_2602_0033_r30.pdf` | 477,412 | 13 | `6f800d1847b840d99714f41833261e87e715e3c48807ebfc5587345ba8b5f4eb` | PASS como objeto congelado |
| `inputs/OBJECT-PROVENANCE-f3c2e1cb-4pp.pdf` | 311,758 | 4 | `f3c2e1cb9ffcc1a1c0f66f5da96fa415248480eebd03f7abd2d93458a5b5cd01` | PASS |
| `inputs/2602.0033v2-public.pdf` | 358,598 | 8 | `91a7d95e1decc1771c548533748916d9941a77f02937fddf90fb13e348730bfe` | PASS |
| `src/erratum_2602_0033.tex` | 57,859 | n/a | `6362b13aa7679e50432cdcf25bde10a0152dd96dfad8d3398586bff5eba4e530` | PASS |
| `src/OBJECT-PROVENANCE.tex` | 19,184 | n/a | `20c8790e6166e44565bd797d4a659daa3620ff05eb75c09a9025b07d4edea242` | PASS |
| `SUBMISSION-ID.txt` | 2,732 | n/a | `2f010e28e259fc9b304371f26edcd9db631e622890f22211bf19dbcdef01dc9d` | contenido PASS; estado pendiente |
| `verify_r30.py` | 6,180 | n/a | `60b0f16a6478b835c96cb112d098bfc0c0f7ba3c74e1f943f57e28db0445475a` | PASS |

El PDF final abre con `pypdf` en modo estricto, no esta cifrado, no contiene
formularios ni JavaScript, y declara 25 paginas. Todos los tipos de letra listados por
`pdffonts` estan embebidos. El v2 preservado contiene fuentes Type 3 sin mapa Unicode,
pero no se observaron glifos rotos y ese bloque es reproduccion historica, no texto
nuevo de R30.

La composicion mantiene tres numeraciones internas: erratum pp. 1--13, procedencia
pp. 1--4 y v2 pp. 1--8. En el PDF ensamblado son pp. 1--13, 14--17 y 18--25. Las
pp. 1--17 son A4 (`595.276 x 841.890 pt`) y las pp. 18--25 US Letter
(`612 x 792 pt`). Es una discontinuidad P2 heredada y visible, pero no produce recorte.

## 2. Verificacion matematica independiente

### 2.1 Condicion exact-trace corregida

R30 p. 6 define

`X_M=A_n(M) exp(-m_n(M)M)` y
`Y_M=A_(n+1)(M/2) exp(-m_(n+1)(M/2)M/2)`

y exige

`abs(Q_M-1)=o(X_M+Y_M)`.

Con colas `o(1)` multiplicativas respecto del primer termino excitado, la identidad
exacta queda

`1+X_M(1+o(1))=Q_M[1+Y_M(1+o(1))]`.

La condicion encuadrada implica

`X_M-Y_M=o(X_M+Y_M)`.

Como `X_M,Y_M>0`, esto equivale a `X_M/Y_M -> 1`. Tomar logaritmos da

`m_n(M)M - m_(n+1)(M/2)M/2 - log(A_n/A_(n+1)) -> 0`.

El control subexponencial separado de ambos cocientes de multiplicidad elimina el
ultimo termino al dividir por `M`; con la convergencia de gaps se obtiene
`m_(n+1)^infinity=2m_n^infinity`. La demostracion es correcta. La precision de R30
de que los errores de cola son multiplicativos relativos es esencial: un `o(1)`
aditivo absoluto podria absorber terminos exponencialmente pequenos.

La frase de R30 p. 6 "these conditions do force the limiting doubling" esta limitada
explicitamente a una identidad exacta y a todas las condiciones mostradas. No se
propaga como afirmacion sobre los operadores Yang--Mills; R30 pp. 1, 5, 8 y 13
mantiene que la derivacion impresa no establece el resultado para esos operadores.

### 2.2 Contraejemplo positivity-improving

R30 pp. 7--8 toma `A(t)=exp(-t)I+(1-exp(-t))P_2`, `a=1/3`, `b=1`,
`a_M=a+M^(-1/2)` y `b_(M/2)=b+(M/2)^(-1/2)`. Sus entradas son estrictamente
positivas y sus autovalores son `1, exp(-t)`. El factor `c_M` hace exacta la identidad
de trazas. Las multiplicidades son uno, la cola es vacia y los gaps convergen a
`a,b`, pero `b-2a=1/3`.

Recalculo independiente:

| M | `abs(Q_M-1)/exp(-M/3)` | `abs(Q_M-1)/(X_M+Y_M)` |
|---:|---:|---:|
| 16 | `1.4208485907932e-2` | `0.63367062005138` |
| 64 | `3.3538119780762e-4` | `0.99951463843301` |
| 256 | `1.1253517471926e-7` | `1.00000000000000` |
| 1024 | `1.2664165549094e-14` | `1.00000000000000` |

Por tanto satisface la condicion debil R29 y viola la condicion finita R30 justamente
donde debe. El contraejemplo y la clasificacion del claim son correctos.

### 2.3 Cierre de todos los hallazgos del dictamen R29

| Hallazgo R29 | Correccion R30 | Evidencia |
|---|---|---|
| Normalizacion respecto de escala limite insuficiente | `abs(Q_M-1)=o(X_M+Y_M)` y prueba de suficiencia | R30 p. 6 |
| Falta contraejemplo positivity-improving | familia `A(t)` con drift `M^(-1/2)` | R30 pp. 7--8 |
| Se dividia `Q_M`, no `abs(Q_M-1)` | "normalisation error" | R30 p. 7; a `M=24` da `3.18422139462688e-11`, frente a `Q_M/e^-M=2.64891221298435e10` |
| Referencia ambigua "The family above" | "original fixed-gap exact-trace family of Section 2" | R30 p. 8 |
| `A_rel` regresaba a constante implicita | "chosen explicit bound A_rel" y condicion uniforme | R30 p. 10 |
| `epsilon_(1,M)` no se fijaba como primer excitado | se ordena como maximo y cola `[3/5,1]` | R30 p. 7 |
| Deuda no propagada al scope/abstract | condicion finita, multiplicidad y cola aparecen en ambos | R30 p. 13; `SUBMISSION-ID.txt`, abstract/change note |

No se encontro una regresion de clase de afirmacion en este bloque: R30 distingue
condicion suficiente para el lema abstracto exact-trace de resultado no establecido
para los operadores pretendidos.

## 3. Ejecucion del verificador y reconstruccion

`verify_r30.py` se ejecuto sobre dos copias aisladas y byte-identicas de los nueve
objetos nucleares del paquete:

- `python verify_r30.py`: salida 0, `PYTHON_OPTIMIZE_LEVEL 0`;
- `python -O verify_r30.py`: salida 0, `PYTHON_OPTIMIZE_LEVEL 1`;
- el script no contiene instrucciones `assert`;
- ambos recorridos verificaron 25 paginas y las doce igualdades por pixel.

Una tercera copia aislada se reconstruyo con `python build_r30.py`. La salida final fue
byte-identica al objeto auditado:

`878dba7cc659477ea9172a24f9dba88498d41ba49af44cfdcb1a73baa13f6285`.

Hallazgo P1: el PDF intermedio recompilado tuvo SHA
`fe376b1192dd8d47811912f30b8ed6df08b47957a55a8c1dc209081bbe368e4d`, distinto del
intermedio congelado `6f800d...`; el ensamblado final fue, pese a ello, byte-identico.
No debe prometerse reproducibilidad byte a byte del intermedio sin corregir o
documentar esa diferencia.

## 4. Inspeccion visual y procedencia

Se renderizaron de nuevo las 25 paginas a 144 dpi y se inspeccionaron todas, con zoom
individual adicional en pp. 6--8. Resultado:

- 25/25 paginas legibles;
- ecuaciones, caja de la condicion, listas y tabla sin recortes ni solapamientos;
- no hay glifos negros/rotos ni margenes invadidos;
- no hay avisos `Overfull`, `Underfull`, referencias indefinidas ni errores en el log;
- pp. 14--17 son pixel-identicas a las cuatro paginas del PDF de procedencia;
- pp. 18--25 son pixel-identicas a las ocho paginas del v2 publico;
- la mezcla A4/Letter es intencionalmente heredada, no un fallo de ensamblado.

Las comparaciones por pixel se repitieron de forma independiente a 144 dpi: 12/12
iguales, con dimensiones coincidentes (`1191 x 1684` para procedencia y
`1224 x 1584` para v2).

## 5. Ficha de envio

La ficha activa es internamente coherente:

- accion `REPLACE VERSION`, ID `2602.0033`, categoria `Mathematical Physics`;
- titulo y autor coinciden con el objeto preservado;
- fichero y SHA del v2 publico coinciden con los objetos locales;
- abstract: 1,261 caracteres / 157 palabras;
- comments: 171 caracteres / 28 palabras;
- change note: 481 caracteres / 70 palabras;
- todo el fichero es ASCII;
- el abstract limita correctamente el alcance y no atribuye falsedad de los teoremas
  pretendidos; retira las derivaciones y llama suficiente solo al lema exact-trace
  fortalecido.

Deudas de cierre:

- el enlace GitHub inmutable esta literalmente `PENDING`;
- el orden esta literalmente `HOLD` hasta cerrar ledger/matriz de 103 papers;
- el estado aun dice que no hubo auditoria independiente;
- no hay manifiesto R30 que separe la ficha activa de
  `src/PEGAR-R29-HISTORICAL.txt`, que conserva a proposito lenguaje R29 obsoleto;
- no se comprobo contra un formulario autenticado el limite vigente de cada campo;
  solo se midieron los campos literales anteriores.

## 6. Accion minima para levantar REVIEW-PENDING

1. Crear `MANIFEST-R30.txt` con hashes, paginas, composicion, estado del intermedio y
   clasificacion explicita del fichero R29 como historico/no activo.
2. Tras commit y push, sustituir el enlace pendiente por URL GitHub inmutable.
3. Cerrar el orden global y actualizar ambos estados a `AUDITED/LISTO-LOCAL` sin tocar
   el PDF ni la fuente matematica.
4. Repetir hashes y barrido de la ficha; generar ZIP con manifiestos interno y externo
   byte-identicos y registrar SHA del ZIP.
5. Si se incluye el PDF intermedio, documentar su no determinacion binaria; de lo
   contrario, excluirlo del ZIP de envio y conservarlo solo como artefacto de build.

Hasta entonces: **NO ENVIAR**.
