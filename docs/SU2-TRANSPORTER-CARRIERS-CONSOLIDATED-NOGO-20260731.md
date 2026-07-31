# Consolidado A/B/C/D/D+ de portadores SU(2)

**Fecha:** 2026-07-31
**Estado:** informe editorial consolidado; no es un teorema Lean ni una
certificación de una celda física.
## Alcance y lenguaje de evidencia

Este documento conserva cinco diseños ya analizados para evitar el colapso
Haar en construcciones de reflexión SU(2). No añade un diseño, no extiende los
resultados y no convierte un no-go local en una imposibilidad global.

Las etiquetas significan exactamente:

- **EXACTO:** identidad algebraica, conteo de grafo o consecuencia analítica
  bajo las hipótesis escritas.
- **VERIFICADO:** el cálculo fue contrastado por un artefacto o una sesión de
  verificación identificable. La etiqueta no significa que esté integrado en
  `YangMillsCore`.
- **INTERPRETACIÓN:** lectura de diseño o de alcance; nunca se usa como premisa
  matemática.

Cuando falta un ancla pública suficiente se escribe literalmente **registro
consolidado de análisis; pendiente de formalización**. El objeto congelado
`a66b1c7da3c7441e06864e327b5c4efa43e9c79d` se cita solo como fuente de
comparación y conserva su certificación propia; este informe no la hereda.

## Cuatro capas que no deben confundirse

1. **Topología del grafo:** calcula componentes, ciclos y
   `b1 = E - V + 1` en cada mitad conexa.
2. **Reducción gauge/Haar:** determina qué variables sobreviven después del
   promedio sobre enlaces integrados.
3. **Pertenencia al álgebra de media rodaja:** decide si un observable es
   admisible como `F` en la forma de reflexión, antes de preguntar por su
   pairing.
4. **Positividad OS:** exige una forma positiva para todo observable admisible;
   no se obtiene de un conteo de ciclos, de un 2-core no vacío ni de un solo
   testigo positivo.

En particular, `b1 >= 2` es necesario para portar dos ciclos independientes,
pero no es suficiente ni para sobrevivir a las integraciones Haar ni para
obtener positividad OS.

## Criterio de poda por 2-core

Construya el grafo bipartito de incidencia cuyos vértices de un lado son los
enlaces transversales integrados y cuyos vértices del otro son las plaquetas;
una incidencia registra que el enlace aparece en la palabra de esa plaqueta.
Si un enlace transversal tiene grado uno **y aparece exclusivamente en el
peso**, su integral Haar elimina la dependencia del factor único. Se retiran
esa hoja y el factor ya reducido, y se itera.

**Caveat inseparable:** la poda no es válida si el observable también depende
de ese enlace. Bajo la hipótesis de exclusividad anterior, un 2-core vacío
implica colapso para el diseño estudiado; sin ella, el criterio no se aplica.

El par abierto de plaquetas que comparte una arista muere por este mecanismo:
los demás enlaces transversales son hojas **siempre bajo la hipótesis local de
que el observable no los usa**. Si el observable usa cualquiera de esas hojas,
esta conclusión por 2-core queda suspendida y hace falta analizar la integral
completa.

## Diseño A — testigo que cruza el corte

**EXACTO.** Hacer depender el testigo de un enlace transversal puede impedir
la integración que, para un observable independiente, borraría el único
factor no trivial. Precisamente por esa dependencia no puede aplicarse la
poda de grado uno.

**Caveat de 2-core junto al uso:** que una hoja deje de ser podable porque el
observable la usa no demuestra supervivencia del formulario; solo invalida
esa poda concreta y obliga a evaluar el integral sin eliminar el enlace.

**EXACTO.** El mismo testigo cruza el corte y, por tanto, no pertenece al
álgebra de una mitad requerida por la forma OS. Esta es una obstrucción de
admisibilidad anterior a cualquier discusión de positividad.

**VERIFICADO.** Registro consolidado de análisis; pendiente de formalización.
No existe en `main` un objeto público que formalice simultáneamente la
dependencia transversal y el fallo de pertenencia al álgebra de media rodaja.

**INTERPRETACIÓN.** El resultado es un no-go para usar ese testigo dentro de
esa forma OS. No excluye otros observables, otras álgebras de mitad u otras
geometrías.

## Diseño B — restricción diagonal `c1 = c2`

**EXACTO.** En la orientación que agrupa los transportadores,

```text
H_E(x,c1,y,c2) = (x c1)(y c2)^-1,
H_E(x,c,y,c)   = x y^-1.
```

La diagonal recupera el pairing reducido. Pero reemplaza dos variables Haar
independientes por una sola variable común: la ley de `(c1,c2)` queda
concentrada en `c1=c2` y ya no es la medida producto original.

**VERIFICADO.** La regresión diagonal y la comparación con el caso libre están
documentadas en
`1fa29e657c43ed71a249808611bf3aea64f2b115:docs/SU2-TWO-TRANSPORTER-NOGO-20260731.md`.
El mismo artefacto advierte que no deriva físicamente el transportador común.

**INTERPRETACIÓN.** Imponer `c1=c2` es una correlación no producto; no acredita
una fijación de gauge Haar legítima. El no-go se limita a presentar esa
restricción como derivación del modelo producto.

## Diseño C — transportador relativo honesto

**EXACTO.** Si el transportador relativo se mantiene como variable Haar y se
integra, una traslación izquierda reduce el bloque del peso a una constante.
Para un observable `F` independiente del transportador se obtiene la forma de
rango uno

```text
Q(F) = Z_beta * | integral_G F dmu |^2.
```

El modo de media Haar cero desaparece. En particular, esto cubre las dos
orientaciones libres estudiadas en el artefacto de dos transportadores.

**VERIFICADO (mecanismo, no montaje C).** El mismo mecanismo de colapso por
Haar izquierda y su especialización al peso Wilson SU(2) están formalizados
para las orientaciones de dos transportadores `H_D` y `H_E` en el commit
`1fa29e657c43ed71a249808611bf3aea64f2b115`, cuya rama estaba en draft al
registrarse este informe el 2026-07-31, rutas
`YangMills/OS/TwoTransporterHaarProjection.lean` y
`docs/SU2-TWO-TRANSPORTER-NOGO-20260731.md`. El montaje específico de C
—fijar `c1=1` e integrar el transportador relativo `r`— comparte ese mecanismo,
pero no está formalizado en dicho módulo.

El estado del artefacto quedó **registrado en** el commit
`3d1a51b9a489edf70d152ad16baf808c9d30414f` del PR #41, que estaba draft y
no mergeado al registrarse este informe el 2026-07-31, ruta
`docs/SU2-TWO-TRANSPORTER-NOGO-STATUS-20260731.md`; el artefacto quedaba fuera
de `YangMillsCore`. Ese commit archiva un informe de estado/auditoría:
no verifica por sí mismo las afirmaciones que registra.

**EXACTO.** Si, en cambio, se fija el transportador relativo a la identidad,
se impone la misma correlación diagonal del diseño B.

**INTERPRETACIÓN.** Integrarlo pierde el sector no trivial; fijarlo no resuelve
la legitimidad de la medida. El no-go cubre esa dicotomía en este diseño, no
cualquier posible portador relativo.

## Diseño D — banda cerrada de dos plaquetas

**EXACTO.** Cerrar la banda elimina el patrón de hoja que lavaba el par abierto:
los enlaces transversales relevantes aparecen en las dos plaquetas y el grafo
de incidencia conserva un 2-core.

**Caveat de 2-core junto al uso:** esta conclusión solo habla de los enlaces
integrados que aparecen exclusivamente en el peso. Si el observable depende
de alguno, no se puede justificar ni la poda del par abierto ni la comparación
con la banda cerrada mediante este criterio.

**EXACTO.** Cada mitad de la banda tiene dos aristas entre dos vértices y es
conexa, luego

```text
b1 = E - V + 1 = 2 - 2 + 1 = 1.
```

Por ello cada mitad porta un solo lazo independiente. Eliminar la tercera rama
de la celda abstracta de tres ramas produce exactamente este conteo.

**VERIFICADO (informe registrado).** El cálculo topológico `b1=1` al retirar
la tercera rama aparece en el informe de auditoría **registrado en** el commit
`268d7576c4edf38ff21185901e33495bc429065f` del PR #41, que estaba draft y no
mergeado al registrarse este informe el 2026-07-31, ruta
`docs/THETA-PRISM-GEOMETRY-PREAUDIT-20260731.md`. El commit
archiva el informe, no certifica por sí mismo su contenido. El alcance del
informe es topológico; la desaparición de sectores de representación quedó
fuera de esa preauditoría.

**INTERPRETACIÓN.** Un 2-core no vacío evita este lavado por hojas, pero no
crea un segundo ciclo. El no-go es topológico para el objetivo de dos ciclos;
no es un fallo general de positividad de bandas cerradas.

## Diseño D+ — espacio cinemático `L2(G^2)` y proyector gauge

**EXACTO.** Partir de dos variables en `L2(G^2)` no determina por sí solo el
álgebra física. En el diseño estudiado, integrar los enlaces temporales
promedia la acción gauge; tras cocientar, la variable efectiva es una sola
holonomía relativa y el rango relevante es el álgebra invariante de un lazo.

**VERIFICADO.** Registro consolidado de análisis; pendiente de formalización.
No hay en `main` un teorema público que identifique este proyector y su rango
para la celda D+.

**INTERPRETACIÓN.** El no-go afecta a inferir dos ciclos físicos desde dos
coordenadas cinemáticas antes del promedio gauge. No afirma que todo espacio
`L2(G^2)` ni todo proyector gauge se reduzca a un lazo.

## Testigo `F_perp` y control de sectores de un ciclo

Para dos holonomías `U,V in SU(2)` y el carácter fundamental real `chi`, el
testigo consolidado es

```text
F_perp(U,V) = chi(U) chi(V) - (1/2) chi(U V^-1).
```

**EXACTO.** Con Haar producto normalizada y `X=UV^-1`, las tres esperanzas
condicionales que proyectan sobre los subespacios de un ciclo son

```text
E(F_perp | U)       = 0,
E(F_perp | V)       = 0,
E(F_perp | UV^-1)   = 0.
```

Las dos primeras usan `integral chi = 0`. Para la tercera, el cambio
`U=XV` preserva Haar producto y la ortogonalidad de Schur da

```text
integral_G chi(XV) chi(V) dV = (1/2) chi(X),
```

que cancela exactamente el término sustraído. Así `F_perp` es ortogonal a
`L2(U)`, `L2(V)` y `L2(UV^-1)` por separado. Además
`F_perp(1,1)=3`, de modo que no es el vector cero.

**VERIFICADO.** Una sesión adversarial read-only rederivó el coeficiente
`1/2`, las tres ortogonalidades y `||F_perp||^2=3/4`. Esa sesión declaró una
contaminación menor de procedencia y no dejó un artefacto público estable:
**registro consolidado de análisis; pendiente de formalización**.

**INTERPRETACIÓN.** La utilidad metodológica del testigo es impedir que un
pairing aparentemente positivo tome prestada toda su positividad de un sector
ya conocido de un solo ciclo. Esta separación de sectores no certifica por sí
misma una celda física ni una forma OS.

### El falso positivo `χ(y0 y1^-1)`

**EXACTO.** `χ(y0 y1^-1)` puede detectar que queda una holonomía relativa y
puede producir un modo no constante. Sin embargo, por definición pertenece
completamente a `L2(y0 y1^-1)`, uno de los tres subespacios de un ciclo que
`F_perp` elimina.

**INTERPRETACIÓN.** Ese carácter diagnostica supervivencia de un lazo relativo;
no acredita un sector genuino de dos ciclos. Usarlo como único testigo
confundiría “no constante” con “dos ciclos independientes”.

## Tabla consolidada

| Diseño | `b1` por mitad | 2-core relevante | Colapso o restricción | Alcance exacto del no-go |
|---|---:|---|---|---|
| A — testigo transversal | No fijado por este análisis | Una hoja no se poda si `F` usa el enlace; **si `F` lo usa, el criterio no se aplica** | Se evita esa eliminación, pero `F` cruza el corte | Ese testigo no pertenece al álgebra de media rodaja de la forma OS estudiada |
| B — `c1=c2` | No fijado por este análisis | No decide el caso; **la poda solo vale para enlaces exclusivos del peso** | Se impone una medida diagonal correlacionada | La diagonal recupera el pairing, pero no deriva una fijación gauge Haar del modelo producto |
| C — relativo libre/fijo | No fijado por el análisis algebraico | Si hay hojas exclusivas del peso se podan; **si el observable las usa, no se podan** | Integrado: constante/rango uno; fijo: restricción B | Dicotomía del transportador relativo estudiado, no exclusión de otros portadores |
| D — banda cerrada | `1` | No vacío para la banda; **solo bajo exclusividad del observable respecto de los enlaces integrados** | No hay lavado por hoja, pero queda un lazo | No puede portar dos ciclos independientes; no decide positividad general |
| D+ — `L2(G^2)` | `1` efectivo tras el cociente estudiado | No es el paso decisivo; **si `F` usa una hoja, la poda no se invoca** | El promedio temporal induce proyección gauge a un álgebra invariante de un lazo | Dos coordenadas cinemáticas no bastan para dos ciclos físicos en este diseño |

## Siguiente experimento admisible ya registrado

El único siguiente experimento que este informe conserva es un **piloto
abstracto con `b1=2` por mitad y 2-core no vacío**. Debe prerregistrar el grafo,
la medida producto, el proyector gauge y un testigo como `F_perp` antes de
evaluar el pairing.

**Caveat de 2-core junto al uso:** el 2-core solo controla la poda Haar de un
enlace hoja cuando el observable no depende de él. Aun con 2-core no vacío,
hay que demostrar por separado la supervivencia Haar, el rango gauge, la
pertenencia al álgebra de mitad y la positividad OS.

El antecedente quedó registrado en el commit
`268d7576c4edf38ff21185901e33495bc429065f` del PR #41, que estaba draft y no
mergeado al registrarse este informe el 2026-07-31, ruta
`docs/THETA-PRISM-GEOMETRY-PREAUDIT-20260731.md`. Allí el
informe de auditoría consigna que el conteo topológico de tres ramas da
`b1=2`. La cadena de procedencia es afirmación → informe de auditoría → commit
que lo archiva: el commit no sustituye la verificación. Ese registro no
demuestra que exista una celda física, no proporciona un puente a
`GaugeConfig` y no certifica el prisma theta.

## Fuentes y límites de procedencia

- `a66b1c7da3c7441e06864e327b5c4efa43e9c79d`, en particular
  `docs/su2-os/AUDIT.md`, `docs/su2-os/CERTIFICATION.md` y
  `YangMills/OS/SU2WilsonReflectionGeometry.lean`: carril reducido congelado,
  usado solo para convenciones y comparación.
- `1fa29e657c43ed71a249808611bf3aea64f2b115`,
  `docs/SU2-TWO-TRANSPORTER-NOGO-20260731.md` y
  `YangMills/OS/TwoTransporterHaarProjection.lean`: colapso Haar de dos
  transportadores libres; su rama estaba draft y no integrada al registrarse
  este informe el 2026-07-31.
- `3d1a51b9a489edf70d152ad16baf808c9d30414f`,
  `docs/SU2-TWO-TRANSPORTER-NOGO-STATUS-20260731.md`: estado de integración y
  límites de procedencia del artefacto anterior; registrado en el PR #41,
  que estaba draft y no mergeado el 2026-07-31. El commit archiva el informe,
  no verifica sus afirmaciones.
- `268d7576c4edf38ff21185901e33495bc429065f`,
  `docs/THETA-PRISM-GEOMETRY-PREAUDIT-20260731.md`: conteos
  `b1=2`/`b1=1`, cociente gauge abstracto y caveat de incidencia; informe de
  auditoría registrado en el PR #41, que estaba draft y no mergeado el
  2026-07-31. El commit lo archiva, no certifica por sí mismo el contenido.
- Diseños A, D+, construcción de `F_perp` y comparación conjunta A/B/C/D/D+:
  **registro consolidado de análisis; pendiente de formalización** donde no
  exista una ruta pública más fuerte citada arriba.

## No-claims

- Ningún resultado de este informe se incorpora al cierre de
  `YangMillsCore`.
- No se afirma una realización física de las celdas abstractas.
- No se deriva positividad OS completa de `b1`, del 2-core o de un testigo.
- No se amplía la certificación del SHA congelado ni se modifica su árbol.
- No se concluye nada sobre límite continuo, reconstrucción o masa física.
