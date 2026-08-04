# (46) Cálculo Birkhoff–Dobrushin y muro

Estado: **cálculo + muro; la rama proyectiva volumen-uniforme queda
descartada**.  No se reclama como nueva la desigualdad aguda TV--Hilbert ni
los teoremas clásicos de Birkhoff y Dobrushin. El manuscrito asociado aísla
como contribución candidata estrecha la clasificación iff de igualdad para
kernels finitos, la ley tensorial hiperbólica y la dicotomía global/local.
No se reclama un gap uniforme por Birkhoff ni un dictamen terminal de
originalidad.

## 1. Convenciones

Sean $X,Y$ conjuntos finitos no vacíos y
$A=(a_{xy})_{x\in X,y\in Y}$ una matriz estrictamente positiva. Para
$u,v\in\mathbb R^Y_{>0}$,

\[
d_H(u,v)=\log\frac{\max_y u_y/v_y}{\min_y u_y/v_y}.
\]

Definimos

\[
\Theta(A)=\max_{x,x',y,y'}
 \frac{a_{xy}a_{x'y'}}{a_{xy'}a_{x'y}},\qquad
\Delta(A)=\log\Theta(A),
\]

y el cociente de contracción proyectivo

\[
\kappa_H(A)=\sup_{u\not\parallel v}
 \frac{d_H(Au,Av)}{d_H(u,v)}.
\]

Para un kernel de Markov $P$ sobre un conjunto finito $S$, usamos

\[
\operatorname{osc}(f)=\max_S f-\min_S f,
\qquad
\delta(P)=\frac12\max_{x,x'}\sum_y|P(x,y)-P(x',y)|.
\]

Esta $\delta$ es el coeficiente de contracción moderno. En la convención del
artículo de Dobrushin de 1956, el «coeficiente ergódico» es el solapamiento
$\alpha_{\mathrm D}=1-\delta$; cambiar de convención sin avisar invierte la
cantidad relevante.

## 2. Teorema comparativo honesto

**Teorema.** Con las convenciones anteriores:

1. **Birkhoff exacto en el cono global elegido.**

   \[
   \sup_{u,v>0}d_H(Au,Av)=\Delta(A),\qquad
   \kappa_H(A)=\tanh\!\left(\frac{\Delta(A)}4\right).
   \]

   Es una igualdad para el operador y ese cono, no solo una cota informal.

2. **Aditividad tensorial exacta.** Para matrices estrictamente positivas
   $A,B$,

   \[
   \Theta(A\otimes B)=\Theta(A)\Theta(B),\qquad
   \Delta(A\otimes B)=\Delta(A)+\Delta(B).
   \]

   En particular,

   \[
   \Delta(A^{\otimes L})=L\Delta(A),\qquad
   \kappa_H(A^{\otimes L})=
   \tanh\!\left(\frac{L\Delta(A)}4\right).
   \]

   Si $\Delta(A)>0$, esta última constante converge a $1$. Por tanto no
   existe $q<1$, independiente de $L$, que se obtenga aplicando el cálculo
   de Birkhoff al cono positivo global de $A^{\otimes L}$. Si
   $\Delta(A)=0$, $A$ tiene rango proyectivo uno y la constante es $0$; es
   el único caso no degenerado de esta familia por este cálculo.

3. **Dobrushin exacto para oscilación.**

   \[
   \operatorname{osc}(Pf)\le\delta(P)\operatorname{osc}(f),\qquad
   \delta(P)=\sup_{\operatorname{osc}(f)>0}
   \frac{\operatorname{osc}(Pf)}{\operatorname{osc}(f)}.
   \]

   Para un producto coordenado, la misma estimación se aplica a cada
   oscilación local $\operatorname{osc}_i$, sin sumar el número de sitios.
   Esto no afirma que el coeficiente de Dobrushin de $P^{\otimes L}$ para la
   **oscilación global** permanezca uniforme: en general tampoco lo hace.

4. **Ventana de interdependencia.** Sea $C=(c_{ij})\ge0$ una matriz de
   interdependencia de especificaciones de sitio único y supóngase

   \[
   \alpha:=\sup_i\sum_j c_{ij}<1.
   \]

   Entonces la serie $D=\sum_{n\ge0}C^n=(I-C)^{-1}$ está controlada con
   constantes independientes del número de sitios. Si $C_{ij}=0$ para
   $d(i,j)>1$,

   \[
   D_{ij}\le \frac{\alpha^{d(i,j)}}{1-\alpha}.
   \]

   El teorema de comparación de Dobrushin propaga linealmente el vector de
   oscilaciones locales a través de $D$. La uniformidad vive en la condición
   local $\alpha<1$, no en una métrica global sobre todo el cono tensorial.

5. **Coincidencia exacta de las constantes `tanh` del corpus.** Para el enlace
   binario

   \[
   K_J=\begin{pmatrix}e^J&e^{-J}\\e^{-J}&e^J\end{pmatrix},\qquad
   P_J=(2\cosh J)^{-1}K_J,
   \]

   se tiene

   \[
   \Delta(K_J)=4|J|,\qquad
   \kappa_H(K_J)=\tanh|J|,\qquad
   \delta(P_J)=\tanh|J|.
   \]

   Además, la condicional binaria
   $p_h(+)=\tfrac12(1+\tanh h)$ satisface

   \[
   \sup_{h\in\mathbb R}
   \|p_h-p_{h-2J}\|_{\rm TV}=\tanh J\quad(J\ge0),
   \]

   con igualdad en $h=J$. Así, `tanh |J|` es simultáneamente el cociente
   proyectivo de un enlace, el cociente exacto de oscilación de su kernel de
   Markov y la envolvente de influencia de una condicional de Ising. La
   coincidencia es exacta para esta celda binaria; no se afirma una identidad
   universal Birkhoff–Dobrushin para kernels arbitrarios.

6. **Muro.** Para $K_J^{\otimes L}$,

   \[
   \kappa_H(K_J^{\otimes L})=\tanh(L|J|)\longrightarrow1,
   \]

   mientras que el mayor módulo espectral no trivial normalizado del producto
   independiente es $\tanh|J|$ para todo $L\ge1$. El deterioro es del
   instrumento proyectivo global, no del sistema independiente. En una red
   local, Dobrushin conserva una constante uniforme solo dentro de
   $\sup_i\sum_j\tanh|J_{ij}|<1$; por ejemplo, en la celda cuadrada anisótropa,

   \[
   2\tanh|\beta|+2\tanh|\gamma|<1.
   \]

   Esta ventana es suficiente y normalmente no óptima.

### Demostración del paso nuevo de diseño

Una entrada de $A\otimes B$ es $a_{xy}b_{uv}$. Cada cociente cruzado del
producto es, exactamente, un cociente cruzado de $A$ multiplicado por uno de
$B$. Su máximo es a lo sumo $\Theta(A)\Theta(B)$, y se alcanza eligiendo por
separado los índices que maximizan cada factor. Tomar logaritmos prueba la
aditividad. Todo el muro sigue de la fórmula exacta de Birkhoff y de la
monotonía de `tanh`.

## 3. Kill-test prerregistrado y contraejemplo congelado

El test usa solo aritmética racional de la biblioteca estándar y el enlace

\[
K=\begin{pmatrix}3&1\\1&3\end{pmatrix},\qquad
P=\frac14K.
\]

Aquí $\Theta(K)=9$, $\Delta(K)=\log9$ y
$\kappa_H(K)=\delta(P)=1/2$. Para el tensor $L$, el cálculo exacto da

\[
\Theta(K^{\otimes L})=9^L,\qquad
\kappa_H(K^{\otimes L})=\frac{3^L-1}{3^L+1}\to1,
\]

pero el cociente espectral no trivial del producto sigue siendo $1/2$. El
script `scripts/killtest_birkhoff_tensor_wall.py` enumera cocientes cruzados de
forma exacta hasta $L=4$, verifica la fórmula y emite JSON. No es la prueba
del teorema; es el kill-test reproducible que congela el contraejemplo y evita
abrir una semana de formalización en la rama equivocada.

## 4. Ejemplos de saturación

1. **Birkhoff y el muro:** en $K_J$, los índices diagonales contra los
   antidiagonales realizan $e^{4|J|}$; en el tensor, las configuraciones
   constantes realizan $e^{4L|J|}$.
2. **Oscilación de Dobrushin:** para $P_J$, la función indicadora de uno de los
   dos estados realiza
   $\operatorname{osc}(P_Jf)/\operatorname{osc}(f)=\tanh|J|$.
3. **Influencia condicional:** los campos $+J$ y $-J$ realizan distancia TV
   $\tanh J$. En un modelo finito concreto, $h=J$ puede no ser un campo
   alcanzable; por eso esta igualdad hace aguda la envolvente uniforme en el
   campo, no necesariamente la matriz de interdependencia mínima del modelo.
4. **No-tensión espectral:** $K_J^{\otimes L}$ tiene espectro normalizado
   formado por productos de $1$ y $\tanh J$; el modo con un solo factor no
   trivial mantiene el módulo $\tanh|J|$ a todo volumen.

## 5. Prioridad bibliográfica

La prioridad se asigna a resultados, no a esta presentación comparativa.

- **Birkhoff (1957):** el teorema de contracción proyectiva y la igualdad
  $N(P,C)=\tanh(\Delta/4)$ ya aparecen en G. Birkhoff, *Extensions of
  Jentzsch's theorem*, Trans. AMS 85, 219–227.
  DOI: https://doi.org/10.1090/S0002-9947-1957-0087058-6 ;
  PDF AMS: https://www.ams.org/journals/tran/1957-085-01/S0002-9947-1957-0087058-6/S0002-9947-1957-0087058-6.pdf
- **Bushell (1973):** desarrollo del cociente de contracción proyectivo y de la
  métrica de Hilbert para aplicaciones positivas:
  https://doi.org/10.1112/jlms/s2-6.2.256 y
  https://doi.org/10.1007/BF00247467 .
- **Dobrushin (1956):** coeficiente ergódico de kernels de Markov como norma en
  masas de suma cero, con la fórmula de solapamiento de filas, en *Central
  Limit Theorem for Nonstationary Markov Chains I*.
  DOI: https://doi.org/10.1137/1101006 .
- **Dobrushin (1968):** especificaciones condicionales, regularidad y criterio
  de unicidad para campos aleatorios.
  DOI: https://doi.org/10.1137/1113026 ; original y traducción:
  https://www.mathnet.ru/eng/tvp839 .
- **Dobrushin (1970):** formulación general mediante distribuciones
  condicionales y base del teorema de comparación.
  DOI: https://doi.org/10.1137/1115049 .
- **Reeb--Kastoryano--Wolf (2011):** comparación general entre norma base y
  diámetro proyectivo, incluida la constante tanh.
  DOI: https://doi.org/10.1063/1.3615729 .
- **Gaubert--Qu (2015):** identificación del coeficiente de Dobrushin con la
  contracción de la seminorma de oscilación de Hopf en conos.
  DOI: https://doi.org/10.1007/s00020-014-2193-2 .
- **Cohen--Fausti (2024):** desigualdad aguda entre variación total y métrica
  de Hilbert para medidas de probabilidad, con saturación.
  arXiv: https://arxiv.org/abs/2309.02413 .

La especialización `tanh |J|` para una condicional binaria es un cálculo
elemental de Ising dentro de esta teoría clásica. No se reclama prioridad por
la aditividad tensorial: es una consecuencia inmediata de la fórmula de
cocientes cruzados. La búsqueda dirigida no encontró una fuente que enuncie
la clasificación iff completa para kernels finitos junto con la ley tensorial
y la localización exacta; eso justifica someter el paquete estrecho a auditoría,
pero no constituye autocertificación de prioridad.

## 6. Conocido, ruta del corpus y limitación

**Resultado conocido.** Birkhoff exacto, el coeficiente de Markov–Dobrushin y
el teorema de comparación/ventana de Dobrushin son clásicos. La aditividad
tensorial es algebraica.

**Ruta del corpus ya existente, pero no importada aquí.** En referencias
históricas del repositorio existen fuentes separadas para:

- la ceguera de cocientes cruzados bajo pesos a izquierda/derecha y un testigo
  $e^{4\beta L}$: `YangMills/OS/SpatialBirkhoff.lean`, blob Git
  `2b222695ce465e720893e6a5b5751cb96d4acb0d` en
  `agent/measure-nominal-scientific-test-debt`;
- la envolvente de enlace `tanh`, oscilación, matriz y resolvente Dobrushin:
  blobs `63a6b79f770f0dc430e34f2b5d8d90d95c9b9a20`,
  `0a14617b87360d29d7cd20bda4308a8ee0857236`,
  `db9cf8e65ff9560409c87cf9ee455a246d41c07f` y
  `717b7e5d78871e72ee2c3751766ccf35c960ac8d` en
  `origin/davinci/dobrushin-uniform`.

La presencia de esas fuentes históricas no se presenta como `.olean`
materializado en este worktree ni como verificación actual. No se ha ejecutado
Lean, Lake ni un oráculo en Windows. La formalización nueva y su compilación
remota se describen por separado en la sección 7.

**Ruta nueva que sí sobrevivió.** El teorema comparativo empaqueta las dos
normas sin confundirlas, prueba la aditividad exacta y localiza el mismo `tanh`
en la celda binaria.

**Ruta muerta.** Cualquier mecanismo que conserve el cono positivo global y
aplique Birkhoff directamente a $K^{\otimes L}$ queda rechazado por
$\Delta_L=L\Delta_1$. Revivirlo exige cambiar materialmente el objeto: cono
local/cociente, métrica ponderada no tensorial, coarse graining o una hipótesis
de mezcla adicional. Eso sería otro candidato y debe volver a pasar un
kill-test independiente.

**Limitación terminal.** De este documento no sale un gap volumen-uniforme por
Birkhoff, ni un resultado fuera de la ventana de Dobrushin, ni optimalidad de
esa ventana, ni consecuencia para Yang–Mills. El muro es parte del teorema.

## 7. Decisión Lean

El kill-test impide formalizar como teorema un gap proyectivo global falso,
pero no impide formalizar el cálculo honesto y su muro. Se añade
`YangMills/BirkhoffDobrushin/Wall.lean`, integrado por importación en
`YangMills.lean`. El módulo formaliza:

1. la identidad cuadrática y la condición de igualdad de extremos recíprocos;
2. la rigidez de igualdad en la cota de cuerda, también para sumas finitas con
   pesos estrictamente positivos;
3. la identidad normalizada que expresa variación total como esperanza de la
   parte positiva del cociente de verosimilitudes;
4. la desigualdad TV--Hilbert finita completa, con clasificación `iff` de la
   igualdad, y su levantamiento a kernels mediante máximos Dobrushin
   realizados;
5. la factorización de cocientes cruzados y la multiplicación de máximos
   realizados bajo producto tensorial;
6. la ley racional de adición hiperbólica del coeficiente de Birkhoff;
7. el paso finito de condicionamiento que preserva una cota de contracción
   fibra a fibra al promediar las coordenadas exteriores.

La fuente exacta de 23.744 bytes, SHA-256
`f2df04ae3b3f8f06730ab33b5d6e25673b3ae822d0727db4e925045fdf5cde65`,
se compiló en Colab Pro+ CPU/alta RAM con Lean `v4.29.0-rc6` y Mathlib
`07642720480157414db592fa85b626dafb71355b`. La pasada de paquete materializó
el `.olean` bajo `.lake/build/lib/lean/YangMills/BirkhoffDobrushin/`, SHA-256
`8196837adae2215bb3a85f92bd317531a867121672cc2629efb5af68540c8ffe`, y un
segundo archivo lo importó con salida 0. Un tercer importador comprobó
explícitamente los teoremas de comparación para probabilidades y kernels y
materializó un `.olean` con SHA-256
`caefea43e2e8a1e8676728ecfbffec4102cf89cef8297c2c5f932c8e16558209`.

El alcance verificado no se infla: siguen externos el teorema analítico de
Birkhoff--Hopf, el paso logarítmico de máximo de cocientes cruzados a diámetro
de Hilbert, la prueba Hellinger del coeficiente Dobrushin global y el teorema de
comparación para especificaciones interactuantes. La normalización
probabilística, la cota par a par, su igualdad `iff` y el levantamiento por
máximo realizado ya no están en esa lista externa. Los intentos fallidos se
conservan en el transcript. Fuente presente no equivale a verificación; aquí
la afirmación se apoya específicamente en la materialización remota del
`.olean` y en dos imports separados.
