# PRE-REGISTRO VINCULANTE — CRITERIO DE PASS DEL LEMA 4

**Fecha:** 2026-08-03. Este criterio se fija antes de aceptar el lema y no se modifica después de ver el resultado.

El lema 4 pasa si y solo si un lector ciego, usando únicamente este objeto, sus definiciones explícitas y las fuentes aquí citadas, puede:

1. determinar sin ambigüedad qué retículo de cuasimomentos corresponde a cada autoespacio de \(J\), tanto para \(N\) par como para \(N\) impar;
2. verificar contra la fuente citada la regla de paridad: par en NS e impar en R bajo \(\gamma<a\);
3. instanciar explícitamente \(N=1\) y \(N=2\), sin convenciones implícitas;
4. confirmar el comportamiento en \(\gamma=0\) y en el límite \(\gamma\uparrow a\), declarando qué ocurre en el borde y si el lema lo incluye o sólo lo aproxima;
5. recalcular \(\lambda_-/\lambda_+\) para \(N=2,\gamma=0\) exclusivamente desde este objeto y obtener exactamente \(\tanh\beta\).

Fallo en cualquiera de los puntos anteriores significa FAIL. Este criterio queda separado del enunciado y no se enmienda a partir del resultado.

---

# Lema 4 canónico: orientación física de los sectores NS/R

## 1. Parámetros, espacio físico y matriz de transferencia

Sean

\[
N\in\mathbb N,\quad N\ge 1,\qquad
\beta>0,\qquad \gamma\ge0,
\]

y sea \(a\in\mathbb R\) tal que

\[
\tanh a=e^{-2\beta},\qquad \gamma<a.
\]

Estas hipótesis implican \(a>0\). Se define

\[
c_{\beta,a}:=\frac{e^\beta}{\cosh a}>0,
\qquad
q:=e^{-2(a-\gamma)}=\tanh\beta\,e^{2\gamma}\in(0,1).
\]

La segunda igualdad se obtiene de

\[
e^{-2a}=\frac{1-\tanh a}{1+\tanh a}
=\frac{1-e^{-2\beta}}{1+e^{-2\beta}}
=\tanh\beta.
\]

Sea

\[
\Omega_N=\{\sigma=(\sigma_0,\ldots,\sigma_{N-1}):\sigma_j\in\{+1,-1\}\},
\qquad
\mathcal H_N=\ell^2(\Omega_N;\mathbb R).
\]

Los índices espaciales se interpretan módulo \(N\). La matriz simétrica de transferencia es

\[
S_N(\sigma,\tau)=
\exp\!\left(\frac\gamma2\sum_{j=0}^{N-1}\sigma_j\sigma_{j+1}\right)
\exp\!\left(\beta\sum_{j=0}^{N-1}\sigma_j\tau_j\right)
\exp\!\left(\frac\gamma2\sum_{j=0}^{N-1}\tau_j\tau_{j+1}\right),
\tag{1}
\]

donde \(\sigma_N=\sigma_0\) y \(\tau_N=\tau_0\). Para \(N=1\), la suma espacial contiene el autoenlace \(\sigma_0^2=1\). Para \(N=2\), contiene los dos términos \(\sigma_0\sigma_1+\sigma_1\sigma_0=2\sigma_0\sigma_1\).

En la base de espines, sean \(X_j,Y_j,Z_j\) las matrices de Pauli en el sitio \(j\), con

\[
Z_j\lvert\sigma\rangle=\sigma_j\lvert\sigma\rangle,
\qquad
X_j\lvert\sigma_0,\ldots,\sigma_j,\ldots\rangle
=\lvert\sigma_0,\ldots,-\sigma_j,\ldots\rangle.
\]

Entonces

\[
S_N=c_{\beta,a}^{N}
e^{\frac\gamma2\sum_jZ_jZ_{j+1}}
e^{a\sum_jX_j}
e^{\frac\gamma2\sum_jZ_jZ_{j+1}}.
\tag{2}
\]

El flip global y sus sectores físicos son

\[
J:=\prod_{j=0}^{N-1}X_j,
\qquad
\mathcal H_N^+:=\ker(J-I),
\qquad
\mathcal H_N^-:=\ker(J+I).
\tag{3}
\]

La matriz \(S_N\) es positiva definida: el factor temporal local tiene autovalores \(2\cosh\beta\) y \(2\sinh\beta\), ambos positivos, y los factores espaciales son diagonales, positivos e invertibles. Por ello

\[
\left\|S_N\restriction\mathcal H_N^\pm\right\|
=\lambda_{\max}\!\left(S_N\restriction\mathcal H_N^\pm\right).
\tag{4}
\]

Se abrevia

\[
\lambda_+(N):=\lambda_{\max}(S_N\restriction\mathcal H_N^+),
\qquad
\lambda_-(N):=\lambda_{\max}(S_N\restriction\mathcal H_N^-).
\]

## 2. Convención Jordan–Wigner y signo del enlace periódico

Se fija, sin libertad posterior de signo, la convención

\[
c_j=\left(\prod_{\ell=0}^{j-1}X_\ell\right)\frac{Z_j-iY_j}{2},
\qquad
c_j^\dagger=\left(\prod_{\ell=0}^{j-1}X_\ell\right)\frac{Z_j+iY_j}{2}.
\tag{5}
\]

Con esta elección,

\[
n_j:=c_j^\dagger c_j=\frac{1-X_j}{2},
\qquad
(-1)^F:=\prod_j(1-2n_j)=\prod_jX_j=J.
\tag{6}
\]

Al prolongar la cuerda a través del enlace entre \(N-1\) y \(0\), el operador local del sitio \(0\) anticomuta con \(X_0\). Por tanto, sobre el autoespacio \(J=pI\), \(p\in\{+1,-1\}\), el cierre es

\[
c_{j+N}=-p\,c_j.
\tag{7}
\]

En consecuencia:

\[
\mathcal H_N^+\;(J=+1)
\quad\longleftrightarrow\quad
c_{j+N}=-c_j
\quad\longleftrightarrow\quad
\text{antiperiódico/Neveu--Schwarz},
\tag{8}
\]

\[
\mathcal H_N^-\;(J=-1)
\quad\longleftrightarrow\quad
c_{j+N}=c_j
\quad\longleftrightarrow\quad
\text{periódico/Ramond}.
\tag{9}
\]

No aparece un factor \((-1)^N\) en (7). Tal factor aparecería con la convención distinta \(n_j=(1+X_j)/2\), que no es la convención de este objeto.

## 3. Retículos de cuasimomentos para todo \(N\)

Los retículos, siempre considerados módulo \(2\pi\), son

\[
K_{NS}(N)=
\left\{\frac{2\pi}{N}\left(m+\frac12\right):m=0,\ldots,N-1\right\},
\tag{10}
\]

\[
K_R(N)=
\left\{\frac{2\pi m}{N}:m=0,\ldots,N-1\right\}.
\tag{11}
\]

Por (8)--(11), para todo \(N\ge1\), par o impar,

\[
\boxed{\mathcal H_N^+\longleftrightarrow K_{NS}(N)},
\qquad
\boxed{\mathcal H_N^-\longleftrightarrow K_R(N)}.
\tag{12}
\]

Los modos autoconjugados bajo \(k\mapsto-k\) son:

\[
\begin{array}{c|c|c}
&K_R(N)&K_{NS}(N)\\ \hline
N\ \text{par}&0,\pi&\text{ninguno}\\
N\ \text{impar}&0&\pi
\end{array}
\tag{13}
\]

En particular,

\[
K_R(1)=\{0\},\qquad K_{NS}(1)=\{\pi\},
\tag{14}
\]

\[
K_R(2)=\{0,\pi\},\qquad
K_{NS}(2)=\left\{\frac\pi2,\frac{3\pi}2\right\}.
\tag{15}
\]

## 4. Dispersión, orientación y regla de paridad

Para cada cuasimomento se define \(\varepsilon(k)\ge0\) por

\[
\cosh\varepsilon(k)
=\cosh(2a)\cosh(2\gamma)
-\sinh(2a)\sinh(2\gamma)\cos k.
\tag{16}
\]

En la región \(0\le\gamma<a\),

\[
\varepsilon(0)=2(a-\gamma)>0,
\qquad
\varepsilon(\pi)=2(a+\gamma)>0.
\tag{17}
\]

Las transformaciones de Bogoliubov de los pares \(k,-k\) son pares en los operadores fermiónicos y conservan \((-1)^F\). En los modos autoconjugados, las masas firmadas son

\[
m_0=2(a-\gamma),
\qquad
m_\pi=2(a+\gamma).
\tag{18}
\]

Ambas son positivas bajo \(\gamma<a\). No se efectúa, por tanto, ningún intercambio creación--aniquilación en esos modos. La paridad cuasiparticular coincide con \((-1)^F=J\), independientemente de la paridad de \(N\). Tras complejificar los espacios reales,

\[
\boxed{
\mathcal H_N^+\otimes_\mathbb R\mathbb C
\simeq
\Lambda^{\mathrm{par}}\mathbb C^{K_{NS}(N)}},
\tag{19}
\]

\[
\boxed{
\mathcal H_N^-\otimes_\mathbb R\mathbb C
\simeq
\Lambda^{\mathrm{impar}}\mathbb C^{K_R(N)}}.
\tag{20}
\]

Equivalente en la notación de signos de los autovalores espinoriales:

\[
\#\{k:s_k=-1\}\equiv0\pmod2
\quad\text{en NS},
\tag{21}
\]

\[
\#\{k:s_k=-1\}\equiv1\pmod2
\quad\text{en R cuando }\gamma<a.
\tag{22}
\]

La regla (21)--(22) es la regla sectorial de Bugrij--Lisovyy, ecuaciones (33)--(34): NS tiene un número par de signos menos en ambas fases; R tiene un número impar en la fase paramagnética y un número par en la ferromagnética.

## 5. Enunciado del borde espectral

Se definen los valores de vacío formal

\[
F_{NS}(N)=c_{\beta,a}^{N}
\exp\!\left(\frac12\sum_{k\in K_{NS}(N)}\varepsilon(k)\right),
\tag{23}
\]

\[
F_R(N)=c_{\beta,a}^{N}
\exp\!\left(\frac12\sum_{k\in K_R(N)}\varepsilon(k)\right),
\tag{24}
\]

y

\[
R_N^{\mathrm{formal}}:=\frac{F_R(N)}{F_{NS}(N)}.
\tag{25}
\]

Un signo menos u ocupación del modo \(k\) multiplica el valor formal por \(e^{-\varepsilon(k)}\). El vacío NS tiene cero signos menos y es físico. El vacío R formal también tiene cero signos menos, pero queda excluido de \(\mathcal H_N^-\) por (22).

Como \(0\in K_R(N)\) y \(\varepsilon(k)\ge\varepsilon(0)\), el mayor estado R físicamente permitido contiene exactamente un signo menos en un modo de energía mínima. Por tanto,

\[
\boxed{\lambda_+(N)=F_{NS}(N)},
\tag{26}
\]

\[
\boxed{\lambda_-(N)=F_R(N)e^{-\varepsilon(0)}}.
\tag{27}
\]

En particular,

\[
\boxed{
\frac{\lambda_-(N)}{\lambda_+(N)}
=e^{-\varepsilon(0)}R_N^{\mathrm{formal}}
=qR_N^{\mathrm{formal}}}.
\tag{28}
\]

El factor \(q=e^{-\varepsilon(0)}\) es el coste de imponer la paridad física impar dentro del sector R. No forma parte de \(R_N^{\mathrm{formal}}\), que compara los dos valores auxiliares de cero ocupaciones antes de la proyección física.

Si \(\gamma>0\), \(\varepsilon(k)\) tiene mínimo estricto en \(k=0\), y el borde de \(\mathcal H_N^-\) es simple. Si \(\gamma=0\), todos los modos tienen la misma energía y la multiplicidad del borde impar es \(N\).

Este enunciado identifica solamente el máximo autovalor permitido y su multiplicidad. No afirma ni necesita una enumeración de los restantes \(2^{N-1}-1\) autovalores de cada bloque.

## 6. Instanciación completa de \(N=1\)

Para \(N=1\), el enlace espacial es el escalar \(e^\gamma\), y

\[
S_1=e^\gamma
\begin{pmatrix}e^\beta&e^{-\beta}\\e^{-\beta}&e^\beta\end{pmatrix}.
\tag{29}
\]

Como \(J=X\), sus autovalores físicos son

\[
\lambda_+(1)=c_{\beta,a}e^{a+\gamma},
\qquad
\lambda_-(1)=c_{\beta,a}e^{-a+\gamma}.
\tag{30}
\]

Por (14), (16) y (17),

\[
F_{NS}(1)=c_{\beta,a}e^{\varepsilon(\pi)/2}
=c_{\beta,a}e^{a+\gamma}=\lambda_+(1),
\tag{31}
\]

\[
F_R(1)=c_{\beta,a}e^{\varepsilon(0)/2}
=c_{\beta,a}e^{a-\gamma}.
\tag{32}
\]

El valor (32) es formal y tiene paridad equivocada. La única ocupación R permitida da

\[
F_R(1)e^{-\varepsilon(0)}
=c_{\beta,a}e^{-a+\gamma}
=\lambda_-(1).
\tag{33}
\]

Así,

\[
R_1^{\mathrm{formal}}=e^{-2\gamma},
\qquad
qR_1^{\mathrm{formal}}=e^{-2a}=\tanh\beta
=\frac{\lambda_-(1)}{\lambda_+(1)}.
\tag{34}
\]

## 7. Instanciación completa de \(N=2\) para \(0\le\gamma<a\)

Para \(N=2\), el peso espacial de (1) contiene \(2\sigma_0\sigma_1\). Se usan las bases ortonormales

\[
e_1=\frac{|++\rangle+|--\rangle}{\sqrt2},\qquad
e_2=\frac{|+-\rangle+|-+\rangle}{\sqrt2}
\]

de \(\mathcal H_2^+\), y

\[
o_1=\frac{|++\rangle-|--\rangle}{\sqrt2},\qquad
o_2=\frac{|+-\rangle-|-+\rangle}{\sqrt2}
\]

de \(\mathcal H_2^-\). Abreviemos

\[
C_\beta:=\cosh(2\beta),\qquad D_\beta:=\sinh(2\beta)>0.
\]

La ecuación (1) da, por ejemplo,

\[
S_2(++ ,++)\pm S_2(++ ,--)
=e^{2\gamma}(e^{2\beta}\pm e^{-2\beta}),
\]

y

\[
S_2(++ ,+-)\pm S_2(++ ,-+)=1\pm1.
\]

Las otras entradas se obtienen intercambiando \(e^{2\gamma}\) y \(e^{-2\gamma}\). Por tanto, sin usar (26)--(28), las dos restricciones físicas son

\[
S_2\restriction\mathcal H_2^+
=2\begin{pmatrix}
e^{2\gamma}C_\beta&1\\
1&e^{-2\gamma}C_\beta
\end{pmatrix}_{(e_1,e_2)},
\qquad
S_2\restriction\mathcal H_2^-
=2D_\beta
\begin{pmatrix}
e^{2\gamma}&0\\
0&e^{-2\gamma}
\end{pmatrix}_{(o_1,o_2)}.
\tag{35}
\]

Sea

\[
\Delta_{\beta,\gamma}
:=\sqrt{1+C_\beta^2\sinh^2(2\gamma)}.
\]

La diagonalización directa de (35) da

\[
\lambda_+(2)
=2\bigl(C_\beta\cosh(2\gamma)+\Delta_{\beta,\gamma}\bigr),
\qquad
\lambda_-(2)=2D_\beta e^{2\gamma},
\]

y, en consecuencia,

\[
\frac{\lambda_-(2)}{\lambda_+(2)}
=\frac{D_\beta e^{2\gamma}}
{C_\beta\cosh(2\gamma)+\Delta_{\beta,\gamma}}.
\tag{36}
\]

El autovalor \(\lambda_+(2)\) es simple para todo \(\gamma\ge0\). El autovalor \(\lambda_-(2)\) es simple cuando \(0<\gamma<a\); cuando \(\gamma=0\), los dos autovalores del bloque impar coinciden y su multiplicidad es dos.

Relacionamos ahora (36) con las definiciones formales, no con el borde general. La relación \(\tanh a=e^{-2\beta}\) implica, por álgebra hiperbólica,

\[
d_{\beta,a}:=c_{\beta,a}^{2}=2D_\beta,\qquad
\sinh(2a)=\frac1{D_\beta},\qquad
\cosh(2a)=\frac{C_\beta}{D_\beta}.
\]

Los retículos de (15) dan

\[
\varepsilon(0)=2(a-\gamma),\qquad
\varepsilon(\pi)=2(a+\gamma),
\]

y un mismo valor

\[
\varepsilon_A:=\varepsilon(\pi/2)=\varepsilon(3\pi/2),
\qquad
\cosh\varepsilon_A=\frac{C_\beta}{D_\beta}\cosh(2\gamma).
\]

Además,

\[
D_\beta\sinh\varepsilon_A
=\sqrt{C_\beta^2\cosh^2(2\gamma)-D_\beta^2}
=\Delta_{\beta,\gamma},
\]

donde se usó \(C_\beta^2-D_\beta^2=1\). Por ello, directamente desde (23)--(25),

\[
F_{NS}(2)
=d_{\beta,a}e^{\varepsilon_A}
=2\bigl(C_\beta\cosh(2\gamma)+\Delta_{\beta,\gamma}\bigr)
=\lambda_+(2),
\]

\[
F_R(2)e^{-\varepsilon(0)}
=d_{\beta,a}e^{2a}e^{-2(a-\gamma)}
=2D_\beta e^{2\gamma}
=\lambda_-(2).
\]

Así, la diagonalización independiente satisface

\[
\frac{\lambda_-(2)}{\lambda_+(2)}
=e^{2\gamma-\varepsilon_A}
=e^{-2(a-\gamma)}e^{2a-\varepsilon_A}
=qR_2^{\mathrm{formal}}.
\tag{37}
\]

En la especialización \(\gamma=0\),

\[
\Delta_{\beta,0}=1,\qquad
\varepsilon_A=2a,\qquad
R_2^{\mathrm{formal}}=1,
\]

y (36) se reduce, sin usar el lema general, a

\[
\frac{\lambda_-(2)}{\lambda_+(2)}
=\frac{\sinh(2\beta)}{\cosh(2\beta)+1}
=\tanh\beta.
\tag{38}
\]

En este punto el borde impar tiene multiplicidad dos, correspondiente a los dos modos periódicos \(0,\pi\). El punto \(\gamma=a\) no pertenece a esta sección ni al lema: las fórmulas anteriores sólo se afirman bajo \(0\le\gamma<a\), aunque admitan un límite cuando \(\gamma\uparrow a\).

## 8. Cara \(\gamma=0\) y borde crítico \(\gamma=a\)

La cara \(\gamma=0\) está incluida en el lema porque satisface \(0\le\gamma<a\). En ella,

\[
\varepsilon(k)=2a\quad\text{para todo }k,
\qquad
F_R(N)=F_{NS}(N),
\qquad
R_N^{\mathrm{formal}}=1,
\tag{39}
\]

y

\[
\frac{\lambda_-(N)}{\lambda_+(N)}=e^{-2a}=\tanh\beta.
\tag{40}
\]

Cuando \(\gamma\uparrow a\) desde la región paramagnética,

\[
\varepsilon(0)=2(a-\gamma)\downarrow0,
\qquad
q=e^{-\varepsilon(0)}\uparrow1.
\tag{41}
\]

El punto crítico \(\gamma=a\) no está incluido: contradice la hipótesis estricta \(\gamma<a\). En el punto crítico, el modo R de \(k=0\) tiene energía cero. El estado R de cero ocupaciones y el estado con el modo \(k=0\) ocupado tienen el mismo valor de transferencia, aunque paridades opuestas; la polarización positiva del lift deja de ser única. La identidad (28) tiene un límite desde abajo, con factor \(q\to1\), pero este lema no afirma la correspondencia de polarización ni una desigualdad estricta en \(\gamma=a\).

## 9. Convenciones comparadas y procedencia de cada afirmación

### Definiciones tomadas del repositorio

Se usa el repositorio `lluiseriksson/THE-ERIKSSON-PROGRAMME`, SHA exacto

`1470b4e91b582b043a225957a112d94b9a6226c0`.

1. `YangMills/OS/SpatialRing.lean`: `flipCfg`, `flipObs`, `IsFlipEven`, `IsFlipOdd`, la conmutación del operador con el flip y los sectores físicos.
2. `YangMills/OS/PerronKernel.lean`: `spatialWeightRing`.
3. `YangMills/OS/PerronGap.lean`: `symWeighted`.
4. `YangMills/OS/SpatialExtent.lean`: `spatialKernel`.
5. `YangMills/OS/SpatialDualBond.lean`: `z2Bond_dual_factorization`, `spatialKernel_dual_factorization`, `spatialWeightRing_eq_exp_ringBondSum` y `symWeighted_ring_dual_factorization`.
6. `YangMills/OS/SpatialVacuum.lean` y la parte escalar final de `YangMills/OS/SpatialRing.lean`: infraestructura del cociente formal periódico/antiperiódico. Este objeto no usa esa infraestructura como prueba de la identificación física.

### Resultados bibliográficos citados

1. Bruria Kaufman, “Crystal Statistics. II. Partition Function Evaluated by Spinor Analysis”, *Physical Review* **76** (1949), 1232–1243, DOI `10.1103/PhysRev.76.1232`. Se usa como fuente original de que la matriz de transferencia se trata como un elemento de una representación spinorial y de que sus autovalores se controlan mediante la rotación inducida. No se usa Kaufman como única fuente del signo de orientación del lift.

2. T. D. Schultz, D. C. Mattis y E. H. Lieb, “Two-Dimensional Ising Model as a Soluble Problem of Many Fermions”, *Reviews of Modern Physics* **36** (1964), 856–871, DOI `10.1103/RevModPhys.36.856`. Se usan las ecuaciones (3.9), (3.12a), (3.12b), (3.13), (3.17a), (3.17b) y el texto inmediatamente posterior a (3.13): los estados físicos pares proceden del operador antíciclico y los impares del cíclico; los estados de paridad contraria se descartan. SML supone tamaño par al escribir (3.17); las afirmaciones para tamaño impar de este objeto no se atribuyen a esa suposición.

3. A. I. Bugrij y O. Lisovyy, “Correlation function of the two-dimensional Ising model on a finite lattice. II”, arXiv:`0708.3643` [nlin.SI] (2007), especialmente ecuaciones (33)–(34) y el párrafo que las sigue. Se usan sus retículos NS/R y la regla: número par de signos menos en NS en ambas fases; número impar en R en la fase paramagnética y par en la fase ferromagnética.

### Derivaciones contenidas en este objeto

Las ecuaciones (5)--(9), incluidas \((-1)^F=J\) y \(c_{j+N}=-Jc_j\), se derivan de la convención Jordan--Wigner impresa y de las definiciones del repositorio. También se derivan aquí la independencia respecto de la paridad de \(N\), la ubicación de \(0,\pi\), la orientación bajo \(\gamma<a\), las instanciaciones \(N=1,2\), las multiplicidades del borde y la separación entre \(q\) y \(R_N^{\mathrm{formal}}\).

### Convenciones fijadas, no resultados externos

Los nombres “NS” y “R” significan, respectivamente, antiperiódico y periódico según (8)--(11). La elección local (5) fija \((-1)^F=J\). El lift global se toma con el signo positivo determinado por la positividad de \(S_N\) y por \(c_{\beta,a}^{N}>0\). No queda en este objeto una convención sectorial o de signo sin fijar.

---

## Lista cerrada de dependencias del objeto

El objeto depende únicamente de:

1. las definiciones y ecuaciones (1)--(25) escritas en este mismo texto;
2. los seis ficheros del repositorio enumerados en la sección 9, en el SHA fijado;
3. Kaufman (1949), DOI `10.1103/PhysRev.76.1232`;
4. Schultz–Mattis–Lieb (1964), DOI `10.1103/RevModPhys.36.856`, ecuaciones enumeradas en la sección 9;
5. Bugrij–Lisovyy, arXiv:`0708.3643`, ecuaciones (33)--(34) y su párrafo de reglas de selección;
6. álgebra matricial finita, relaciones CAR y las identidades hiperbólicas demostradas explícitamente arriba.

No se incorpora como premisa prosa del carril, resultados numéricos, una clasificación completa de B4 ni el resultado escalar como sustituto de la identificación sectorial.

## Estado del objeto

Este texto constituye la versión congelada del enunciado matemático ordinario del lema 4 y de sus convenciones. Su aceptación o rechazo no forma parte de este objeto.
