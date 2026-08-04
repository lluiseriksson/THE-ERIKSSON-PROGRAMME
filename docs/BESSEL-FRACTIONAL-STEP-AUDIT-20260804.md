# (49) Auditoría del paso fraccionario de Bessel

Fecha: 2026-08-04 (Europe/Stockholm)

Rama aislada: `codex/audit-bessel-fractional-49`

## Dictamen

**FAIL para el candidato 6.0 literal y FAIL para fabricación como teorema
analítico nuevo de nivel +6. PASS únicamente como nota de síntesis,
formalización y prueba alternativa.**

El enunciado sin restricciones de orden es falso. Un testigo holgado es

```text
mu = -0.8, nu = -0.4, x = 10
rho_mu-rho_nu = 0.042682961675102858009598313311...
(nu-mu)/x     = 0.04
exceso        = 0.002682961675102858009598313311...
```

El enunciado exacto que sobrevivió a la reconstrucción y fue formalizado es:

```text
-1 < mu < nu:

  (forall x > 0, rho_mu(x)-rho_nu(x) < (nu-mu)/x)
      iff mu+nu >= 0,

y, si mu+nu >= 0,
  0 < rho_mu(x)-rho_nu(x) < (nu-mu)/x  para todo x>0.
```

La parte `0 <= mu < nu` y su geometría de primer contacto ya están en
Freitas--Laugesen, Lemma 10. El barrido ampliado de v8 encontró además que
Garofalo, Proposición 8.8, ya contiene el umbral negativo exacto para salto
unitario, y que el iff de salto arbitrario es un corolario corto de resultados
clásicos (fórmula de conexión, Wronskiano y expansión en infinito). Aunque no
se localizó el iff arbitrario como un único teorema publicado, su contenido
analítico no supera el umbral de novedad exigido para fabricar un paper +6.

## 1. Cálculo reconstruido

Sean

```text
rho_a(x) = I_(a+1)(x)/I_a(x),  delta = nu-mu > 0,
h = rho_mu-rho_nu,              b = delta/x,
G = h-b.
```

La serie Gamma es estrictamente positiva para `a>-1`, `x>0`. La recurrencia y
la derivada dan, en todo ese dominio,

```text
rho_a' = 1-rho_a^2-((2a+1)/x)rho_a.
```

En un toque `h=b`:

```text
h' = -delta*(mu+nu+1)/x^2,
G' = -delta*(mu+nu)/x^2.
```

La primera fórmula del sketch es correcta para `h'`; la orientación relevante
es la segunda. El ODE completo, que evita cualquier ambigüedad de contacto, es

```text
G' = -(rho_mu+rho_nu+(mu+nu+1)/x)G
     - delta*(mu+nu)/x^2.                       (1)
```

### Cero, primer toque y estrictitud

Sin invocar una expansión asintótica, dos pasos de la recurrencia producen
semillas explícitas cerca de cero. Equivalentemente, el término líder es
`rho_a(x) ~ x/(2(a+1))`. Por tanto `h>0` y `G<0` inicialmente.

- Si `h` tuviera un primer cero, el ODE restado daría
  `h'=2*delta*rho_nu/x>0`, incompatible con el cruce desde valores positivos.
- Si `mu+nu>0` y `G` tuviera un primer cero, (1) daría `G'<0`, incompatible
  con el cruce desde valores negativos.
- Si `mu+nu=0`, (1) es homogéneo. Un argumento de unicidad/Gronwall hacia
  atrás desde un supuesto cero contradice la semilla estrictamente negativa.

Así se obtienen ambas desigualdades estrictas cuando `mu+nu>=0`.

### Necesidad cuando `mu+nu<0`

La recurrencia exacta es

```text
1/rho_a = 2(a+1)/x + rho_(a+1).
```

De ella se deducen cotas elementales superior e inferior y, para `x` grande,
`rho_a>3(a+2)/(2x)`. Si se supusiera `G<0` globalmente y se pusiera
`F=-delta*(mu+nu)>0`, `H=x^2 G`, `J=H-Fx`, las mismas cotas y (1) implicarían
`J'>0` a partir de un umbral explícito. Elegir
`z=X-H(X)/F+1` fuerza `H(z)>0`, contradicción. Por tanto existe `x>0` con
`G(x)>=0`. No se usa función `K`, conexión de órdenes ni expansión en infinito.

## 2. Ataques numéricos

El script `scripts/audit49_fractional_bessel.py` usó `mpmath` con 100 dígitos,
800 puntos adversariales deterministas (semilla `490060`), separaciones de
orden hasta `10^-12` y argumentos desde `10^-10` hasta `10^7`. La malla y los
residuos son diagnóstico, nunca prueba.

- No se encontró fallo dentro de `-1<mu<nu`, `mu+nu>=0`.
- Se atacó especialmente la frontera `mu+nu=0`, donde el margen puede ser
  exponencialmente pequeño.
- El testigo literal anterior se recalculó a 100 dígitos.
- Otro punto adversarial es `mu=-0.8`, `nu=0.3`, `x=2`, que también viola la
  barrera superior con margen
  `0.07012291658572701948178010641590655268...`.

## 3. Prioridad en fuentes primarias

### Freitas--Laugesen 2021

P. Freitas y R. S. Laugesen, *From Neumann to Steklov and beyond, via
Robin: the Weinberger way*, Amer. J. Math. 143 (2021), 969--994,
DOI `10.1353/ajm.2021.0024`, arXiv `1810.07461`, Lemma 10.

Para cada `r>0`, prueba que `r I_nu'(r)/I_nu(r)` crece estrictamente en
`nu>=0`. En pp. 20--21 la parte de orden usa signo en cero, primer cero y la
ecuación diferencial; no es una prueba por ceros de Bessel. Tras el cambio de
variables, es la misma orientación de contacto. Por tanto ni el teorema no
negativo ni esa ruta pueden reclamarse como nuevos.

### Segura 2021

J. Segura, *Monotonicity properties for ratios and products of modified
Bessel functions and sharp trigonometric bounds*, Results Math. 76 (2021),
221, DOI `10.1007/s00025-021-01531-1`, arXiv `2105.02524`.

Es una fuente primaria de la metodología Riccati/nullcline y primeros cruces.
Sus resultados citados varían `x` a orden fijo y no enuncian el iff global
entre dos órdenes arbitrarios.

### Fuentes negativas y riesgo residual

- K. Hornik y B. Grün, *Generalized Amos-type bounds for modified Bessel
  function ratios*, Math. Inequal. Appl. 27 (2024),
  DOI `10.7153/mia-2024-27-55`: cotas individuales en órdenes negativos, no se
  localizó el criterio cross-order `mu+nu>=0`.
- Z.-H. Mao y J.-F. Tian, *The monotonicity of the ratio of two modified
  Lommel functions*, Results Math. 80 (2025),
  DOI `10.1007/s00025-025-02488-1`: el registro primario accesible anuncia
  corolarios para Bessel modificadas, pero el texto íntegro no fue accesible.
  Esto se registra como riesgo de prioridad, no como evidencia de novedad.
- Á. Baricz, *Bounds for Turánians of modified Bessel functions*, Expo. Math.
  33 (2015), DOI `10.1016/j.exmath.2014.07.001`, arXiv `1202.4853`: cubre la
  monotonía clásica inferior del cociente en el orden.

### Barrido ampliado v8: testigo de prioridad adverso

N. Garofalo, *Two classical properties of the Bessel quotient
`I_(nu+1)/I_nu` and their implications in PDEs*, arXiv `1810.09756`
(2018), Proposición 8.8, enuncia que `I_(a+1)/I_a` crece estrictamente en
`x` para `a>=-1/2`, mientras que para `-1<a<-1/2` primero crece y luego
decrece hacia 1. Garofalo califica el hecho como clásico y remite a la
discusión del apéndice de L. Yuan y J. D. Kalbfleisch, *On the Bessel
distribution and related problems*, Ann. Inst. Statist. Math. 52 (2000),
438--447, DOI `10.1023/A:1004152916478`.

Registros primarios exactos:

- Garofalo: `https://arxiv.org/abs/1810.09756`, PDF pp. 38--40;
- Yuan--Kalbfleisch:
  `https://www.ism.ac.jp/editsec/aism/52/438.html`;
- Hartman 1976:
  `https://www.numdam.org/item/ASNSP_1976_4_3_2_267_0/` y errata
  `https://www.numdam.org/item/ASNSP_1976_4_3_4_725_0/`;
- DLMF: `https://dlmf.nist.gov/10.27`, `/10.28` y `/10.40`.

La recurrencia muestra exactamente

```text
(rho_a)' > 0  iff  rho_a-rho_(a+1) < 1/x.
```

Por tanto Garofalo/Yuan--Kalbfleisch ya contienen la rebanada de salto
unitario del iff, incluido el umbral óptimo `2a+1=0`.

Hay un testigo aún más decisivo para el desplazamiento arbitrario. Escribiendo
`r_a=I_a'/I_a`, la cota superior equivale a `r_mu<r_nu`. Para
`mu=-a in (-1,0)`, las fórmulas DLMF 10.27.2 y 10.28.2 dan

```text
I_(-a) = I_a + (2/pi) sin(pi a) K_a,
K_a'/K_a < I_a'/I_a,
```

luego `r_(-a)<r_a`. Si `mu+nu>=0`, entonces `nu>=a`, y
Freitas--Laugesen aplica entre `a` y `nu`. Si `mu+nu<0`, DLMF
10.40.1--10.40.4 da

```text
r_mu-r_nu = (mu^2-nu^2)/(2x^2) + O(x^-3) > 0
```

para `x` suficientemente grande. Esto reconstruye el iff completo a partir
de hechos clásicos. Hartman, *Completely monotone families of solutions...*,
Ann. Scuola Norm. Sup. Pisa (1976), Teorema 1.0, ya proporciona además el
antecedente estructural de monotonía completa en el parámetro `a^2`.

Conclusión v8: no se halló una única proposición previa con la frase exacta
`mu+nu>=0`, pero la clasificación analítica es un corolario breve de fuentes
anteriores. **FAIL de prioridad para venderla como teorema nuevo +6.** Quedan
como aportaciones defendibles la síntesis explícita, la prueba alternativa
sin `K` ni asintótica y la formalización Lean completa.

## 4. Corrección exacta de `bessel-amos-fh`

La versión previa debía corregir estas afirmaciones:

1. «el paso no entero no sigue del método»: falso para el método amplio de
   ecuación diferencial/primer contacto; sólo el telescopado recurrence--Amos
   de paso unitario no produce por sí solo el paso fraccionario.
2. «Lemma 10 usa ceros de Bessel»: falso para la parte de monotonía en el
   orden; su prueba publicada ya contiene el primer contacto.
3. «la ruta de primer contacto es nueva»: falso por la misma fuente.
4. La extensión sin dominio de orden: falsa; debe sustituirse por
   `-1<mu<nu` y `mu+nu>=0`, con fallo existencial si `mu+nu<0`.
5. El alcance Lean anterior, que declaraba ausente la región negativa, quedó
   obsoleto tras la formalización actual.
6. «La frontera negativa óptima es una contribución candidata nueva» ya no
   es sostenible tras el barrido v8: el salto unitario es clásico y el iff
   arbitrario se deduce en pocas líneas de resultados clásicos.
7. El paper debe describirse como síntesis con prueba alternativa y
   formalización, no como descubrimiento de una clasificación analítica.

El Teorema 2 corregido dice exactamente: para `-1<mu<nu`, la desigualdad
inferior vale para todo `x>0`; la superior vale para todo `x>0` si y sólo si
`mu+nu>=0`; si la suma es negativa, falla para al menos un `x>0`.

## 5. Objeto Lean C4

Dependencias reutilizadas:

- `BesselRealInterface`: serie Gamma `besselIReal` y recurrencia base;
- `BesselRealDeriv`: derivación término a término;
- `RiccatiReal`: `besselRatioReal` y el patrón Riccati;
- `FractionalOrder`: patrón topológico de primer contacto no negativo;
- Mathlib: continuidad lateral, `sInf`, derivadas, Gronwall y álgebra de
  desigualdades.

Nuevos módulos:

- `AmosClosure/BesselNegative.lean`: positividad, sumabilidad, recurrencia,
  derivada y Riccati para `nu>-1`;
- `AmosClosure/FractionalOrderOptimal.lean`: ODE completo, semillas por
  recurrencia, monotonía estricta, frontera homogénea, obstrucción negativa,
  iff exacto y teorema bilateral.

Endpoints principales:

```text
besselRatioReal_fractional_upper_all_iff
besselRatioReal_fractional_two_sided
exists_fractional_upper_failure_of_sum_neg
```

Verificación externa de cómputo: Colab Pro+ CPU/alta RAM, Lean
`v4.29.0-rc6`, Mathlib `07642720480157414db592fa85b626dafb71355b`.
`lake build AmosClosure.FractionalOrderOptimal` terminó correctamente con
8167 tareas y `.olean` materializado. El oráculo y la raíz se registran en la
congelación final; fuente presente nunca se equipara a verificación.

## 6. Gobernanza

- Trabajo sólo en el worktree aislado; merge de `main`, nunca rebase/squash ni
  force-push.
- No se ejecutó Lean/Lake localmente.
- La sesión visible de Colab fue verificada como `lluiseriksson@gmail.com` y
  se usó CPU/alta RAM, sin GPU. Apertura aproximada 20:07, cierre y borrado
  20:38 (Europe/Stockholm), duración registrada: 31 minutos; las otras tres
  sesiones activas del owner no se tocaron.
- No se invocó Claude Code, Opus 5 ni Fable 5 porque no podía confirmarse una
  sesión visible de `masterythief@gmail.com`; no se expusieron credenciales.
- El objeto final se entrega con SHA de rama/cuerpo, bytes y hashes LF/CRLF.
- Esta mesa entrega evidencia y ataques; el dictamen terminal corresponde a
  otra tarea independiente.
