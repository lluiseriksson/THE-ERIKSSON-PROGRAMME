# (49) Auditoría del paso fraccionario de Bessel

Fecha: 2026-08-04 (Europe/Stockholm)

Rama aislada: `codex/audit-bessel-fractional-49`

Base inspeccionada: `04f87347f3e4d46a05e77bc1c70855794e111477` (`origin/main`)

## Dictamen previo

**FAIL para fabricar el candidato 6.0 como resultado o ruta nueva.** Hay dos
razones independientes:

1. El enunciado literal «para órdenes reales `mu < nu`» sin cota inferior es
   falso. Un testigo holgado es
   `mu = -0.8`, `nu = -0.4`, `x = 10`, donde a 100 dígitos
   `rho_mu-rho_nu = 0.042682961675102858009598313311... > 0.04 = (nu-mu)/x`.
2. En el dominio que sí sostiene C4, `0 <= mu < nu`, el argumento es correcto,
   pero no es una ruta nueva: es exactamente la prueba del tramo de orden de
   Freitas--Laugesen, Lemma 10, escrita en la variable diferencia de razones.

El enunciado matemático ajustado y verdadero que la infraestructura C4 podría
formalizar es el resultado **conocido**

```text
0 <= mu < nu, 0 < x
  ==> 0 < rho_mu(x) - rho_nu(x)
      < (nu - mu) / x.
```

Este documento no autoriza fabricación Lean y no es un dictamen terminal. Es
el objeto previo congelable para una tarea externa.

## 1. Reconstrucción desde las definiciones

Sea

```text
rho_a(x) = I_(a+1)(x) / I_a(x),   delta = nu-mu > 0,
h(x) = rho_mu(x)-rho_nu(x),        b(x) = delta/x.
```

Para `a >= 0` y `x > 0`, la serie Gamma de C4 da `I_a(x) > 0`. Las
identidades de derivación/recurrencia dan

```text
rho_a' = 1 - rho_a^2 - ((2a+1)/x) rho_a.
```

Restando los dos flujos:

```text
h' = -(rho_mu+rho_nu)h - ((2mu+1)/x)h + (2delta/x)rho_nu.   (1)
```

### Toque de la barrera superior

Si `h=b=delta/x`, entonces (1) da

```text
h' = -delta(mu+nu+1)/x^2.                                  (2)
b' = -delta/x^2.
(h-b)' = -delta(mu+nu)/x^2.                                 (3)
```

Así, la fórmula del sketch es correcta **para `h'` en el toque**; no es la
derivada de la barrera. La orientación relevante es (3). Para
`0 <= mu < nu` es estrictamente negativa.

Equivalentemente, usando

```text
I_a'/I_a = rho_a + a/x,
F = b-h = (log(I_nu/I_mu))',
```

se obtiene en `F=0`

```text
F' = delta(mu+nu)/x^2 > 0.                                  (4)
```

Las ecuaciones (3) y (4) son la misma orientación con signo opuesto.

### Comportamiento en cero

Para `a > -1`, la serie da

```text
rho_a(x) = x/(2(a+1))
  * (1 - x^2/(4(a+1)(a+2)) + O(x^4)).
```

Luego

```text
h(x) = delta*x/(2(mu+1)(nu+1)) + O(x^3) > 0,
h(x)-b(x) -> -infinity
```

cuando `x -> 0+` en el dominio no negativo.

### Primer toque y estrictitud

- Para la desigualdad inferior, si `h` tuviera un primer cero tras el tramo
  positivo inicial, tendría derivada no positiva allí. Pero (1), en `h=0`, da
  `h'=2delta*rho_nu/x > 0`. Contradicción. No hay toque ni tangencia.
- Para la superior, `h-b<0` cerca de cero. En un primer cero tendría derivada
  no negativa; (3) da una derivada estrictamente negativa. Contradicción. No
  hay toque ni tangencia.

La continuidad y diferenciabilidad necesarias están incluidas en los
`HasDerivAt` de C4. El argumento de primer toque debe formalizar el ínfimo de
un conjunto cerrado o, de modo equivalente, el argumento local de pendientes
que ya usa `besselPsiReal_gt`.

### Comportamiento en infinito y dominio máximo visible

La expansión primaria usada en Segura 2021 implica

```text
rho_a(x) = 1 - (a+1/2)/x + (4a^2-1)/(8x^2) + O(x^-3),
h(x) = delta/x - delta(mu+nu)/(2x^2) + O(x^-3).
```

Esto confirma la saturación asintótica en el dominio no negativo y explica el
fallo literal: si `mu+nu<0`, la diferencia queda **por encima** de la barrera
para todo `x` suficientemente grande. El criterio de contacto también cambia
de orientación. La prueba transparente por dos flujos funciona, con
positividad de las series, en el dominio más amplio
`mu,nu>-1` y `mu+nu>0`; C4 está deliberadamente restringido a `mu,nu>=0`.
El borde `mu+nu=0` no queda certificado por la orientación estricta (3).

## 2. Ataques numéricos independientes

Se ejecutó `scripts/audit49_fractional_bessel.py` con `mpmath`, no con la
malla de 392 puntos ni con el recurrence/arb de C4.

- 800 casos log-uniformes, semilla `490060`, 70 dígitos.
- `mu` entre el endpoint exacto 0 y escalas hasta `10^3`; separaciones entre
  `10^-12` y `10^2`; `x` entre `10^-10` y `10^7`.
- Se forzaron órdenes casi coincidentes, `mu=0`, órdenes grandes y ambos
  extremos de `x`.
- Resultado diagnóstico: 800/800 respetaron ambas desigualdades en
  `0<=mu<nu`. El menor slack superior relativo observado fue
  `2.60223531138181244701035e-16`, en el régimen asintóticamente saturado.
- Esto no es prueba. La prueba es el cálculo de primer toque anterior.

Testigo adversarial fuera del dominio correcto, recalculado a 100 dígitos:

```text
mu       = -0.8
nu       = -0.4
x        = 10
rho_mu   = 1.03217918945950159269745024563030141111223375493372707594318
rho_nu   = 0.989496227784398734687851932319259753890789980096085294690031
difference = 0.0426829616751028580095983133110416572214437748376417812531508
barrier    = 0.04
excess     = 0.0026829616751028580095983133110416572214437748376417812531508
```

## 3. Prioridad: enunciado conocido y ruta no nueva

### Freitas--Laugesen, Lemma 10

Fuente primaria: P. Freitas y R. S. Laugesen, *From Neumann to Steklov and
beyond, via Robin: the Weinberger way*, Amer. J. Math. 143 (2021), 969--994,
DOI `10.1353/ajm.2021.0024`, arXiv `1810.07461`.

Lemma 10 afirma que, para cada `r>0`, `r I_nu'(r)/I_nu(r)` es estrictamente
creciente en `nu>=0`. Por la identidad logarítmica, esto es exactamente la
desigualdad superior fraccionaria.

Más importante para la prioridad de ruta: las pp. 20--21 no prueban esa parte
mediante ceros. Para `delta>0`:

1. fijan positividad cerca de cero con el término líder de la serie;
2. consideran `F=(log(I_(nu+delta)/I_nu))'`;
3. prueban `F=0 ==> F''_log = F'>0` sustituyendo la ecuación modificada de
   Bessel;
4. el signo se reduce literalmente a `nu^2 < (nu+delta)^2`.

Tras poner `mu=nu` y `nu=nu+delta`, ésta es (4). La barrera de dos razones no
es una ruta bibliográficamente nueva, sino una conjugación algebraica de la
prueba publicada.

### Segura 2021

Fuente primaria: J. Segura, *Monotonicity properties for ratios and products
of modified Bessel functions and sharp trigonometric bounds*, Results Math.
76 (2021), art. 221, DOI `10.1007/s00025-021-01531-1`, arXiv `2105.02524`.

Segura desarrolla sistemáticamente nullclines Riccati y primeros cruces.
Su Theorem 6(1) establece, para orden fijo `nu>=0`, que
`x I_nu'/I_nu` y el doble cociente
`I_(nu-1) I_(nu+1)/I_nu^2` son crecientes en `x`. No es el enunciado de orden
arbitrario de Freitas--Laugesen, pero sí elimina cualquier presentación de la
técnica cualitativa Riccati/primer cruce como novedosa en general.

### Desigualdad inferior

La monotonía de `nu -> I_(nu+1)(x)/I_nu(x)` es una consecuencia clásica de
la log-concavidad en el orden/Turán. En particular, Baricz registra que
`nu -> I_(nu+alpha)(x)/I_nu(x)` decrece para `alpha in (0,2]` y `nu>-1`:
A. Baricz, *Bounds for Turánians of modified Bessel functions*, Expo. Math.
33 (2015), 223--251, DOI `10.1016/j.exmath.2014.07.001`, arXiv `1202.4853`.

Conclusión de prioridad: el enunciado completo es conocido; el tramo superior
y la orientación de contacto propuesta ya están en Freitas--Laugesen. No
queda una ruta nueva que justifique el candidato 6.0.

## 4. Corrección exacta requerida en `bessel-amos-fh`

El cuerpo publicado congelado está en
`papers/bessel-amos-fh/bessel_amos_fh.tex`, commit de última modificación
`eab88b225564e7edeaaa561ade74c9d5f1745890`.

Las afirmaciones que deben corregirse son:

1. Resumen, líneas 43--48: atribuye la monotonía continua a Lemma 10, pero
   describe su prueba como basada en Mittag--Leffler/ceros y dice que no hace
   afirmación elemental fraccionaria. La parte en el orden de Lemma 10 usa en
   realidad serie en cero + primer toque + ecuación de Bessel.
2. Remark de alcance, líneas 108--127, especialmente 115--119: «does not
   recover this» y «does not follow from our method». Es falso si «method»
   incluye el argumento Riccati/primer toque ahora propuesto; la prueba está
   además ya en Freitas--Laugesen.
3. El mismo remark, líneas 124--127: la afirmación de necesidad de cotas
   bilaterales uniformes hasta `O(x^-2)` es falsa como necesidad de prueba.
   El primer toque evita esas cotas.
4. Acknowledgements, líneas 472--478: «what is new here is the proof route» y
   que el argumento elemental «closes ... only» requieren calificación. La
   ruta unitaria recurrence--Amos sí sigue siendo distinta, pero no puede
   usarse para negar una prueba elemental fraccionaria ya publicada.
5. `papers/bessel-amos-fh/README.md`, bloque «Status and honest scope», debe
   reflejar la misma distinción.

La corrección factual mínima es separar dos frases: (a) el telescopado del
argumento recurrence--Amos de paso unitario no produce por sí solo pasos
fraccionarios; (b) la desigualdad fraccionaria ya posee en Freitas--Laugesen
una prueba elemental de primer toque basada en la ecuación de Bessel. No debe
presentarse el cambio de variables a dos flujos como novedad.

## 5. Dependencias Lean C4 existentes y huecos

No se ejecutaron Lean, Lake ni oráculos. Tampoco existe `.lake` materializada
en este worktree. Fuente presente no se cuenta como `.olean` ni como
verificación. Pin observado: `leanprover/lean4:v4.29.0-rc6`, Mathlib
`07642720480157414db592fa85b626dafb71355b`.

Dependencias existentes reutilizables:

- `AmosClosure.BesselRealInterface`
  - `besselIReal`, `besselIReal_pos`;
  - serie `besselRealTerm`, sumabilidad y recurrencia
    `besselIReal_recurrence`.
- `AmosClosure.BesselRealDeriv`
  - `besselIReal_hasDerivAt`;
  - `besselIReal_deriv_identity`;
  - `besselIReal_log_hasDerivAt`.
- `AmosClosure.RiccatiReal`
  - `riccatiQReal`, `besselRatioReal`;
  - `besselRatioReal_pos`;
  - `besselRatioReal_hasDerivAt`.
- Patrones topológicos ya compilados históricamente en fuente:
  `besselPsiReal_gt` (`AmosBarrierReal.lean`) contiene el conjunto cerrado,
  `sInf`, continuidad lateral y contradicción de pendiente de primer toque.
- Herramientas de zona/serie potencialmente útiles:
  `besselRealTerm_zero_lt_besselIReal`, `besselIReal_mul_le`,
  `real_zone_ratio_uniform`, `real_zone_coefficient_bound`.

Huecos que **no** son teoremas C4 existentes:

- un seed formal para orden arbitrario cerca de `x=0` (o una expansión
  asintótica suficiente) tanto para `rho_mu>rho_nu` como para `F>0`;
- el teorema de primer toque entre dos órdenes;
- el endpoint público con dos órdenes reales arbitrarios.

Por prioridad, esos huecos no deben abrirse bajo etiqueta de resultado/ruta
nueva. El presente FAIL no se convierte en autorización de reparación.

## 6. Gobernanza y ataques entregados

- Trabajo realizado sólo en el worktree aislado indicado.
- Actualización: `git fetch`; rama creada desde `origin/main`; no rebase,
  squash ni force-push.
- Cómputo local: extracción de dos PDF primarios, render de cuatro páginas y
  un proceso Python de 0.82 s para el ataque; ningún proceso sostenido.
- Colab: no abierto; tiempo 0; no había trabajo Lean/oráculo autorizado para
  ejecutar tras el FAIL de prioridad.
- Ataques: dominio negativo, órdenes casi coincidentes, endpoint `mu=0`,
  órdenes grandes, `x` pequeño/grande, saturación asintótica y equivalencia
  literal con la prueba de Lemma 10.
- El dictamen terminal queda reservado a otra tarea sobre el objeto congelado.
