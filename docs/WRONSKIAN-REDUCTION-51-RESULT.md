# (51) Conjetura Wronskian F_B y cociente

## Dictamen del ataque pre-registrado

**FAIL global; una pierna exacta cerrada y una obstrucción exacta en el
endpoint. Puntuación: 6/10, no 7+.**

La representación de convolución cierra de manera limpia
`F_B(t)>0` para todo `beta>0` y `0<t<pi`. También recupera la normalización
exacta de la barrera en la cara `beta=0`:

```text
(-4096/beta^10) W(beta,t)  ->  4 sin(t)^3.
```

Pero esos dos datos no cruzan `t=pi`. Después de retirar el cero cúbico, el
dato lateral que necesita cualquier argumento parabólico es exactamente

```text
lim_(t->pi-) [-W(beta,t)/sin(t)^3] = 4 c3(beta) Bpi(beta),
```

donde `Bpi>0` sí viene del kernel, mientras que `c3(beta)` es una suma
alternante cuya cancelación relativa conjunta con `Bpi` es
`exp(-(8-4 sqrt(2)) beta)`, con exponente límite `2.34314575...`. En el rango
numérico temprano los exponentes efectivos son `2.1068`, `2.2302`, `2.2879`:
esto reproduce y explica el `~exp(-2.1 beta)` del kill-test pre-registrado.
Una barrera que sustituya esa suma firmada por cotas absolutas pierde
precisamente el dato cuyo signo debe probar.

No se escribió Lean: todavía no existe el nuevo lema matemático global que
justificaría ese coste.

## 1. Normalización

Se usa la normalización sin el factor común `I_1(beta)^(-4)`:

```text
a_m = I_m^2 ((m-1) I_(m-1)^2 + (m+1) I_(m+1)^2),
b_m = m I_m^4,
F_A = sum_(m>=1) a_m sin(mt),
F_B = sum_(m>=1) b_m sin(mt),
W   = 2(F_A' F_B - F_A F_B').
```

El factor omitido es positivo y común, por lo que no cambia ningún signo.

## 2. Pierna de convolución: PASS para F_B

La forma de Graf/Neumann da las dos identidades desplazadas

```text
K_+(phi) = I_0(2 beta cos(phi/2))
         = sum_(m in Z) I_m(beta)^2 exp(i m phi),

K_-(phi) = I_0(2 beta sin(phi/2))
         = sum_(m in Z) (-1)^m I_m(beta)^2 exp(i m phi).
```

Por tanto, con convolución circular normalizada,

```text
P_4 = K_+ * K_+ = K_- * K_-
    = sum_(m in Z) I_m(beta)^4 exp(i m t),
F_B = -P_4'/2.
```

`K_+` es par y estrictamente decreciente en `[0,pi]`. Su representación
layer-cake es una integral de indicadores de arcos centrados. La convolución
de dos de esos indicadores es la longitud de una intersección de arcos,
no creciente con la separación y estrictamente decreciente para un conjunto
positivo de pares de niveles en cada `0<t<pi`. Integrando niveles,
`P_4'(t)<0`, luego `F_B(t)>0`. Esta prueba conserva estrictitud y no usa
cuadratura.

La forma con `sin(phi/2)` es la misma prueba desplazada por `pi`; el signo
`(-1)^m` desaparece al cuadrar los coeficientes de Fourier. Ésta es la
respuesta exacta a la primera pierna solicitada.

## 3. Cara beta=0: el ancla 4 sin^3(t) es exacta

De las series positivas de Bessel,

```text
I_1 = beta/2 + O(beta^3),       I_2 = beta^2/8 + O(beta^4),
a_1 = beta^6/128 + O(beta^8),   b_1 = beta^4/16 + O(beta^6),
a_2 = beta^6/256 + O(beta^8),   b_2 = beta^8/2048 + O(beta^10).
```

Así,

```text
c_12 = a_1 b_2 - a_2 b_1 = -beta^10/4096 + O(beta^12).
```

Los demás pares empiezan en orden superior, y la identidad trigonométrica
exacta del primer par es `T_12(t)=4 sin(t)^3`. En consecuencia

```text
W(beta,t) = -beta^10 sin(t)^3/1024 + O(beta^12),
(-4096/beta^10) W(beta,t) -> 4 sin(t)^3.
```

El script reproduce la razón contra el ancla en tres puntos de `t`: para
`beta=0.05,0.02,0.01` da respectivamente aproximadamente
`1.002294`, `1.0003667`, `1.00009167`, uniformemente en esos puntos.

## 4. El lema de endpoint que la barrera no puede omitir

Ponga `d=pi-t`. El corrimiento de índices en `a_m` da exactamente

```text
sum_(m>=1) (-1)^(m+1) m a_m = 0
```

y

```text
c3(beta) = (1/6) sum_(m>=1) (-1)^(m+1)
           m(m+1)(2m+1) I_m^2 I_(m+1)^2.
```

También

```text
Bpi(beta) = sum_(m>=1) (-1)^(m+1) m^2 I_m^4 > 0.
```

La última estrictitud tiene una representación positiva en el kernel killed
von Mises; equivale a `-F_B'(pi)>0`. Las expansiones de seno dan

```text
F_A(pi-d) = c3 d^3 + O(d^5),
F_B(pi-d) = Bpi d  + O(d^3),
W(pi-d)   = -4 c3 Bpi d^3 + O(d^5).
```

Por tanto, la desigualdad lateral que necesita la cantidad regularizada
`H=-W/sin^3(t)` es **equivalente** a `c3(beta)>0`. La prueba de `F_B>0` no
implica este signo.

Hay una forma integral exacta. Si

```text
g(u) = I_1(2 beta cos u)/2,
```

entonces `c3=(S3-S1)/24`, con las correlaciones derivadas descritas en el
manuscrito global. En la forma de medio intervalo, escribiendo
`y=2 beta sin u`, `z=2 beta cos u`, `f=I_1/2`, el integrando es

```text
J = -z^2 f'(y)f'(z) + z y^2 f'(y)f''(z) + y f(y)f'(z).
```

`J` cambia de signo para todos los valores probados (`beta=1,8,32,125`).
Así, la representación integral no convierte `c3>0` en positividad
puntual; todavía exige una comparación global de masas que retenga las dos
paridades.

## 5. Kill-test cuantitativo

Sean `c3_abs` y `Bpi_abs` las mismas sumas con valores absolutos. El cociente
que mide lo que queda después de una separación por desigualdad triangular es

```text
R_end = |c3/c3_abs| |Bpi/Bpi_abs|.
```

La corrida ligera produce:

| beta | R_end | log R_end |
|---:|---:|---:|
| 8  | 3.868681e-5 | -10.1600118 |
| 16 | 1.852176e-12 | -27.0146600 |
| 32 | 5.901146e-28 | -62.6972361 |
| 64 | 9.455451e-60 | -135.908514 |

Los exponentes secantes son `2.106831`, `2.230161`, `2.287852`, tendiendo a

```text
8 - 4 sqrt(2) = 2.3431457505...
```

El mismo script verifica a `beta=32`, `d=10^-4` que

```text
[W(pi-d)/d^3]/[-4 c3 Bpi] = 1.00000091098...
```

Ésta es la prueba de fuego: cualquier supuesto lema que entregue una cota de
orden del sobre absoluto, en vez de una cota firmada de `c3 Bpi`, ha perdido
entre 28 y 60 dígitos ya en `beta=32..64` y no distingue el teorema de su
negación.

## 6. Kill-test estructural

El vector finito `p=(2,1,0,...)` satisface

```text
sum (-1)^(m+1) m p_m = 0,
-(1/6) sum (-1)^(m+1) m^3 p_m = 1.
```

Así, reemplazar `A` por `A+h p` deja `F_B` y todo su kernel intactos, conserva
el cero cúbico de `F_A` en `pi`, y cambia `c3` por `c3+h`. Una función bump en
`beta`, con soporte alejado de cero, deja intacta incluso toda la expansión en
la cara `beta=0`. Tomando `h=-2c3(32)` se invierte el signo del endpoint.

El diagnóstico comprueba que en `beta=32` esta perturbación sigue teniendo
coeficientes `A_m>0` y cocientes `A_m/B_m` estrictamente crecientes; el tamaño
relativo es sólo `c3/A_1 = 1.2706946e-12`. Por continuidad, el bump puede
elegirse en una vecindad donde esas desigualdades estrictas sobrevivan y ser
cero fuera de ella.

Esto no es un contraejemplo a la conjetura Bessel: la perturbación no satisface
toda la estructura Bessel. Sí demuestra exactamente lo que debe distinguir
una prueba real: `F_B>0`, el ancla en `beta=0`, positividad de coeficientes y
orden de cocientes no bastan. El lema faltante debe consumir una identidad
Bessel que controle `c3` con signo.

## 7. Por qué la barrera parabólica queda bloqueada

Para aplicar un principio de máximo a `H=-W/sin^3(t)` sobre el semirectángulo
se necesitan dos piezas que las piernas propuestas no proporcionan:

1. una desigualdad de evolución escalar cerrada para `H`; al derivar en
   `beta`, los coeficientes `I_m^4` producen términos
   `I_m^3(I_(m-1)+I_(m+1))`, de modo que la ecuación de `I_0` no cierra sobre
   `W` o `H` sin nuevas correlaciones;
2. el dato lateral `H(pi,beta)=4c3(beta)Bpi(beta)>0` para todo `beta>0`.

El primer dato conocido de la cara `beta=0` no determina el segundo, como
muestra el bump anterior. Un principio fuerte estándar tampoco repara el
problema: antes de dividir, `W` tiene contacto cúbico con la frontera, por lo
que el dato normal de Hopf es cero; después de dividir, aparece exactamente
`c3`.

Existe en el repositorio una prueba exacta de `c3>0` para `beta>=125`, y el
sector pequeño se puede cubrir por dominación alternante. El intervalo
intermedio y la desigualdad global se cierran en el paper sucesor mediante
certificados de intervalos y relés de alta `beta`, no mediante las dos piernas
de este ataque. Eso es una solución global asistida por certificados, pero no
convierte la barrera parabólica propuesta en un lema analítico nuevo.

### 7.1. Endurecimiento tras la primera revisión especializada

La versión revisada despliega las cuatro cargas que la evaluación inicial
marcó como comprimidas: un lema uniforme para restos Bessel diferenciados,
la separación cuantitativa de la ventana de Laplace y sus dos colas, cotas
de las envolventes mediante productos explícitos de momentos, y un radio
continuo `rho(beta)` que controla exactamente positividad y los dos gaps de
cocientes alterados. El bump se sustituyó por uno cuyo exponente es
estrictamente cóncavo y tiene máximo global probado en `beta=R`; las regiones
pequeña, compacta y grande de `beta` se cierran por separado.

El kill-test ahora comprueba además que en `beta=32` la inversión de signo
ensayada queda dentro de ese radio con `rho/c3 = 965917182.921`. Este número
es diagnóstico y no se usa en la demostración ordinaria.

## 8. Resultado, coste y criterio de reanudación

- `F_B>0`: **PASS exacto**, coste de formalización moderado si se formaliza la
  prueba layer-cake; alternativamente `F_B=Q^3s_1` reduce el coste.
- `F_A/F_B` decreciente por la nueva barrera: **FAIL**, bloqueado exactamente
  en `c3>0` y en la falta de una evolución escalar cerrada.
- Valor científico del carril: **6/10**. Aísla el endpoint correcto y fabrica
  un kill-test reutilizable; no es una nueva solución global.
- Lean: **0 líneas nuevas**. No se autoriza fabricación hasta tener un lema
  ordinario que pruebe `c3(beta)>0` en todo `beta>0` y una desigualdad de
  evolución cerrada para `H`.
- Estimación si esos dos lemas aparecen: `800--1500` líneas Lean para el
  esqueleto algebraico y de Fourier, más una interfaz explícita para Graf,
  positividad y diferenciación Bessel; ejecución sólo en Colab según la
  gobernanza. Sin los lemas, el coste es abierto y no debe presupuestarse como
  “semanas de Lean”.

## 9. Reproducción y fuentes

Ejecutar local-light (un proceso, menos de 30 s en la corrida registrada):

```text
python scripts/wronskian_endpoint_kill_test.py --self-test-mutations
python -O scripts/wronskian_endpoint_kill_test.py --self-test-mutations
```

El script es diagnóstico multiprecisión, no aritmética de intervalos. Las
identidades exactas que diagnostica se justifican arriba y en los objetos
primarios del carril:

- NIST DLMF, §10.44(ii), fórmulas de adición de Neumann/Graf para Bessel
  modificadas: https://dlmf.nist.gov/10.44.ii
- NIST DLMF, §10.29(i), recurrencias y derivadas de `I_nu`, identificador
  10.29.1: https://dlmf.nist.gov/10.29.E1
- `ai.viXra:2607.0023v2`, paper primario del carril, que deja la conjetura
  global abierta y registra la estructura/obstrucciones:
  https://ai.vixra.org/abs/2607.0023
- `ai.viXra:2607.0089v1`, sucesor primario que reclama la clausura global por
  identidades exactas más certificados outward-rounded, con replay externo
  todavía marcado pendiente en el registro de supersesión:
  https://ai.vixra.org/abs/2607.0089

No se reclama prioridad nueva para Graf/Neumann, la positividad por convolución
ni el principio de máximo. El aporte de este objeto es el kill-test exacto que
obliga a una futura prueba analítica a pagar la cancelación de endpoint, junto
con el teorema de no-identificabilidad estructural desarrollado en
`papers/wronskian-endpoint-barrier/wronskian_endpoint_barrier.tex`.
