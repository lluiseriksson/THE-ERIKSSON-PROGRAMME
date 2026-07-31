# Dos transportadores SU(2) libres: no-go de proyección Haar

**Estado: DESIGN NO-GO / AUDIT PENDING.** Fecha: 2026-07-31.
Falta una auditoría independiente terminal. Este documento no hereda ni se
atribuye el resultado de auditoría del objeto congelado citado abajo.

## Alcance y niveles de evidencia

Este artefacto estudia exactamente dos orientaciones algebraicas con dos
transportadores independientes integrados contra Haar y ausentes del
observable. No deriva una geometría de plaqueta física, no amplía el carril
SU(2) congelado y no convierte una elección auxiliar en una fijación de gauge.

- **Exacto (derivación matemática):** las identidades de grupo, el testigo de
  cuaterniones y las reducciones Haar de las secciones siguientes. Las
  reducciones usan únicamente invariancia Haar izquierda normalizada, Fubini
  para funciones integrables y álgebra de la traza en SU(2).
- **Verificado ejecutablemente, alcance finito:**
  `scripts/certify_su2_two_transporter_nogo.py` comprueba mediante aritmética
  exacta en `Q(sqrt(2))` el testigo de cuaterniones y, mediante palabras libres
  reducidas, las identidades algebraicas finitas. El programa declara en su
  salida que **no** prueba las identidades integrales generales.
- **Verificado por Lean, general y Wilson SU(2) concreto:** el módulo nuevo e
  independiente `YangMills/OS/TwoTransporterHaarProjection.lean` prueba primero
  los dos colapsos para todo peso con `w(a z⁻¹ a⁻¹)=w(z)`. Después define
  localmente el peso Wilson `su2WilsonWeight`, prueba esa simetría en SU(2) y
  especializa ambos formularios cuadráticos. No importa ni edita el carril
  congelado.
- **Certificación congelada ajena a este artefacto:** el bound reducido
  `Qβ(tr) ≥ β/4` se cita al SHA de solo lectura
  `a66b1c7da3c7441e06864e327b5c4efa43e9c79d`. No se atribuye a este documento
  el PASS asociado a ese SHA.
- **División exacta de la etiqueta no-go:** Lean formaliza el colapso Wilson
  SU(2) de las orientaciones D y E. No formaliza en el mismo grafo la separación
  estricta frente a `Qβ(tr) ≥ β/4 > 0`; esa segunda mitad vive en este documento
  como comparación matemática citada al SHA congelado. La etiqueta **no-go**
  combina esas dos piezas de evidencia y no debe atribuirse solo al módulo Lean.
- **Interpretación no probada:** que el transportador común del carril reducido
  sea una fijación de gauge físicamente derivada. Nada aquí lo establece.

## Definiciones y cuantificadores

Sea `G = SU(2)` y sea `μ` la medida de Haar de probabilidad sobre `G`. Sea
`β ∈ R` y defínase

```text
wβ(g) = exp((β/2) Re tr(g)),                         g ∈ G.
```

Sea `F : G → C` un observable `μ`-integrable que no depende de `c₁` ni de
`c₂`. Para justificar todas las manipulaciones sin condiciones laterales se
puede, en particular, tomar `F` continua: `G` es compacto, `wβ` es continua y
acotada, y todos los integrandos son entonces absolutamente integrables.

Los cuatro elementos `x,y,c₁,c₂ ∈ G` son variables independientes. Cada uno
se integra contra una copia independiente de `μ`. Definimos

```text
H_D(x,c₁,y,c₂) = x c₁ y⁻¹ c₂⁻¹,
H_E(x,c₁,y,c₂) = x c₁ c₂⁻¹ y⁻¹ = (x c₁)(y c₂)⁻¹,
Zβ                = ∫_G wβ(g) dμ(g),

Q_A(F) = ∫_{G⁴} conjugate(F(x)) wβ(H_A(x,c₁,y,c₂)) F(y)
           dμ(c₂) dμ(c₁) dμ(y) dμ(x),       A ∈ {D,E}.
```

El orden escrito es iterado; por integrabilidad absoluta coincide con la
integral de producto. Como `wβ > 0` y `μ(G)=1`, `Zβ` es real y estrictamente
positivo. El kernel reducido usado para la comparación es

```text
Kβ(x,y) = wβ(x y⁻¹),
Qβ(F)   = ∫_G ∫_G conjugate(F(x)) Kβ(x,y) F(y) dμ(y) dμ(x).
```

## 1. La orientación D no pasa la regresión diagonal

Imponer `c₁=c₂=c` da

```text
H_D(x,c,y,c) = x c y⁻¹ c⁻¹.
```

En un grupo no abeliano no se puede cancelar `c` a través de `y⁻¹`. Por tanto
esta expresión no regresa, en general, a `x y⁻¹`.

El fallo tiene un testigo exacto en el modelo de cuaterniones unitarios de
`SU(2)`. Tome

```text
x = i,       y = j,       c = (1+k)/sqrt(2).
```

Los tres cuaterniones tienen norma uno. Sus inversos son
`i⁻¹=-i`, `j⁻¹=-j` y `c⁻¹=(1-k)/sqrt(2)`. Primero,

```text
x y⁻¹ = i(-j) = -k,
tr(x y⁻¹) = 2 Re(-k) = 0.
```

Para la orientación D,

```text
c(-j)c⁻¹
  = ((1+k)/sqrt(2)) (-j) ((1-k)/sqrt(2))
  = i,

H_D(i,c,j,c) = i i = -1,
tr(H_D(i,c,j,c)) = 2 Re(-1) = -2.
```

En consecuencia, los pesos exactos son

```text
wβ(x y⁻¹)        = exp((β/2)·0)    = 1,
wβ(H_D(x,c,y,c)) = exp((β/2)·(-2)) = exp(-β).
```

La regresión de holonomía falla para todo `β`; los pesos además la distinguen
cuando `β ≠ 0`.

## 2. La orientación D se proyecta al sector trivial usando solo Haar izquierda

Fije `x,y,c₁` y escriba

```text
A = x c₁ y⁻¹,
H_D(x,c₁,y,c₂) = A c₂⁻¹.
```

En la integral en `c₂`, sustituya

```text
c₂ = A z.
```

Esta es una traslación **izquierda** por `A`; por invariancia Haar izquierda,
`dμ(c₂)=dμ(z)`. Además,

```text
A c₂⁻¹ = A (A z)⁻¹ = A z⁻¹ A⁻¹.
```

La traza matricial es invariante bajo conjugación. Como `z` es unitario,
`tr(z⁻¹)=conjugate(tr(z))`, y por tanto

```text
Re tr(A z⁻¹ A⁻¹) = Re tr(z⁻¹) = Re tr(z),
wβ(A z⁻¹ A⁻¹) = wβ(z⁻¹) = wβ(z).
```

No se ha usado invariancia derecha ni invariancia de la medida bajo inversión:
las dos últimas igualdades son álgebra puntual del peso. Luego

```text
∫_G wβ(H_D(x,c₁,y,c₂)) dμ(c₂)
  = ∫_G wβ(A z⁻¹ A⁻¹) dμ(z)
  = ∫_G wβ(z) dμ(z)
  = Zβ.
```

El resultado ya no depende de `x`, `y` ni `c₁`. La copia de Haar restante
sobre `c₁` integra la constante:

```text
∫_G ∫_G wβ(H_D(x,c₁,y,c₂)) dμ(c₂)dμ(c₁)
  = ∫_G Zβ dμ(c₁)
  = Zβ.
```

Ahora `F` es independiente de ambos transportadores, de modo que

```text
Q_D(F)
  = Zβ ∫_G ∫_G conjugate(F(x)) F(y) dμ(y)dμ(x)
  = Zβ (∫_G conjugate(F(x))dμ(x)) (∫_G F(y)dμ(y))
  = Zβ conjugate(∫_G F dμ) (∫_G F dμ)
  = Zβ |∫_G F dμ|².
```

Así, una sola integración Haar libre elimina la dependencia `x-y`; la segunda
solo aporta el factor `μ(G)=1`.

## 3. La orientación E pasa la diagonal, pero tiene la misma proyección

En la diagonal,

```text
H_E(x,c,y,c) = x c c⁻¹ y⁻¹ = x y⁻¹.
```

Por tanto E sí pasa la prueba algebraica que D falla. Sin embargo, con `c₁` y
`c₂` libres e independientes, haga los dos cambios

```text
u = x c₁,       v = y c₂.
```

Ambos son traslaciones **izquierdas** sobre su propia variable de transporte,
por lo que `dμ(u)=dμ(c₁)` y `dμ(v)=dμ(c₂)`. Además,

```text
v⁻¹ = (y c₂)⁻¹ = c₂⁻¹ y⁻¹,
H_E(x,c₁,y,c₂) = u v⁻¹.
```

Para ver la constante usando todavía solo Haar izquierda, fije `u` y escriba
`v=u z`. La sustitución es una traslación izquierda, y

```text
u v⁻¹ = u (u z)⁻¹ = u z⁻¹ u⁻¹,
wβ(u z⁻¹ u⁻¹) = wβ(z⁻¹) = wβ(z).
```

Por Fubini e invariancia izquierda,

```text
∫_G ∫_G wβ(H_E(x,c₁,y,c₂)) dμ(c₂)dμ(c₁)
  = ∫_G ∫_G wβ(u v⁻¹) dμ(v)dμ(u)
  = ∫_G Zβ dμ(u)
  = Zβ.
```

Este bloque tampoco depende de `x` ni de `y`. La misma factorización exterior
produce

```text
Q_E(F) = Zβ |∫_G F dμ|².
```

La orientación y el éxito de la regresión diagonal no evitan la proyección.

## 4. Separación estricta mediante el carácter fundamental

Tome `F(U)=tr(U)`. El carácter fundamental no trivial tiene media Haar cero:

```text
∫_G tr(U) dμ(U) = 0.
```

La identidad también existe en el repositorio como
`sunHaarProb_trace_complex_integral_zero`; el carril congelado la especializa
como `su2TraceObservable_haar_mean_zero`. Aplicando las dos reducciones,

```text
Q_D(tr) = Zβ |0|² = 0,
Q_E(tr) = Zβ |0|² = 0.
```

En contraste, el carril reducido congelado prueba, para `β>0`,

```text
Qβ(tr) ≥ β/4 > 0.
```

La referencia de solo lectura es el commit
[`a66b1c7da3c7441e06864e327b5c4efa43e9c79d`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/a66b1c7da3c7441e06864e327b5c4efa43e9c79d),
en particular `docs/su2-os/SHARP-GATE.md` y los teoremas
`su2Trace_crossing_lower`, `su2OnePlaquette_trace_pairing_lower` y
`su2GaugePureCut_trace_pairing_positive_sharp`. Esta cita compara resultados;
no importa el carril, no relanza sus gates y no atribuye su PASS al presente
artefacto.

La división de evidencia es deliberada y exacta: el módulo Lean nuevo certifica
`Q_D(tr)=Q_E(tr)=0` a partir de la media Haar nula una vez suministrada esa
identidad; la desigualdad estricta del kernel reducido no está en su cierre de
imports. La afirmación de **no-go** resulta al comparar ese colapso formalizado
con `Qβ(tr)≥β/4>0`, probado únicamente en el objeto congelado citado. Esta
comparación es una derivación documental entre dos artefactos, no un theorem
Lean conjunto.

## 5. Conclusión limitada

Para las dos orientaciones especificadas, **dos transportadores independientes,
libremente Haar-integrados y ausentes del observable proyectan el formulario
cuadrático al sector trivial**:

```text
Q_D(F) = Q_E(F) = Zβ |∫_G F dμ|².
```

Por ello se pierde el modo fundamental de media cero. Ni reordenar la
orientación, ni disponer de invariancia Haar derecha, ni introducir inversión
rescata ese modo bajo estos cuantificadores. De hecho, el no-go anterior usa
solo invariancia Haar izquierda; conjugación e inversión aparecen únicamente
en identidades puntuales del peso.

El frente que sobrevive requeriría transportadores restringidos o
correlacionados, o un álgebra de observables que dependa de ellos. Eso sería un
proyecto distinto, con nuevas definiciones y obligaciones; no es una
continuación automática del carril certificado.

## APIs Haar ya existentes

El repositorio ya contiene la infraestructura relevante:

| API | Ubicación | Papel |
|---|---|---|
| `sunHaarProb` | `YangMills/P8_PhysicalGap/SUN_StateConstruction.lean` | Haar normalizada en `SU(N)` |
| `instIsProbabilityMeasureSUN` | mismo módulo | `μ(G)=1` |
| `sunHaarProb_isMulLeftInvariant` | `YangMills/ClayCore/SchurZeroMean.lean` | traslaciones izquierdas usadas en la reducción |
| `instIsHaarMeasureSUN` | `YangMills/ClayCore/SchurNormOne.lean` | instancia Haar explícita |
| `instIsMulRightInvariantSUN` | `YangMills/ClayCore/SchurNormOne.lean` | traslaciones derechas disponibles, no consumidas aquí |
| `MeasureTheory.integral_mul_left_eq_self` | Mathlib, ya consumida por varios módulos | cambio `g ↦ ag` |
| `MeasureTheory.integral_mul_right_eq_self` | Mathlib, ya consumida por `SchurNormOne` y `SchurFundamentalOrthogonality` | disponible, no necesaria aquí |
| `measurePreserving_mul_left` | Mathlib, ya consumida por `CenterInvariance` | versión de medida producto/cambio de variable |

En particular, Haar derecha no es el cuello de botella: la instancia
`instIsMulRightInvariantSUN` y el lema integral correspondiente ya están
presentes. Sin embargo, la prueba más fuerte no los consume. La obstrucción es
la independencia y la integración libre de los transportadores, combinadas
con su ausencia en `F`, no una propiedad adicional de invariancia derecha.

## Formalización Lean separada

El módulo nuevo
`YangMills/OS/TwoTransporterHaarProjection.lean` importa únicamente
`YangMills/L0_Lattice/SU2Basic.lean`, que a su vez importa Mathlib. No importa
ningún módulo `SU2WilsonReflection*`. Define `ConjugationInverseInvariant w` y
prueba, entre otros, los siguientes headlines genéricos:

```text
integral_weight_mul_inv_eq
orientationD_inner_projection
orientationD_twoTransporter_projection
orientationE_uv_projection
orientationE_twoTransporter_projection
quadraticD_eq_partition_mul_mean_sq
quadraticE_eq_partition_mul_mean_sq
```

Los dos últimos concluyen exactamente

```text
Q_A(F) = (∫w dμ) conjugate(∫F dμ) (∫F dμ),       A ∈ {D,E}.
```

La sección concreta define en el propio módulo

```text
su2WilsonWeight β g = exp((β/2) Re tr(g))
```

y cierra la descarga algebraica mediante

```text
su2_trace_conjugate_inverse
su2_trace_inv_eq
su2WilsonWeight_conjugationInverseInvariant
```

Aquí `su2_trace_inv_eq` usa `det z = 1` y la fórmula exacta de la adjugada de
una matriz `2×2`; no usa prosa como sustituto de un teorema. Los cuatro bloques
de transportadores se especializan como

```text
su2Wilson_orientationD_inner_projection
su2Wilson_orientationD_twoTransporter_projection
su2Wilson_orientationE_uv_projection
su2Wilson_orientationE_twoTransporter_projection
```

y los dos titulares concretos son

```text
su2Wilson_quadraticD_eq_partition_mul_mean_sq
su2Wilson_quadraticE_eq_partition_mul_mean_sq
```

Por tanto, para toda medida de probabilidad invariante por la izquierda sobre
SU(2), todo `β ∈ R` y todo `F : SU2 → C`, Lean prueba la identidad Wilson
concreta `Q_A(F)=Zβ conjugate(∫F)(∫F)` para `A∈{D,E}`.

El oráculo independiente es
`docs/SU2-TWO-TRANSPORTER-NOGO-ORACLE.lean`. La formalización no usa `sorry`,
`admit`, axiomas de proyecto ni definiciones vacías. `#print axioms` reporta
solo `[propext, Classical.choice, Quot.sound]` para cada uno de los 16
headlines declarados arriba. Esto incluye explícitamente
`su2_trace_conjugate_inverse`, `su2Wilson_orientationD_inner_projection` y
`su2Wilson_orientationE_uv_projection`.

Comandos de comprobación:

```text
lake build YangMills.OS.TwoTransporterHaarProjection
lake env lean docs/SU2-TWO-TRANSPORTER-NOGO-ORACLE.lean
```

## Certificado finito y reproducción

Desde la raíz del repositorio:

```text
python scripts/certify_su2_two_transporter_nogo.py
python -O scripts/certify_su2_two_transporter_nogo.py
python scripts/certify_su2_two_transporter_nogo.py --self-test
python -O scripts/certify_su2_two_transporter_nogo.py --self-test
```

El certificado usa solo la biblioteca estándar de Python. Su dominio exacto
es `Q(sqrt(2))` para los cuaterniones y un reductor de palabras de grupo libre
para las identidades finitas. No muestrea SU(2), no usa punto flotante y no se
presenta como prueba de la identidad integral general. La aceptación requiere
exactamente 14 comprobaciones explícitas, también bajo `python -O`. El modo
`--self-test` exige el rechazo de tres mutaciones: traza decisiva, condición de
unidad del testigo y omisión de una comprobación. El transcript reproducible
de la reparación instrumental está en
`docs/oracle-transcripts/PR39-INSTRUMENTAL-REPAIR-20260731.txt`.

## No-claims

- No se modifica ni amplía `docs/su2-os/**` ni
  `YangMills/OS/SU2WilsonReflection*`.
- No se relanza Fable, Gate 7 ni la auditoría del carril congelado.
- No se afirma que D o E sean la geometría física correcta de una plaqueta.
- No se afirma que el transportador común del carril reducido sea una fijación
  de gauge físicamente derivada; esa es una **interpretación no probada**.
- El certificado Python finito no formaliza la proyección Haar general; esa
  función corresponde exclusivamente al módulo Lean separado.
- No se obtiene positividad no trivial para observables de media cero.
- No se hace ninguna afirmación de continuo, reconstrucción OS/Wightman, gap
  de masa o problema de Clay.
- No hay auditoría independiente terminal todavía: **AUDIT PENDING**.
