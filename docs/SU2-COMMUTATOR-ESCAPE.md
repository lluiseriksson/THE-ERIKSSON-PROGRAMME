# Escape algebraico por conmutador en SU(2)

Estado: resultado derivado nuevo, basado exactamente en
`a66b1c7da3c7441e06864e327b5c4efa43e9c79d`
(`su2-os-preaudit-pass-a66b1c7d`). Este documento y los ficheros nuevos no
heredan la pre-auditoría del SHA fuente y requieren auditoría adversarial
propia. No modifican PR #35, no cuentan como Gate 7 y no autorizan un paper.

## EXACTO

Sea `G=SU(2)`, con Haar de probabilidad `μ`, carácter fundamental
`χ(U)=tr(U)` y peso

`wβ(U)=exp((β/2) Re tr(U))`.

Fijamos, sin ambigüedad, la convención

`k(c₁,c₂)=[c₁,c₂]=c₁ c₂ c₁⁻¹ c₂⁻¹`.

Entonces `[c,c]=1` y

`k(c₁,c₂)⁻¹=c₂ c₁ c₂⁻¹ c₁⁻¹=k(c₂,c₁)`.

Como `(c₁,c₂)↦(c₂,c₁)` preserva `μ⊗μ`, `k⁻¹` y `k` tienen la misma ley.

### Los dos momentos

Para `A=c₂`, la entrada `(i,j)` de la primera integral es

`Σₖₗ Aₖₗ ∫ (c₁)ᵢₖ conj((c₁)ⱼₗ) dμ(c₁)`.

La ortogonalidad fundamental de Schur da

`∫ Uᵢₖ conj(Uⱼₗ)dμ(U)=δᵢⱼδₖₗ/2`.

Por tanto, entrada por entrada,

`∫ c₁ c₂ c₁⁻¹ dμ(c₁)=(tr(c₂)/2)I`.

Asimismo, usando `(c⁻¹)ᵢⱼ=conj(cⱼᵢ)`,

`∫ tr(c)c⁻¹ dμ(c)=(1/2)I`.

No se sustituye ninguna exponencial por la exponencial de un promedio. Al
componer los dos cálculos,

`∫∫ k(c₁,c₂)dμ(c₁)dμ(c₂)=(1/4)I`.

El intercambio de variables anterior da también

`∫∫ k(c₁,c₂)⁻¹dμ(c₁)dμ(c₂)=(1/4)I`.

### Integrabilidad y Fubini

Para `U∈SU(2)`, cada valor singular es uno y por la desigualdad triangular
`|χ(U)|≤2`. Además `|Re tr(U)|≤2`, luego

`0<wβ(U)≤exp(|β|)`.

El integrando de la forma cuadrática está acotado explícitamente por

`|conj(χ(x)) wβ(xky⁻¹) χ(y)|≤4 exp(|β|)`.

El dominio es un producto de cuatro espacios compactos con medidas de
probabilidad. Esta constante es integrable; las funciones son continuas.
Fubini/Tonelli para Bochner se aplica. En Lean, el gate genérico
`integral_integral_swap_of_integrable` mantiene la integrabilidad como
hipótesis visible antes de instanciarlo con Haar.

### Cambio condicionado y colapso

Con `c₁,c₂` fijos, se cambia solamente la fibra Haar `x`:

`u=xk`, `x=uk⁻¹`.

Es una traslación derecha fibra a fibra. `c₁,c₂` permanecen intactos y `k` no
se trata como una variable Haar. Después del cambio,

`wβ(xky⁻¹)=wβ(uy⁻¹)`

y `k` aparece únicamente en

`conj(χ(uk⁻¹))`.

La traza es lineal en las entradas de `k⁻¹`. Su momento `(1/4)I` da

`∫∫conj(χ(uk⁻¹))dμ(c₁)dμ(c₂)=(1/4)conj(χ(u))`.

En consecuencia, para la forma concreta definida en Lean sin factor
incorporado,

`Qβ^C(χ)=∫conj(χ(x))wβ(xk(c₁,c₂)y⁻¹)χ(y)dμ⁴=(1/4)Qβ(χ)`.

El teorema congelado se usa sólo en su dominio `0≤β`:

`Qβ(χ)≥β/4`, luego `Qβ^C(χ)≥β/16`.

Si `β>0`, entonces `β/16>0`, de modo que `Qβ^C(χ)>0`. Para `β<0` esta
deducción no aplica; aquí no se afirma positividad.

## CERTIFICADO

`YangMills/Derived/SU2CommutatorEscape.lean` certifica sin marcadores ni
axiomas de proyecto; la obligación abierta viaja como hipótesis explícita:

- la convención, `[c,c]=1` y `k⁻¹(c₁,c₂)=k(c₂,c₁)`;
- los dos momentos matriciales entrada por entrada;
- los momentos `(1/4)I` de `k` y `k⁻¹`;
- el momento conjugado entrada por entrada;
- la traslación derecha condicionada exacta en `x`, que elimina `k` del peso;
- un gate genérico de Fubini con integrabilidad explícita;
- los titulares condicionales
  `su2CommutatorQuadraticForm_lower`, `_strict` y `_one_strict` sobre la
  integral concreta del conmutador; cada uno exige en su tipo la hipótesis
  nombrada `hFubiniBridge : Qβ^C(χ) = (1/4) Qβ(χ)`;
- no vacuidad mediante `χ(1)≠0`, Haar no nula y el acoplamiento concreto
  `β=1`; el certificado exacto añade una matriz SU(2) distinta de la identidad.

Obligación formal restante: descargar `hFubiniBridge` ensamblando en Lean los
intercambios de Fubini de la integral cuádruple con la contracción finita de
la traza. La identidad integral completa es **EXACTA en la derivación
anterior, pero todavía no es un titular Lean CERTIFICADO**. El hueco ya no es
una ausencia: aparece literalmente en el tipo de todos los resultados
terminales sobre el conmutador. No se introduce un axioma ni se altera la
definición concreta de `su2CommutatorQuadraticForm` para codificar `1/4`.

El oracle separado imprime los axiomas de cada titular realmente certificado.
El certificado Python comprueba dos veces, con racionales exactos, las
contracciones finitas `1/2`, `1/2` y `1/4`; no sustituye Haar ni Fubini.

## INTERPRETACIÓN

Este cálculo refuta únicamente un no-go universal que pretendiese abarcar
toda palabra con dos transportadores. No refuta el no-go para `H_D/H_E`,
donde cada transportador aparece una sola vez y se integra libremente.

No se identifica `H_C` con una plaqueta física ni con una construcción de
Osterwalder--Schrader. Esa geometría no se ha derivado. Tampoco se hace una
afirmación de continuo, reconstrucción, gap de masa o problema del Milenio.
