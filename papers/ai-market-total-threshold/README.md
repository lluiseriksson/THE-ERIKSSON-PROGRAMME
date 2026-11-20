# Cuándo el crecimiento diferencial implica mayores ventas totales

Nota de investigación del 20 de noviembre de 2026. Aplicación a Barwick, Fang, Liu, Xu y Yuan, *AI as Shared Business Infrastructure*, NBER w36003. [Fuente primaria](https://www.nber.org/papers/w36003).

## Qué identifica el estudio

La ecuación 7 interactúa el mes relativo al piloto con la tasa de reembolso de cada categoría, medida en 2023. Incluye efectos fijos de categoría y de mes. El piloto comenzó en marzo de 2024 y febrero es el mes omitido. Para ventas, el resultado es log(1 + ventas). La figura IV muestra los coeficientes de interacción. La sección 3.4, pp. impresas 19–20, explica expresamente que se trata de una comparación entre categorías con distinta fricción inicial. La figura IV está en la página impresa 50. La cifra de 51,6 % pertenece a otra regresión, de empresas adoptantes.

En su modelo estructural, la proposición 3 condiciona el crecimiento de ventas a una elasticidad de demanda superior a uno. Su evidencia sobre entrada, pedidos y efectos indirectos tiene valor adicional. El problema resuelto aquí se limita a qué se puede deducir del gradiente de la ecuación 7. La distinción básica ya está en la fuente.

## Umbral para un mes y un conjunto fijo de categorías

Sean yᵢ las ventas observadas con IA y yᵢ⁰ las que se habrían producido sin el programa. Ambas son no negativas y están expresadas en las mismas unidades que la regresión original. Supongamos, favorablemente para la identificación, que conocemos exactamente todos los efectos relativos dᵢ en la escala log(1 + ventas). Para una categoría de referencia fijamos d = 0. En el caso afín dᵢ = β(rᵢ − r*), con rᵢ la exposición. Esta igualdad de efectos individuales es un supuesto más fuerte que conocer una pendiente de regresión. Queda un componente común a.

\[
\log(1+y_i)-\log(1+y_i^0)=a+d_i .
\]

Escribamos B = Σᵢ(1+yᵢ), wᵢ=(1+yᵢ)/B y H=Σᵢwᵢ exp(−dᵢ). Al despejar cada contrafactual y sumar, la diferencia total de ventas es

\[
\Delta=B(1-H e^{-a}).
\]

El umbral es exacto: Δ > 0 si y solo si a > log H. Si se dispone de una cota inferior L sobre a, la garantía estricta para todos los valores admisibles empieza en L > log H, suponiendo L alcanzable y el conjunto no vacío. Cambiar la referencia desplaza a y log H en la misma cantidad. Los pesos incorporan el uno sumado a cada categoría en la transformación. Sustituirlos por participaciones simples en ventas cambia el umbral.

**Límite impuesto por las ventas observadas.** La no negatividad de cada yᵢ⁰ exige a ≤ U = minᵢ[log(1+yᵢ) − dᵢ]. Recíprocamente, para cada a ≤ U, el despeje yᵢ⁰=(1+yᵢ)exp(−a−dᵢ)−1 construye un contrafactual admisible. Sobre ventas reales no negativas, el conjunto exacto de diferencias es (−∞, B(1−H exp(−U))]. Con una cota externa L ≤ U, el extremo inferior pasa a B(1−H exp(−L)). Una categoría sin ventas situada en la exposición de mayor efecto impone U ≤ −máx dᵢ ≤ log H. En ese caso el propio supuesto de efectos relativos exactos impide una ganancia agregada estricta. No se afirma que esa situación se dé en los datos de la plataforma.

## Mismos datos y tres efectos agregados distintos

El ejemplo utiliza dos categorías. Las ventas anteriores son (119, 59) y las posteriores observadas son (119, 119). Las exposiciones pueden ser 0,05 y 0,15, con β = 10 log 2. El multiplicador relativo de la segunda categoría es dos. Los datos observables, la pendiente y las tendencias paralelas en log(1 + ventas) son iguales en los tres casos. Los números son construidos para comprobar identificación.

| Multiplicador común exp(a) | Ventas posteriores sin IA | Cambio común sin IA en 1 + ventas | Efecto total |
|---:|---:|---:|---:|
| 1/2 | (239, 119) | ×2 | −120 |
| 3/4 | (159, 79) | ×4/3 | 0 |
| 1 | (119, 59) | ×1 | +60 |

En los tres casos, las ventas observadas suman 238 y H=3/4. El componente común sin IA difiere porque no se observa. La tendencia sin IA dentro de cada caso es idéntica entre las dos categorías. Así, las diferencias entre categorías y el paralelismo de tendencias por sí solos permiten los tres signos.

## Qué publicar si faltan las participaciones por categoría

Si se conoce la media m ponderada por los wᵢ de las diferencias dᵢ y solo se sabe que dᵢ∈[l,u] con l<u, la convexidad de exp(−d) da

\[
e^{-m}\ \le H\le\frac{u-m}{u-l}e^{-l}+\frac{m-l}{u-l}e^{-u}.
\]

La cota inferior se obtiene concentrando la distribución en m. La superior se obtiene repartiendo masa entre los extremos para obtener esa media. Son cotas óptimas entre distribuciones con esa información, antes de imponer otros datos sobre categorías concretas. Con d constante se tiene H=exp(−m). Estas fórmulas permiten evaluar un ancla externa aun cuando el editor solo divulgue resúmenes agregados. Una media por número de categorías puede diferir de la media ponderada necesaria.

## Alcance y prioridad

Esta comprobación no estima el efecto real de la IA en la plataforma. No se disponía de su panel privado. Tampoco sustituye una pendiente en escala logarítmica por el logaritmo de un efecto medio en niveles. Para estimar o acotar el cambio total hacen falta evidencia sobre el contrafactual común y una justificación de los efectos relativos usados. Una serie externa comparable exige un argumento independiente sobre exposición, escala, tendencias y composición.

Los antecedentes metodológicos incluyen el análisis de identificación con tratamiento continuo de [Callaway, Goodman-Bacon y Sant’Anna](https://www.nber.org/papers/w32117) y el trabajo de [de Chaisemartin, D’Haultfœuille y Vazquez-Bare](https://doi.org/10.1257/pandp.20241049). Se documenta una aplicación con pesos y restricciones de soporte específicos de log(1 + ventas). La identidad algebraica, el argumento de convexidad y la falta de un contrafactual común no justifican reclamar prioridad metodológica mundial. Conservar esta nota como parte de una investigación más amplia sobre mercados de IA hasta que haya un ancla defendible o una segunda aplicación sustantiva.
