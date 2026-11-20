# ¿Cuánta inversión verde se compensa con inversión no verde?

**Resultado.** En la muestra principal de *Greening on Hold*, 0,56/0,74 equivale a 0,757. El apéndice publicado no justifica reconstruir la precisión de este cociente a partir del error estándar de la inversión total. Sí permite una inferencia conservadora para la razón de los dos coeficientes marginales.

## Comprobación de la aditividad

Si los tres resultados satisfacen T = G + N observación por observación y las tres regresiones OLS utilizan el mismo operador lineal, debe cumplirse b(T) = b(G) + b(N) para **todos** los regresores. Con tres cifras redondeadas a centésimas, el error máximo en esta comprobación es 0,015. En el apéndice IA.4, columna 7, e IA.5, columnas 2 y 4, las tres regresiones indican 2.826 observaciones.

| Regresor | Verde G | No verde N | Total T | T − G − N |
|---|---:|---:|---:|---:|
| Riesgo político ambiental | −0,74 | 0,56 | −0,18 | 0,00 |
| Rentabilidad de los activos (ROA) | −6,69 | 11,73 | 4,99 | −0,05 |
| Endeudamiento | −12,90 | −4,98 | −17,91 | −0,03 |
| Logaritmo de la razón mercado/valor contable | −0,59 | 4,47 | 3,90 | 0,02 |

Los tres controles descartan que una identidad lineal exacta y un simple redondeo expliquen a la vez todos los valores impresos. Las tablas no permiten atribuir la discrepancia a selección de filas, tratamiento de extremos, transcripción u otra causa específica. Tampoco permiten deducir que el coeficiente publicado de riesgo político ambiental sea erróneo. La consecuencia concreta afecta a cualquier intento de deducir la covarianza entre sus dos estimadores mediante la varianza publicada del total. [Apéndice original, pp. xvii–xviii](https://www.ecgi.global/sites/default/files/2026-11/fin-1166-2026_greening_on_hold_environmental_political_risk_and_the_reallo_0.pdf#page=69)

## Qué permiten los resultados marginales

Sean n = 0,56 y d = 0,74 los estimadores del aumento no verde y de la disminución verde. Sus errores estándar se recuperan, a la precisión impresa, como sₙ = n/2,05 y s𝒹 = d/4,00. Para un valor candidato r de la razón poblacional, la desigualdad de Cauchy–Schwarz acota el error estándar de n − rd por sₙ + |r|s𝒹, cualquiera que sea su correlación. Invertimos el contraste bilateral manteniendo los valores que cumplen

**|n − rd| ≤ 1,96 (sₙ + |r|s𝒹).**

La cobertura es asintótica y conservadora bajo una aproximación normal conjunta con errores marginales consistentes. El cálculo se refiere a la razón de coeficientes de las dos especificaciones publicadas. Su interpretación como transferencia de gasto entre los mismos proyectos requeriría evidencia adicional.

Con ambos estadísticos t positivos y mayores que 1,96, todos los valores negativos quedan excluidos. El intervalo para r tiene extremos (n − 1,96sₙ)/(d + 1,96s𝒹) y (n + 1,96sₙ)/(d − 1,96s𝒹). Para incorporar el redondeo, se varía cada coeficiente y cada t en ±0,005. Por monotonía, el extremo inferior se obtiene con n mínimo y d máximo, y el superior con n máximo y d mínimo. Ambos extremos exteriores usan los dos t mínimos. Incluso así se excluye cero, se admite la compensación completa (r = 1) y se admiten razones superiores a dos. Esta última inclusión expresa incertidumbre, no evidencia a favor de una compensación superior al doble.

La inversión del contraste de una razón ya figura en el trabajo de Fieller. La contribución aquí es la comprobación de las restricciones y la aplicación a estas tablas. La fuente describe datos de inversión compilados por Corporate Knights. La comparación se realizó sobre estadísticas publicadas. [Fieller, 1954](https://academic.oup.com/jrsssb/article/16/2/175/7026708) · [Datos y definiciones del estudio](https://www.ecgi.global/sites/default/files/2026-11/fin-1166-2026_greening_on_hold_environmental_political_risk_and_the_reallo_0.pdf#page=14)

## Reproducción y resultado numérico

El estudio de Matthew Gustafson, Ugur Lel y Zhongling (Danny) Qin se publicó en la serie de working papers de ECGI el 9 de noviembre de 2026 (DOI 10.67929/ecgi-fin-1166-2026). El PDF fuente examinado tiene SHA-256 81eb23297a51050a88da84ec98064118e8d2369acbaab9c1a0153650f261cf09. El programa reproduce las tres discrepancias de los controles, recupera los t del riesgo ambiental y comprueba con fracciones las ecuaciones de ambos extremos. La estimación puntual exacta sobre los coeficientes impresos es 28/37. Con los números impresos tratados como exactos, los límites son aproximadamente 0,02230 y 2,90253. Al admitir el redondeo, los límites exteriores exactos son 502571/24193577 y 24106629/8156687. Un intervalo que redondea hacia afuera a tres decimales es **[0,020; 2,956]**.

En un runtime propio de Colab Linux, ejecutar reproduce.py y comparar audit.json dentro de /content/archive.zip con el audit.json que acompaña a esta nota. Verificar también el hash del PDF fuente en ambos resultados. La extracción usa pypdf 5.9.0 y necesita acceso al documento original. La nota queda como material de investigación del programa.
