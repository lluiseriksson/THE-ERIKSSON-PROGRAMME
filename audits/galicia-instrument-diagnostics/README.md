# Diáspora gallega y alfabetización: qué prueba corresponde a la columna 4

En la tabla 2 del paquete de replicación de Martín Fernández Sánchez, la columna 4 estima el efecto rezagado de la proporción de hombres ausentes sobre la alfabetización. La nota de la tabla describe un instrumento de demanda en destino y su interacción con una red migratoria histórica. Sin embargo, la línea 56 de `Code/table_2.do` estima esa columna con **solo el primer instrumento**. La línea 89 calcula diagnósticos con **los dos**. Las líneas 234–235 imprimen esos diagnósticos en las columnas 3–8. El archivo `Tabfig/table_2.txt` sitúa bajo la columna 4 un valor p de sobreidentificación de 0,48 y un estadístico de primera etapa de 20,30. [Paquete del autor, versión 20114638](https://doi.org/10.5281/zenodo.20114638) · [Artículo](https://doi.org/10.1093/jeea/jvag074)

Un instrumento excluido para una variable endógena deja **cero grados de libertad** para el contraste de restricciones de sobreidentificación. El contraste con los dos instrumentos tiene un grado de libertad. El valor 0,48 impreso pertenece al cálculo con ambos. Para evaluar la especificación de la columna 4 se necesita una prueba alineada con el único instrumento utilizado.

## Qué cambia al usar una especificación u otra

Se reconstruyó la misma muestra de 1.284 observaciones, 321 municipios y cuatro censos, con estandarización sobre el panel fuente antes del filtro temporal. Se mantuvieron los controles rezagados de población y alfabetización y los efectos fijos municipales y de año. La reconstrucción con mínimos cuadrados en dos etapas da 0,24727, que reproduce el coeficiente depositado de 0,247 a la precisión impresa. La segunda estimación añade únicamente la interacción que aparece en el diagnóstico. El test tipo Anderson–Rubin de efecto cero usa un Wald conjunto de los instrumentos excluidos, covarianza agrupada por municipio sin corrección de muestra pequeña (CR0) y referencia chi-cuadrado asintótica. Se verificó el ajuste reducido tanto con indicadores municipales explícitos como restando las medias municipales.

| En la misma muestra | Instrumento de demanda | Demanda e interacción |
|---|---:|---:|
| Coeficiente estandarizado | 0,24727 | 0,29200 |
| R² parcial de primera etapa | 0,02470 | 0,03194 |
| Wald de primera etapa por restricción, CR0 | 30,748 | 20,456 |
| Valor p Anderson–Rubin para efecto cero | 0,06769 | 0,01452 |
| Coeficientes al excluir un municipio cada vez | 0,20434–0,29844 | 0,26089–0,33588 |

El signo positivo sobrevive a las 321 exclusiones individuales en ambas especificaciones. Con el umbral convencional del 5 %, la evidencia del contraste de efecto cero depende de qué instrumentos se usen. Los dos valores p de la tabla anterior son cálculos nuevos. El valor p de sobreidentificación responde a otra pregunta. La inferencia sigue dependiendo de la exogeneidad de los instrumentos y de que la agrupación elegida represente adecuadamente la dependencia de los errores. La comprobación tampoco abarca las demás columnas ni las conclusiones a un siglo de distancia.

## Sensibilidad en la escala del resultado

Tras quitar controles y efectos fijos, sea h la proyección de la exposición x sobre el espacio de instrumentos. El coeficiente es (h′y)/(h′h). Para llevarlo a cero mediante una perturbación e del resultado, se necesita h′e = −h′y. Por Cauchy–Schwarz, su menor magnitud cuadrática media, expresada como raíz de la media de cuadrados, es |β|·‖h‖/√n. Se alcanza con e = −βh. Para estos datos los mínimos son 0,01668 y 0,02240 unidades del resultado estandarizado. Es la perturbación hipotética de menor norma en cualquier dirección admisible del vector de resultados. No es una medida observada de sesgo, ni establece que una violación económica concreta pueda generar esa perturbación. La contribución de esta auditoría es el contraste de especificaciones y su cuantificación en el paquete público. [Anderson y Rubin (1949)](https://doi.org/10.1214/aoms/1177730090)

## Reproducción

En un runtime Linux con NumPy, pandas y SciPy, ejecutar `python reproduce.py`. El programa verifica el SHA-256 del ZIP del autor, reconstruye los indicadores relevantes y escribe `/content/archive.zip` con las estimaciones, las pruebas y las 321 exclusiones. Los scripts de Stata del autor permanecen en el depósito original. Esta auditoría calcula directamente sobre su panel en Python. Se conserva una segunda pasada con una regresión explícita de comprobación. La unidad documental auditada es la tabla del paquete versionado.

La página 24 del manuscrito del autor fechado el 31 de julio de 2024 también muestra 0,247, 20,30 y 0,48 en esa columna. El PDF de la revista devolvió HTTP 403 en la consulta de esta ejecución. La correspondencia se verificó para el manuscrito público del autor y el depósito de replicación. [Manuscritos del autor](https://sites.google.com/view/martinfernandezsanchez/research)
