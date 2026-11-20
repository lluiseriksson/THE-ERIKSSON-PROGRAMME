# El mes piloto en el control histórico

La sección sobre el despliegue (página física 10) sitúa el comienzo del piloto en marzo de 2024, la introducción de la generación de contenido en abril y la funcionalidad operativa en julio. La ecuación 7 y la figura IV toman marzo como mes cero. En la página física 73, el apéndice D.7 calibra los resultados históricos de los controles con el crecimiento agregado de enero–marzo de 2024 respecto a 2023. Por tanto, la ventana comparte **un mes calendario** con el piloto. Esto es comprobable en el [original de NBER](https://www.nber.org/system/files/working_papers/w36003/w36003.pdf). El solapamiento por sí solo no establece que el piloto alterara ventas, ni que los comercios del calibrador tuvieran uso efectivo ese mes.

## Cuánto podría cambiar el calibrador

Para ventas, si el factor se calcula como cociente de sumas, sean A y M las ventas de enero–febrero y marzo de 2023. Sean g y h las tasas brutas interanuales de esos periodos. Para A,M>0 y w=M/(A+M), el factor trimestral es F=(1−w)g+wh. El cambio al excluir marzo es F−g=w(h−g). Incluye estacionalidad, tendencias y shocks ajenos al piloto. El factor trimestral sin el efecto de la IA en marzo sería F⁰=(1−w)g+wh⁰, si enero y febrero están libres de anticipación. Por tanto, F−F⁰=w(h−h⁰). Un umbral de materialidad absoluta τ en el factor exige |h−h⁰|≥τ/w. La comparación enero–febrero frente al trimestre no identifica por sí misma h⁰.

Si las ventas históricas de un control son x y los factores son positivos, el cambio exacto en su resultado transformado es log[(1+Fx)/(1+F⁰x)]. Tiene el signo de F−F⁰ para x>0, vale cero para x=0 y su valor absoluto está acotado por |log(F/F⁰)|. El límite se alcanza asintóticamente para x grande. Esta cota para una observación individual no es una cota automática para el coeficiente de una regresión con efectos fijos y ponderaciones implícitas.

**Consecuencia.** El control histórico de la figura III se aplica a controles del análisis de empresas, conserva los resultados observados de los tratados y se reestima en una muestra emparejada. Trasladarlo directamente a las ventas totales de todas las categorías requeriría justificar cobertura, entradas, salidas y tendencia común del conjunto. La cifra de crecimiento de los adoptantes y las diferencias entre categorías no suministran ese contrafactual agregado. No se ha estimado un sesgo numérico del estudio.

Fuente conservada con SHA-256 ef9d3fd42db8cbcbbaF9F08108F1547AF3F5C8003E495D388F0EA6CE9560BB53 (mayúsculas y minúsculas equivalentes).
