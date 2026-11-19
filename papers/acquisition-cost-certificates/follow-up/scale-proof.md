# Resultado de la última evaluación de QM9

En la propiedad gap, los siete predictores se puntúan sobre el mismo vector completo de valores objetivo. Por la definición usada en el archivo original, cada entrada satisface RMSE relativo = RMSE bruto / desviación típica de ese vector. La incertidumbre de redondeo de las dos cifras impresas a cinco decimales es como máximo h = 0,000005.

Intersectar los intervalos [(r−h)/(z+h), (r+h)/(z−h)] de 3.920 pares brutos y relativos admisibles deja 901/18961 ≤ σ ≤ 7127/149983. Para la estrategia activa, presupuesto 500, semilla 7, se tiene q = 121897/133885, a = 0,03118 y z = 0,82319. Si el error cuadrático medio relativo en el conjunto común fuese a lo sumo 1/4, el MAE normalizado no podría superar q/2 + √[(1−q)((z+h)²−q/4)], por Cauchy–Schwarz en el conjunto y su complemento y por z−h > 1/2. El cálculo racional verifica que (a−h)/(7127/149983) supera estrictamente esa cota.

Así, el RMSE de este predictor en el conjunto común supera la mitad de la desviación típica de la propiedad. Esta es la única de las 838 evaluaciones abiertas por el certificado de v1 que quedó fuera del certificado de ambigüedad uniforme de los dos momentos. El cálculo previo limitado a configuraciones emparejadas no llegó a resolverla. Los dos intentos están archivados.
