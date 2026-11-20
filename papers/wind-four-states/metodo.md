# Qué conservan cuatro velocidades medias al comparar dos turbinas

Se compara la **potencia eléctrica media prevista** para dos curvas tabuladas ante exactamente la misma serie horaria de viento. La diferencia se expresa en kW por turbina. El archivo de Dakota del Norte proporciona un recurso representativo a 80 m. Las potencias provienen de la biblioteca pública del System Advisor Model (SAM). Este ejercicio de recurso común excluye dirección, densidad variable, estelas, turbinas vecinas, pérdidas eléctricas y paradas. Una decisión real de emplazamiento necesitaría incorporar esos factores.

## Una comprobación que funciona con curvas tabuladas

Sean A y B dos curvas con interpolación lineal por tramos, D=A−B, y V la velocidad en una hora elegida uniformemente. Si el soporte comienza en a, D tiene pendiente inicial s y su pendiente salta en δₖ en los nudos interiores k, entonces

    E[D(V)] = D(a) + s (E[V] − a) + Σₖ δₖ E[max(V−k,0)].

En efecto, la función de la derecha antes de tomar esperanza coincide con D en a y tiene su misma pendiente en cada tramo. Si ambas pendientes cambian en la misma cantidad en un nudo, el término correspondiente desaparece de la diferencia. Para comparar dos diseños basta conservar las excedencias medias por encima de los nudos donde difieren sus cambios de pendiente. La expresión calcula la media horaria sin divulgar el orden de las horas. También explica por qué las medias por grupo pueden fallar incluso con curvas continuas.

Con solo el soporte [l,h], la media m y el peso de cada grupo se pueden calcular los extremos posibles sin elegir una distribución de velocidades. En el gráfico (v,D(v)), la envolvente convexa de los vértices contiene exactamente los pares (E[V],E[D(V)]) de ese grupo si se admiten leyes arbitrarias en el intervalo. La sección vertical en m tiene por extremos valores de las cuerdas que unen vértices a ambos lados de m, o D(m). La interpolación usa masas (b−m)/(b−a) y (m−a)/(b−a) en los extremos a y b de la cuerda. Al sumar por grupos con sus pesos se obtiene un intervalo exacto para esa clase de leyes. Si contiene cero, los resúmenes no bastan para determinar el signo dentro de esa clase. Con frecuencias enteras fijadas de antemano el intervalo sigue siendo válido aunque un extremo pueda requerir masas incompatibles con ese tamaño muestral.

## Protocolo del caso abierto

Se fijó el archivo representativo del norte de Dakota del Norte antes del cálculo y se tomaron todas sus horas a 80 m. Se asignó cada velocidad al más próximo de 2,99, 3,18, 6,25 y 10,12 m/s, resolviendo empates por el primer valor. Para la aproximación se usó la **media observada** de cada grupo y su peso exacto. Se compararon todas las parejas elegibles de igual potencia nominal en el intervalo 1–5 MW con tablas válidas de la biblioteca. Se asignó potencia nula fuera de las tablas únicamente si el tramo afectado acababa en cero. Se conservan los descartes, las medias de todas las curvas y todas las inversiones. El caso destacado maximiza el menor de los dos márgenes absolutos dividido por la potencia nominal entre las inversiones. Esta selección es exploratoria.

Zaidi agrupó velocidades y direcciones antes de reducirlas a cuatro estados. Aquí se usan sus cuatro velocidades únicamente para definir las fronteras de una prueba unidimensional independiente. Una réplica de Winnipeg requeriría, además, sus asignaciones direccionales y la respuesta de cada disposición de turbinas. Estos datos del caso abierto permiten inspeccionar qué información cambia una elección en un modelo de curvas.

[Datos y curvas de SAM en la revisión utilizada](https://github.com/NatLabRockies/SAM/tree/784177b634fa1475fda6672b70595e087a238aea/deploy) · [Artículo de Winnipeg](https://doi.org/10.1177/0309524X261506803) · [Antecedente del autor en PMLR](https://proceedings.mlr.press/v318/zaidi26a.html)
