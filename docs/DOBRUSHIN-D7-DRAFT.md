# (55) D-7/D-8: límite Dobrushin y estado covariante

Estado: manuscrito completo y objeto congelable para auditoría externa; no es
un dictamen terminal. El paper maquetado vive en
`papers/dobrushin-thermodynamic-limit/` y el PDF en
`output/pdf/dobrushin_thermodynamic_limit.pdf`.

## Resultado probado

La rama construye una comparación de Dobrushin entre dos medidas de Gibbs
finitas a partir de defectos TV sitio a sitio, la especializa a dos volúmenes
Ising rectangulares genuinos mediante un chart común y obtiene, para un
observable `g` soportado en el cuadrado de radio `r`,

```text
|E_m(g) - E_n(g)|
  ≤ [α^(n-r)/(1-α)] · card(CenteredRect r) · osc(g),   r ≤ n ≤ m.
```

De esta cota se deduce Cauchy para la secuencia entera de radios `r+n`, se
construye el límite por completitud de `ℝ` y se prueba convergencia al valor
construido. No se supone Cauchy, convergencia, existencia de estado infinito ni
una estimación de cola de frontera.

El límite se empaqueta además, radio a radio, como una familia compatible de
funcionales reales lineales, positivos y normalizados sobre kernels
cilíndricos centrados. Se demuestra independencia del parámetro auxiliar
`α`, de la presentación del radio de soporte y de todo muestreo cofinal. Una
segunda aplicación de la comparación prueba estabilidad frente a
perturbaciones de filas que retroceden hacia la frontera y, en particular, que
las exhaustiones libres y periódicas explícitas convergen al mismo límite.

La ampliación D-8 construye presentaciones cilíndricas con soporte finito
directamente en `ℤ²`, las cocienta por igualdad de la función realizada sobre
configuraciones globales y hace descender suma, producto y escalares. La
traslación del soporte define una acción aditiva literal de `ℤ²`, con
inversas. La invariancia exacta del acoplamiento periódico bajo los dos
generadores cíclicos, combinada con la igualdad libre--periódica D-7, produce
un funcional positivo, normalizado y real-lineal `ω` que satisface
`ω (z +ᵥ O) = ω O` para todo `z : Fin 2 → ℤ`.

La ventana utilizada en todos los teoremas concretos es

```text
0 ≤ α < 1,
2 tanh|β| + 2 tanh|γ| ≤ α.
```

En el caso isótropo esto conserva `tanh|β| < 1/4`, es decir
`|β| < atanh(1/4) ≈ 0.2554`; no aparece ninguna hipótesis KP.

## Inventario y participación

- `DobrushinConditional`, `DobrushinComparison`, `DobrushinGibbs` y
  `DobrushinIsing`: kernels de calor, matriz de influencia y ventana.
- `DobrushinLattice`: distancia Manhattan, acoplamiento rectangular y suma de
  fila uniforme.
- `DobrushinMeasureComparison`: telescopado random-scan, resolvente y cola
  geométrica sin factor de volumen.
- `DobrushinIsingComparison`: traduce igualdad de filas a igualdad de kernels
  y compara Hamiltonianos con filas defectuosas.
- `DobrushinVolumeRestriction` y `DobrushinVolumeEquiv`: eliminación exacta de
  spins espectadores y reindexación exacta de sumas Gibbs.
- `DobrushinRectangleVolume`: chart centrado, geometría del corte, soporte y
  oscilación uniformes, y comparación de dos volúmenes genuinos.
- `DobrushinThermodynamicLimit`: secuencia entera, Cauchy, límite y convergencia.
- `DobrushinInfiniteState`: linealidad, positividad, normalización,
  compatibilidad entre radios, independencia canónica, estabilidad de frontera
  y comparación libre--periódica.
- `DobrushinSiteCylinder`: soporte finito intrínseco en `ℤ²`, cociente por
  realización global, operaciones puntuales y acción completa con inversas.
- `DobrushinPeriodicTranslation`: simetría exacta de la adyacencia, del
  acoplamiento y de toda expectativa Gibbs periódica en ambas direcciones.
- `DobrushinCovariantState`: descenso del límite al cociente, linealidad,
  positividad, normalización e invariancia bajo todo `ℤ²`.

El brick KP se reutiliza como arquitectura de prueba (chart común, cota
par-a-par, Cauchy de toda la secuencia y selección del límite), no como
hipótesis analítica. Sus tipos `CompatibleLocalObservable` e
`IntegerLocalObservable` son específicos de enlaces gauge y no se pueden
instanciar honestamente con spins de sitios Ising.

## Kill-tests

1. **Circularidad:** ninguna declaración anterior a Cauchy contiene `CauchySeq`,
   `Tendsto` o un valor infinito como premisa.
2. **Vacuidad:** el defecto entre acoplamientos es TV y queda acotado por `1`;
   filas iguales producen defecto exactamente cero.
3. **Factor de volumen:** se suman primero todos los sitios defectuosos en el
   resolvente. Las potencias menores que la distancia se anulan y la suma de
   fila da `α^R/(1-α)`, sin `card(volumen)`.
4. **Observable local:** el levantamiento es insensible fuera del core y su
   suma total de oscilaciones está acotada por
   `card(core) * osc(g)`, independientemente del volumen exterior.
5. **Ventana:** búsqueda textual y tipos terminales no contienen constantes KP;
   la única pequeñez concreta es la ventana Dobrushin visible.

## Frontera no probada

- No se construye todavía la complejificación, norma uniforme, involución,
  completación ni extensión continua necesarias para un estado C* genuino.
- No se comparan formas Følner arbitrarias ni se empaqueta una especificación
  DLR sobre el espacio producto infinito.
- No se afirma ninguna consecuencia adicional para Yang–Mills.

## Fuentes primarias

- R. L. Dobrushin, *The Description of a Random Field by Means of Conditional
  Probabilities and Conditions of Its Regularity*, Theory Probab. Appl. 13
  (1968), 197–224, DOI
  [10.1137/1113026](https://doi.org/10.1137/1113026).
- R. L. Dobrushin, *Prescribing a System of Random Variables by Conditional
  Distributions*, Theory Probab. Appl. 15 (1970), 458–486, DOI
  [10.1137/1115049](https://doi.org/10.1137/1115049).

## Lista cerrada de ficheros D-7/D-8

1. `YangMills/OS/DobrushinMeasureComparison.lean`
2. `YangMills/OS/DobrushinIsingComparison.lean`
3. `YangMills/OS/DobrushinVolumeRestriction.lean`
4. `YangMills/OS/DobrushinVolumeEquiv.lean`
5. `YangMills/OS/DobrushinRectangleVolume.lean`
6. `YangMills/OS/DobrushinThermodynamicLimit.lean`
7. `YangMills/OS/DobrushinInfiniteState.lean`
8. `YangMills/OS/DobrushinSiteCylinder.lean`
9. `YangMills/OS/DobrushinPeriodicTranslation.lean`
10. `YangMills/OS/DobrushinCovariantState.lean`
11. `YangMillsCore.lean`
12. `oracle_check.lean`
13. `docs/DOBRUSHIN-D7-DRAFT.md`
14. `papers/dobrushin-thermodynamic-limit/dobrushin_thermodynamic_limit.tex`
15. `papers/dobrushin-thermodynamic-limit/README.md`
16. `papers/dobrushin-thermodynamic-limit/RELEASE-MANIFEST.md`
17. `output/pdf/dobrushin_thermodynamic_limit.pdf`
