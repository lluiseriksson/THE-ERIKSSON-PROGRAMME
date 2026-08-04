# (45) D-7 por trasplante Dobrushin

Estado: borrador congelable para auditoría externa; no es un dictamen terminal.

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

- La acción completa de traslaciones `ℤ²` con inversas del brick KP no se ha
  transportado todavía al nuevo tipo de observables de spins. El código KP
  actúa sobre coordenadas de enlaces gauge; reutilizarlo por coerciones sería
  falso. Falta construir el observable cilíndrico de sitios sobre `ℤ²` y
  comparar charts rectangulares desplazados (o una aproximación periódica) para
  demostrar invariancia del límite. Por tanto este draft prueba el límite
  termodinámico local centrado, no certifica aún un estado `ℤ²` plenamente
  covariante.
- No se afirma ninguna consecuencia adicional para Yang–Mills.

## Fuentes primarias

- R. L. Dobrushin, *The Description of a Random Field by Means of Conditional
  Probabilities and Conditions of Its Regularity*, Theory Probab. Appl. 13
  (1968), 197–224, DOI
  [10.1137/1113026](https://doi.org/10.1137/1113026).
- R. L. Dobrushin, *Prescribing a System of Random Variables by Conditional
  Distributions*, Theory Probab. Appl. 15 (1970), 458–486, DOI
  [10.1137/1115049](https://doi.org/10.1137/1115049).

## Lista cerrada de ficheros D-7

1. `YangMills/OS/DobrushinMeasureComparison.lean`
2. `YangMills/OS/DobrushinIsingComparison.lean`
3. `YangMills/OS/DobrushinVolumeRestriction.lean`
4. `YangMills/OS/DobrushinVolumeEquiv.lean`
5. `YangMills/OS/DobrushinRectangleVolume.lean`
6. `YangMills/OS/DobrushinThermodynamicLimit.lean`
7. `YangMillsCore.lean`
8. `oracle_check.lean`
9. `docs/DOBRUSHIN-D7-DRAFT.md`
