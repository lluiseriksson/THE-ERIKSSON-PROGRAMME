# (48) Testigo SU(2) exacto para transporte

Estado de fabricación: compilación y oráculo validados en Colab Pro+;
pendiente exclusivamente del dictamen de auditoría externa.

## Endpoint canónico

El endpoint mínimo es
`YangMills.OS.Dobrushin.abstract_uniform_gap`, en
`YangMills/OS/DobrushinTransport.lean`.  Transporta decaimiento uniforme de
covarianzas de banda a una cota uniforme del operador de transferencia
proyectado.  El teorema publicado en la rama Dobrushin v8 lo consume a través
de `dobrushin_ising_uniform_gap`; el testigo interno anterior,
`transport_witness`, sólo usa el tipo `Fin 2`.

El nuevo objeto exacto es
`YangMills.OS.Dobrushin.SU2Transport.exact_transport_witness`, en
`YangMills/OS/SU2TransportWitness.lean`.  Su carrier finito contiene, en cada
punto, un elemento bundled de
`Matrix.specialUnitaryGroup (Fin 2) ℂ`: la identidad o `diag(I,-I)`.

## Interpretaciones distinguidas

1. **Dobrushin / transporte de covarianza a gap (carril fijado).** Es el único
   que conecta literalmente con el endpoint abstracto y el teorema publicado.
2. **Dos transportadores Haar SU(2).**
   `YangMills/OS/TwoTransporterHaarProjection.lean` prueba un no-go para dos
   holonomías libres. No instancia `abstract_uniform_gap` y responde otra
   pregunta.
3. **Transporte físico/CMP116.**
   `YangMills/RG/PhysicalGaugeCMP116OperatorTransport.lean` transporta
   coordenadas, kernels y soportes RG. No es consumidor del teorema D-6.
4. **Operador de calor continuo completo.** El satélite primario
   `lluiseriksson/lean-2d-yang-mills` prueba el semigrupo concreto de calor
   SU(2) por expansión de caracteres. El endpoint D-6 exige tipos finitos, por
   lo que importarlo como si SU(2) fuera un `Fintype` sería falso. El presente
   testigo usa sólo el modo fundamental exacto `exp(-3t/4)` sobre dos puntos
   SU(2) explícitos y declara esta limitación.

## Teoremas ya disponibles y descargados

- `ClayCore.twoSitePhase_mul_conjTranspose` y `twoSitePhase_det` prueban la
  unitariedad y determinante uno de `diag(I,-I)`.
- `Dobrushin.wKernel_symm`, `wKernel_row` y `wKernel_pow` proporcionan el
  álgebra exacta del kernel de dos estados.
- `Dobrushin.band_pair`, `connCorr_eq_bandCov` y
  `abstract_uniform_gap` constituyen la cadena decisoria del endpoint.
- `TransferGap.volumeUniform_gap` fija el mass rate `m = -log r`.

El nuevo módulo no carga ninguna de estas conclusiones como hipótesis. Prueba
en particular:

- `holonomy_unitary`, `holonomy_det`, `holonomy_injective`;
- `kernel_symm`, `kernel_row`, `kernel_pow`;
- la identidad exacta `kernel_bandCov`;
- la identidad de no trivialidad `projected_apply_sign_zero` y la consecuencia
  `projected_ne_zero`;
- la instanciación end-to-end `exact_transport_witness`.

## Alcance y no-afirmaciones

El resultado demuestra que la interfaz publicada de transporte posee un
testigo no-Ising, no vacío y genuinamente SU(2)-habitado, con el factor de calor
fundamental exacto. No construye el operador integral continuo completo sobre
Haar SU(2), no identifica el kernel binario con valores puntuales de ese kernel
integral, no añade un resultado Yang--Mills 4D y no recibe dictamen terminal en
esta tarea. El oráculo Lean es
`docs/SU2-TRANSPORT-WITNESS-ORACLE.lean`; cualquier certificado Python futuro
sería instrumental y no sustituiría estas pruebas Lean.

## Fuentes primarias

- Repositorio satélite exacto SU(2):
  <https://github.com/lluiseriksson/lean-2d-yang-mills>
- Semigrupo de calor SU(2) formalizado:
  <https://github.com/lluiseriksson/lean-2d-yang-mills/blob/main/Lean2dYangMills/SU2HeatSemigroup.lean>
- Kernel de clase y pesos de Casimir:
  <https://github.com/lluiseriksson/lean-2d-yang-mills/blob/main/Lean2dYangMills/SU2ClassHeatKernel.lean>

Estas fuentes sustentan el factor `exp(-t n(n+2)/4)`, cuyo primer modo no
trivial (`n=1`) es `exp(-3t/4)`. La conexión al endpoint D-6 y todas las
identidades finitas del testigo se prueban dentro de este repositorio.
