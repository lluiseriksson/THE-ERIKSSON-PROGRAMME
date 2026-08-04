# (48) Validación Colab del testigo SU(2) de transporte

## Entorno y procedencia

- Cuaderno: <https://colab.research.google.com/drive/14vRYEx8p8yxlvg_MS6YHahvTEgAwQ10j>
- Cuenta Colab Pro+: `lluiseriksson@gmail.com`.
- Runtime: CPU, RAM alta (50.99 GB visibles), sin GPU.
- Rama base publicada: `d3-closure` en
  `c76b790505268eedcb8fe126bc399ccab82baa4f`.
- `main` incorporado por merge, no por rebase, desde
  `04f87347f3e4d46a05e77bc1c70855794e111477`.
- Lean: `v4.29.0-rc6`, el toolchain fijado por el repositorio.

La primera pasada se hizo como overlay de los archivos locales sobre un clone
limpio de la rama base. Después se materializó el merge con el SHA anterior de
`main` y se compiló el root. Esta fue una prevalidación antes de publicar: la
comprobación final se repite desde el SHA congelado de la rama.

## Pruebas ejecutadas

1. `lake exe cache get`.
2. `lake build YangMills.OS.SU2TransportWitness`.
3. `lake env lean docs/SU2-TRANSPORT-WITNESS-ORACLE.lean`.
4. `lake build YangMillsCore` sobre el árbol integrado.

Resultados observados:

- módulo aislado: `Build completed successfully (8173 jobs)`, compilación del
  objetivo en 8.1 s tras reparar tres metas reveladas por la primera pasada;
- oráculo: todas las declaraciones decisorias dependen exactamente del conjunto
  estándar `[propext, Classical.choice, Quot.sound]`;
- root integrado: inicio `2026-08-04T14:16:38Z`, fin
  `2026-08-04T14:33:35Z`, 1010 s medidos, `8483/8483`, `INTEGRATED_RC=0`.

Las advertencias del root fueron lints preexistentes. La advertencia local del
nuevo módulo (`one_mul` redundante) se retiró antes del congelado.

## Ataques descargados

- **SU(2) real:** `phaseHolonomy` y cada `holonomy i` tienen tipo bundled
  `Matrix.specialUnitaryGroup (Fin 2) ℂ`; `holonomy_unitary` y `holonomy_det`
  exponen las dos componentes decisorias de pertenencia.
- **No trivialidad:** `phaseHolonomy_ne_one`, `holonomy_injective`,
  `signVector_ne_zero`, `projected_apply_sign_zero` y `projected_ne_zero`
  descartan el colapso a un punto o al operador nulo.
- **No circularidad:** la covarianza exacta se prueba en `kernel_bandCov` y
  `kernel_bandDecay`; no se recibe como hipótesis la conclusión de transporte.
- **Participación del endpoint:** `exact_transport_witness` invoca literalmente
  `abstract_uniform_gap`, alimentado por `kernel_symm`, `kernel_row` y el lema de
  decaimiento recién probado.
- **Lean frente a Python:** no hay certificado Python del resultado matemático.
  La certificación es el `.olean` y la salida de `#print axioms`.

## Alcance

El objeto es un testigo finito de la interfaz D-6 cuyos estados contienen dos
elementos SU(2) exactos. No es el operador integral continuo completo del calor
de Haar SU(2), no identifica el kernel binario con valores puntuales de aquel
kernel y no crea un nuevo corolario Yang--Mills. Esta tarea entrega el objeto
congelado y sus ataques; no emite el dictamen terminal reservado al auditor
externo.
