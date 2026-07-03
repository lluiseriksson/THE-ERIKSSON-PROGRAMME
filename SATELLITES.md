# SATELLITES — fleet ledger of THE-ERIKSSON-PROGRAMME

One row per satellite.  Each satellite may modify **only its own section**,
via the milestone ritual (tag `vM<k>` + single-file PR).  The coordinator
merges; the orchestrator bot reads nothing here (it reads `STATUS.json` on
each satellite's `status` branch and regenerates `DASHBOARD.md`).

Honesty rule, inherited from `HYPOTHESIS_FRONTIER.md`: nothing in this file
may claim more than a `main`-branch theorem proves.  Session pushes that are
still awaiting CI are marked `pending-CI` and count as NOTHING until green.

| repo | rol | estado main (verificado) | sesión 2026-07-03 (pending-CI hasta heartbeat verde) |
|---|---|---|---|
| lean-gaussian-field | gaussianas para hRpoly | T0 verde | push/m1-core: Cauchy-Schwarz PSD, finitud de pairings, cota Wick uniforme en dimensión; frontier/M1: Isserlis statements |
| lean-transfer-matrix | diccionario gap⇔clustering | T0 verde (M0: diagonalización 2×2) | push/m1-ising-closure: PRIMERA instancia de TransferOperatorInterface con cero hipótesis (Ising ferro); tasa exp(−rate·n) probada positiva; T^n forma cerrada; frontier: Perron-Frobenius (candidato Mathlib), Gibbs desde primeros principios |
| lean-os-positivity | definición del objetivo RP/OS | T0 verde | push/m1-rp-core: Cauchy-Schwarz de reflexión (Glimm-Jaffe 6.2.2); RP ⟺ núcleo PSD (ambas direcciones); bond Ising/Potts ferro RP incondicional; frontier: seminorma GNS, multi-bond vía Schur. ERRATA de patch: ver PUSH_REPORT del madre |
| lean-connes-kreimer | Hopf de árboles | T0 verde | push/m0-grading: cálculo de graduación completo con ley multiplicativa; GraftingProvider con B₊; HALLAZGO de interfaz (Nonempty subespecifica; propuesta AdmissibleCutData) — decisión del Revisor pendiente |
| lean-2d-yang-mills | sandbox soluble + zeta de Witten | T0 verde | push/m4-witten-riemann: ζ_Witten(SU(2)) = riemannZeta (paquete incondicional); Z_g = ζ(2g−2); motor de convergencia M0; frontier: caracteres vía Chebyshev, falta solo |tr g| ≤ 2 |
| lean-zero-free-regions | primer consumidor externo de KP | T0 verde (M0: KP ⇒ Z ≠ 0) | push/m0-polydisc: KP ⇒ polidisco libre de ceros; sección de fugacidad polinómica y entera; caso base Lee-Yang descargado; ADOPTADO UPSTREAM en YangMills/KP/ActivityDomain.lean. ERRATA de patch: ver PUSH_REPORT del madre |
| lean-ym-flow | toolbox parabólico | T0 verde | push/m0-discrete-parabolic: máximo/mínimo discretos bajo CFL + conservación de masa, iterados; primera instancia incondicional de M0 (flujo lineal en intervalo compacto) |
| lean-rooted-tree-polymer-expansion | combinatoria de árboles para KP | ya importa YangMills@4e45246 | sin empuje hoy |
| ym-lattice-numerics | Monte Carlo + certificación (exento del lock Lean) | T0 verde (7 tests) | push/m0-exact2d-certified: VERIFICADO LOCALMENTE 20/20 tests; σ exacta 2D certificada por intervalos (25 dígitos); MC validado contra Bessel; honesty-gap M4: la ventana (16d+1)²σ<1 pasa en β≈2000 y falla en β=1..4 |

## Bloqueadores cruzados registrados

- Capa Peter-Weyl compartida (SU(2)): bloquea el M0 real de lean-2d-yang-mills
  (cota de Weyl + ortogonalidad) y el M1 de lean-ym-flow (SU(2)^aristas).
  Coordinar vía PETER_WEYL_ROADMAP.md; no duplicar.
- Tipo de árbol compartido: bloquea la instanciación de GraftingProvider en
  lean-connes-kreimer; candidato natural: lean-rooted-tree-polymer-expansion.
  Decisión humana (dependencia cruzada toca lakefile + manifest).
- lean-os-positivity M1-transfer: bloqueado en lean-transfer-matrix vM1
  (empujado hoy, pending-CI).
