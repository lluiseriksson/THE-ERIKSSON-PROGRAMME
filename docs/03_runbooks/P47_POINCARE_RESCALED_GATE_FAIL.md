# (47) Puerta de Poincaré reescalada

Estado de ejecución: **FAIL — puerta falsificada**. Este documento congela el
objeto y los ataques observados; no constituye autocertificación. El dictamen
terminal corresponde a una auditoría externa independiente.

Fecha de ejecución: 2026-08-04. Rama aislada:
`codex/poincare-rescaled-gate-47`. Antes de ejecutar se integró `origin/main`
mediante merge, sin rebase, squash ni force-push. El merge limpio quedó en
`5477f3c21e4127bd43fe79d027d98979a63b57b3`, con padres
`574ac60246a54ff58efb080907e48bae71762026` y
`04f87347f3e4d46a05e77bc1c70855794e111477`.

## 1. Falsificador registrado y criterio congelado

El falsificador aplicable ya estaba registrado en la línea de trabajo
`codex/stieltjes-root` y en el paquete
`papers/critical-rescaling-no-go-all-coarse`. Su fuente inmutable declarada es:

- commit fuente:
  `f21539ed0bb880a04078de369bf5cbf063f7b101`;
- Lean: `v4.29.0-rc6`, commit
  `00659f8e6071d7e46131ed643bf8003b99b044e9`;
- Lake: `5.0.0-src+00659f8`;
- Mathlib: `07642720480157414db592fa85b626dafb71355b`;
- módulo terminal:
  `YangMills.RG.PhysicalCriticalRescalingFourierNoGoAllScales`;
- juez de axiomas:
  `YangMills/RG/PhysicalCriticalRescalingFourierNoGoOracle.lean`.

El criterio congelado, sin modificación del juez, fue:

1. `lake build YangMills.RG.PhysicalCriticalRescalingFourierNoGoAllScales`
   debe terminar correctamente;
2. `lake env lean YangMills/RG/PhysicalCriticalRescalingFourierNoGoOracle.lean`
   debe producir nueve resultados, cada uno exactamente con
   `[propext, Classical.choice, Quot.sound]`;
3. los siete cuerpos no deben contener `sorry`, `admit` ni declaraciones
   `axiom` de proyecto;
4. el teorema terminal esperado es
   `volumeUniformCriticalRescaledFlatPoincareGate_fourier_false`, de tipo
   `¬ VolumeUniformCriticalRescaledFlatPoincareGate N' Nc ρ`, para todo
   `N' > 0`, `Nc ≥ 2` y modelo adjunto `ρ`.

La salida esperada fue congelada antes de la corrida a partir del manifiesto
v1.1: compilación focal satisfactoria con 8184 trabajos y nueve consultas de
axiomas con el trío anterior.

## 2. Captura binaria y hashes

Método de captura: `Get-Content -Raw -Encoding Byte`/`ReadAllBytes` en el
worktree Windows para los bytes presentes; normalización determinista
`CRLF -> LF`, después `CR -> LF`, para el cuerpo LF; reconstrucción
`LF -> CRLF` para el cuerpo CRLF. SHA-256 se calculó sobre cada secuencia de
bytes. El ZIP de transporte contenía únicamente archivos fuente rastreados,
`lake-manifest.json` y `lean-toolchain`, conservando rutas.

| cuerpo | bytes raw/CRLF | SHA-256 raw/CRLF | bytes LF | SHA-256 LF |
|---|---:|---|---:|---|
| `PhysicalCriticalRescalingFourierCochain.lean` | 6626 | `F8FDDE291755A9BE8A7DB93E6138BBE8CDE8D176E7A75B0B2061152AB7D72E3D` | 6462 | `53993EAAA55418AE7EA1235CDEDB0793A4EA58D452F577EA0A677AD203733793` |
| `PhysicalCriticalRescalingFourierEnergy.lean` | 4578 | `22C8AEFEC0FC926866BB0A54F340C68104B61082C859CB2E6B9CD2BA02C96007` | 4465 | `A94083D9FCE54442AAC8C3990180F92469F1A7915F530A287CF16611A5C3E149` |
| `PhysicalCriticalRescalingFourierHodge.lean` | 6091 | `F9C535C9DECF01831A08F77FC99C2F7EB61046760C2961BE153B18921BB4D32D` | 5941 | `C311EEB648DD0371C7B9D343A37BC659DF537FD5E1A33F6EA7F20CBD702665E9` |
| `PhysicalCriticalRescalingFourierMode.lean` | 3510 | `5CCE02EA172B1CBDC67E906127868BA63DC0D919CE429E1FC70B0C1D313C03CB` | 3418 | `B3884618CC9B82B1E138089323DEAEF24D6E4613DAAE6A10D6EC0AFC37526993` |
| `PhysicalCriticalRescalingFourierNoGo.lean` | 8492 | `AC64F246016E7418A5D0C62357A8E9D780643CE3AC8761F9B6637239101C9504` | 8282 | `6F0D69D79B6C93D01A8C298EC6E9E5A53FD37DE43DF5963B8A0411DE2930153D` |
| `PhysicalCriticalRescalingFourierNoGoAllScales.lean` | 5125 | `6A6D69F1A76BE4BD70DAEF9FE28F73089323A1C1C3D3B4633329104010561077` | 5004 | `5F0890D14EA6981CBE6459605A634386ED2C844F6D03A6947E33B34250E2F5AE` |
| `PhysicalCriticalRescalingFourierNoGoOracle.lean` | 779 | `281BEF0FDC2CCD2BE6DD6DF498B82EA2ED8501CBBDB6A16FED1B87E22395035E` | 766 | `ADAEB6E955E83C4CEC97A84D45590AD449B038F0CA6B08FAF2586652961C3CCB` |

Paquete de transporte: 1,793,151 bytes, SHA-256
`771B088B6D0A32CF1097F6BD3DB6F0CD446F0B9FA402CD939DABAA0DF5DF70AF`.
Los hashes se volvieron a calcular dentro del runtime antes de instalar o
compilar y coincidieron con esta tabla.

## 3. Ejecución remota

Se utilizó Colab Pro+ con CPU, alta RAM, sin GPU: 8 procesadores y
`MemTotal: 53467192 kB`. La preparación del notebook se hizo con runtime
desconectado. Apertura efectiva medida por la primera celda:
`2026-08-04T13:59:36Z`. Fin de la metaverificación:
`2026-08-04T14:10:18Z` (642 s). La desconexión y borrado se confirmaron en la
interfaz; el estado `Reconectar` quedó verificado no más tarde de
`2026-08-04T14:11:09Z`, por lo que la ventana conectada medida fue como máximo
693 s.

`lake update` reescribió únicamente los finales de línea del manifiesto:

- SHA-256 raw anterior (CRLF):
  `E2F2D45A5FEF5AE352E6F8BE858726D603D83FDE30D740A14A8A2A588579381D`;
- SHA-256 raw posterior (LF):
  `1C72B465AB37A0418DE6F82573C18BB0E79F9E0165E901FD9DA0DDABECDB2611`;
- SHA-256 LF anterior y posterior:
  `1C72B465AB37A0418DE6F82573C18BB0E79F9E0165E901FD9DA0DDABECDB2611`;
- objetos JSON: idénticos.

No se modificó ninguna fuente ni el juez. La primera comparación binaria del
manifiesto se detuvo por esa normalización y se conservó como incidente del
harness; la continuación comprobó igualdad JSON y de bytes LF.

Resultado observado:

- `Build completed successfully (8184 jobs).`;
- 9/9 consultas del oráculo con
  `[propext, Classical.choice, Quot.sound]`;
- escaneo de tokens de código: `PASS`;
- log de build: 2330 bytes, SHA-256
  `2976F3B2FA0CFB8640CE4B6139F7AF9320F3C616894B4B59612C843FECAC8C97`;
- log del oráculo: 1071 bytes, SHA-256
  `D3594ECB7DDB2DF7A4A6958527F9AC8BAF387C50CED89AB5848EFCA340EFBB45`;
- log de `lake update`: 9802 bytes, SHA-256
  `9E8D52638BA072D0B76503C89A5B6DA13AF1676DD9C972C94947BF707C9D9F13`;
- marcador terminal: `AUDIT47_RESULT=FAIL_GATE_FALSIFIED`.

Notebook conservado como traza de ejecución:
`https://colab.research.google.com/drive/1Ozsi-3-0eoIAGH4CdPuMcqgxr3qrVAgO`.
El runtime y sus archivos efímeros fueron borrados.

## 4. Contraejemplo y alcance exacto

Para `d = 4`, cada `L ≥ 2`, cada lado grueso fijo pero arbitrario `N' > 0`,
cada `Nc ≥ 2` y cada modelo adjunto `ρ`, el cochain transversal de Fourier
`A_L` satisface exactamente:

\[
 Q_L A_L=0,\qquad \operatorname{div}A_L=0,
 \qquad \|A_L\|^2=(LN')^4,
\]

y

\[
 \frac{\langle A_L,K_0A_L\rangle}{\|A_L\|^2}
 =\lambda_L=4\sin^2(\pi/L)
 \le (2\pi/L)^2.
\]

Como `Q_L A_L = 0`, también `(a_L Q_L)A_L=0` para **todo** reescalado
escalar `a_L`; el exponente crítico no puede alterar este sector. Si existiera
un `CP > 0` elegido antes de cuantificar `L`, la desigualdad de Poincaré daría

\[
 1\le CP\,\lambda_L\le 4\pi^2 CP/L^2,
\]

lo que contradice la elección posterior de `L` suficientemente grande. Esta
es la divergencia oculta que el reescalado no elimina: cualquier constante
admisible debe crecer al menos como `L^2/(4\pi^2)`.

El endpoint `L=2` está incluido; no se usa un límite abierto ni una expansión
asintótica para establecer el núcleo o el cociente exacto. `N'` no se envía a
infinito: es positivo, fijo y arbitrario, y el factor de volumen `(LN')^4` se
cancela de ambos lados. `CP` se elige antes de `L`, de modo que no puede
absorber dependencia de volumen. El testigo formal necesita dos direcciones
distintas y un vector interno no nulo, realizados por `d=4` y `Nc≥2`.

## 5. Auditoría del exponente

En el sector constante, con `a_L=L^σ`, las identidades exactas son

\[
 \|A\|^2=L^d(N')^d S,
 \qquad \|a_LQ_LA\|^2=L^{2σ+2}(N')^dS,
\]

por lo que cualquier estimación uniforme fuerza

\[
 L^{d-2-2σ}\le CP.
\]

Así, `σ ≥ (d-2)/2` es necesario para no hacer divergir la constante por el
**sector constante**. La igualdad `σ=(d-2)/2` es la única elección que hace
ese sector exactamente neutro/isométrico en escala, pero no es necesaria para
la mera acotación uniforme: todo exponente mayor también supera este test.
Por tanto, presentar la igualdad como “necesaria y suficiente” sin imponer
separadamente neutralidad exacta sería introducir la conclusión en las
hipótesis. Además, ningún exponente escalar es suficiente para la puerta de
espacio completo, por el núcleo de Fourier anterior.

El desarrollo Lean auditado formaliza la puerta y su falsedad en `d=4`; la
fórmula aritmética general en `d` es una derivación analítica del teorema de
sector constante, no una afirmación de que se haya materializado un `.olean`
general para una puerta positiva.

## 6. Hipótesis físicas y geométricas que permanecen abiertas

Una ruta distinta tendría que cambiar el enunciado, no rescatar esta puerta:

- justificar físicamente un dominio restringido o cociente que elimine los
  modos transversales y demostrar que sea estable bajo el RG;
- añadir un Hessiano/interacción positiva `V_L` con cota uniforme sobre la
  familia explícita;
- cambiar el operador de bloque de manera no escalar y demostrar coercividad
  en el nuevo dominio.

No se deduce coercividad interactuante, medida de volumen infinito, límite
continuo, reconstrucción de Osterwalder-Schrader ni mass gap. No se implementó
una puerta Lean positiva porque el criterio vinculante ordena cerrar en FAIL.

## 7. Prioridad bibliográfica

El no-go se limita al operador plano de espacio completo aquí definido. No
reivindica prioridad sobre la necesidad general de gauge fixing ni contradice
propagadores construidos en dominios restringidos, con minimizadores o fondos.
Fuentes primarias:

- T. Bałaban, *Propagators and renormalization transformations for lattice
  gauge theories. I*, CMP 95 (1984), 17–40,
  [doi:10.1007/BF01215753](https://doi.org/10.1007/BF01215753).
- T. Bałaban, *Propagators and renormalization transformations for lattice
  gauge theories. II*, CMP 96 (1984), 223–250,
  [doi:10.1007/BF01240221](https://doi.org/10.1007/BF01240221).
- J. Dimock, *Covariant axial gauge*, LMP 105 (2015), 959–987,
  [doi:10.1007/s11005-015-0763-0](https://doi.org/10.1007/s11005-015-0763-0).

Las fuentes de herramienta fijadas para reproducción son la
[release de Lean v4.29.0-rc6](https://github.com/leanprover/lean4/releases/tag/v4.29.0-rc6)
y el
[commit exacto de Mathlib](https://github.com/leanprover-community/mathlib4/commit/07642720480157414db592fa85b626dafb71355b).

## 8. Entrega para dictamen externo

Objeto a revisar: esta rama, el commit congelado que la contiene, los siete
cuerpos con los hashes anteriores, el ZIP de transporte y el notebook. Ataques
intentados: escala constante, sobre-reescalado, núcleo de Fourier, extremos,
orden de cuantificadores, cancelación de volumen, dependencia de constantes y
supuestos que equivalen a la conclusión. Clasificación de esta ejecución:
**FAIL**. Certificación terminal: **pendiente de otra tarea**.
