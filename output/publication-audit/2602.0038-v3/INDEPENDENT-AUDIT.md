# Auditoria independiente de reemplazos de titulo y alcance

Fecha de corte: 2026-07-31  
Modo: adversarial, solo lectura sobre `output/publication-audit/2602.0038-v3` y `output/publication-audit/2602.0041-v4`; los unicos ficheros escritos por esta auditoria estan bajo `tmp/publication-audit/title-replacements-independent`.

## Resultado ejecutivo

| Paquete | Resultado material | Veredicto de paquete | Motivo bloqueante |
|---|---|---|---|
| `2602.0038-v3` | El titulo, el abstract y la pagina correctiva restringen correctamente el resultado a una cota de `D(0)` para la medida cuadratica GZ simplificada. La frase de procedencia corregida es exacta. Build reproducible, verificadores O0/O1, fuentes y 11/11 paginas pasan. | **REVIEW-PENDING** | Faltan manifiesto e hipervinculo inmutable; ademas coexisten en `artifacts` el PDF vigente `4bcadc2d...` y el obsoleto `d741821c...`, sin cuarentena ni manifiesto que impida subir el incorrecto. |
| `2602.0041-v4` | El titulo dice explicitamente `A Conditional Reduction`; el abstract y la pagina correctiva mantienen H-XSD, H-DOB, la ventana de parametros y excluyen continuo/OS/Clay. La procedencia corregida es demostrable. Build reproducible, verificadores O0/O1, fuentes y 12/12 paginas pasan. | **REVIEW-PENDING** | Faltan manifiesto e hipervinculo inmutable; ademas coexisten en `artifacts` el PDF vigente `d268921d...` y el obsoleto `21bf1212...`, sin cuarentena ni manifiesto que impida subir el incorrecto. |

No se ha encontrado un defecto matematico nuevo. El bloqueo de procedencia de la primera auditoria esta cerrado: las nuevas frases describen exactamente identidad de render y de streams. Los bloqueos restantes son de completitud y seleccion inequivoca del artefacto, no del PDF vigente.

## 2602.0038-v3

### Identidad y estructura

- PDF propuesto vigente: `artifacts/2602.0038v3-4bcadc2d-11pp.pdf`.
- SHA-256: `4bcadc2d4a5ea32c5a56c12d9ca6952fbb24e8c8fcceea868b1a40b0ad70260e`.
- Tamano: 487089 bytes; 11 paginas; no cifrado; PDF 1.5.
- Pagina 1 A4; paginas 2--11 US Letter, heredadas del PDF publico. Es una irregularidad editorial P2, no un fallo de render.
- PDF publico incorporado: `2602.0038v2-public.pdf`, SHA-256 `306d2336ad3c415fce994ba20ee0488ba20739ed5002877fc7a79745c530da16`, 329374 bytes, 10 paginas. Coincide con el ledger y el censo congelado.
- Todas las fuentes del PDF final aparecen embebidas. No hay cifrado, formularios ni JavaScript.

### Alcance y ficha

- El titulo propuesto, `Zero-Momentum Propagator Bound in a Simplified Gribov-Zwanziger Lattice Measure`, coincide con la clase de claim del ledger: cota exacta del propagador en un modelo cuadratico simplificado.
- La pagina correctiva y el abstract de envio distinguen correctamente condicion necesaria de mass gap frente a prueba de clustering/gap, y excluyen Wilson Yang--Mills, limite continuo y Clay.
- No se promueven los checks numericos del manuscrito a certificado independiente.
- Categoria `Quantum Physics` y autor `Lluis Eriksson` coinciden con la ficha publica.
- Campos de envio: titulo 79 caracteres; abstract 690 caracteres/98 palabras; comments 85 caracteres/12 palabras. Son razonables.
- El nombre de fichero de `SUBMISSION-ID.txt` existe y coincide con el artefacto auditado.

### Reproducibilidad y verificacion

- Fuente `src/front_note.tex`: SHA-256 `547046d11edcb62bbede5dc202541441b6e81c594cb1343f8472672a35024786`.
- `build.py`: SHA-256 `9a2644cc467f97a055a3ae1f6882286d9997ce1dc5a640669bbc7591d62e4a68`.
- `verify.py`: SHA-256 `6efaed874669b3a90b5678578dd754c5daac804993be51f3d80722e4a1740576`.
- Dos builds consecutivas desde una copia limpia temporal produjeron exactamente el SHA final empaquetado.
- `python verify.py`: PASS; `python -O verify.py`: PASS; `PYTHON_OPTIMIZE_LEVEL` se registra como 0 y 1 respectivamente.
- No hay sentencias `assert` en los scripts Python del paquete; la comprobacion no desaparece con `-O`.
- `build-result.json`, el fichero real y el campo `FILE` de `SUBMISSION-ID.txt` coinciden en `2602.0038v3-4bcadc2d-11pp.pdf`; el hash del build-result coincide con los bytes. El estado HOLD sigue siendo coherente con los bloqueos restantes.
- Paginas finales 2--11 frente a v2: 10/10 renders pixel-identicos a 120 dpi; 10/10 streams comprimidos y 10/10 streams descomprimidos byte-identicos.
- La frase corregida de `src/front_note.tex:45-46`, `identical rendered content and unchanged page-content streams`, queda demostrada. Ya no afirma identidad de objetos de pagina.

### Inspeccion visual completa

Se inspeccionaron previamente 11/11 paginas. En la reauditoria se inspecciono a resolucion original la nueva pagina 1: no hay recortes, solapes, glifos rotos ni desbordes. Las paginas 2--11 siguen siendo pixel-identicas al input ya inspeccionado.

### Acciones minimas antes de LISTO-LOCAL

1. Retirar de la ruta activa o marcar inequivocamente como obsoleto `2602.0038v3-d741821c-11pp.pdf`; idealmente el builder debe limpiar finales antiguos del mismo paquete.
2. Anadir manifiesto con hashes de PDF vigente, input, fuente, builder, verifier, transcripts y ficha, y declarar un unico fichero de upload.
3. Completar el enlace GitHub inmutable despues del commit/push; hasta entonces la ficha debe seguir en HOLD.

## 2602.0041-v4

### Identidad y estructura

- PDF propuesto vigente: `artifacts/2602.0041v4-d268921d-12pp.pdf`.
- SHA-256: `d268921dd8fd3a1ee4b1440118692ffc53472e1c3ef84f84736b95016b1ba93d`.
- Tamano: 547537 bytes; 12 paginas; no cifrado; PDF 1.5.
- Pagina 1 A4; paginas 2--12 US Letter, heredadas del PDF publico. Irregularidad editorial P2, sin defecto de render.
- PDF publico incorporado: `2602.0041v3-public.pdf`, SHA-256 `f67dea05d521ce5ea59caf79edca8038f0eb850b5c2256282394ca665c01afbb`, 380899 bytes, 11 paginas. Coincide con ledger y censo.
- Todas las fuentes estan embebidas. Los Type 3 heredados (`F59`, `F72`, `F73`) estan embebidos y se renderizan correctamente.

### Alcance y ficha

- El titulo propuesto, `Uniform Log-Sobolev Inequality and Mass Gap for Lattice Yang-Mills Theory: A Conditional Reduction`, corrige el overclaim del titulo publico sin ocultar el tema.
- El abstract y la pagina 1 coinciden con el teorema publico: LSI depende de H-XSD; el mass gap depende adicionalmente de H-DOB o de una ruta alternativa valida que este manuscrito no verifica.
- Se conserva explicitamente la ventana cuantitativa de H-DOB y se excluyen gap incondicional, continuo, reconstruccion OS y Clay.
- Los checks numericos siguen clasificados como soporte del autor, no prueba de las hipotesis Yang--Mills.
- Categoria `Mathematical Physics` y autor coinciden con la ficha publica.
- Campos: titulo 98 caracteres; abstract 681 caracteres/84 palabras; comments 85 caracteres/12 palabras. Son razonables.
- El fichero declarado existe y coincide con el artefacto auditado.

### Reproducibilidad y verificacion

- Fuente `src/front_note.tex`: SHA-256 `4582fa1762a5f57c661afd94d1bc2cbc8e30ac877dc8a408b3b7231b6a105b20`.
- `build.py`: SHA-256 `f618f73ed51ec690e50d5ff1f4fe19662c7d5532fa0b6ba84dc1b9147cf2a85a`.
- `verify.py`: SHA-256 `cab5911e23776bf8cbf72c4b55276846101e4aae09b9e1d3f0d3b7bd69c4409c`.
- Dos builds consecutivas desde copia limpia produjeron exactamente el SHA empaquetado.
- `python verify.py` y `python -O verify.py`: PASS con niveles 0 y 1 registrados; sin `assert` funcional.
- `build-result.json`, el fichero real y `SUBMISSION-ID.txt` coinciden en `2602.0041v4-d268921d-12pp.pdf`; el hash declarado coincide con los bytes. El estado HOLD sigue siendo coherente.
- Paginas 2--12 frente a v3: 11/11 renders pixel-identicos; 11/11 streams comprimidos y 11/11 streams descomprimidos byte-identicos.
- La frase corregida de `src/front_note.tex:46-47`, `identical rendered content and unchanged page-content streams`, queda demostrada y ya no habla de identidad de objetos.

### Inspeccion visual completa

Se inspeccionaron previamente 12/12 paginas. La nueva pagina 1 fue reinspeccionada a resolucion original y no presenta recortes, solapes, pies defectuosos ni glifos rotos. Las paginas 2--12 son pixel-identicas al PDF publico ya inspeccionado.

### Acciones minimas antes de LISTO-LOCAL

1. Retirar de la ruta activa o marcar inequivocamente como obsoleto `2602.0041v4-21bf1212-12pp.pdf`; idealmente el builder debe limpiar finales antiguos.
2. Anadir manifiesto completo y declarar un unico fichero de upload.
3. Completar el enlace GitHub inmutable despues del commit/push y mantener HOLD hasta cerrar la matriz.

## Observacion sobre el veredicto

`REVIEW-PENDING` no cuestiona los recortes de alcance ni la procedencia corregida, que pasan. Impide que dos artefactos finales rivales y un paquete sin manifiesto/enlace inmutable se conviertan por inercia en `LISTO-LOCAL`.
