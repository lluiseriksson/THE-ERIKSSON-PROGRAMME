# Fechas ausentes y orden de los proveedores de modelos

Medimos cuántos destinatarios distintos aparecen vinculados a cada proveedor en relaciones dirigidas de suministro establecido de modelos. La ventana comprende noviembre de 2022 a octubre de 2026, ambos incluidos. Son destinatarios documentados en la muestra. Interpretar el recuento como cuota de mercado requeriría información sobre ventas o uso.

De 463 filas de esta capa sin fecha interpretable, 450 satisfacen además los requisitos de dirección, nombres y fuente. Hay 4.446 filas elegibles con fecha dentro de la ventana y 176 fuera. Se buscó la misma URL en todas las filas fechadas del conjunto antes de considerar indeterminada su pertenencia a la ventana. Todas las filas opcionales de una misma URL reciben la misma decisión. Se obtienen 198 documentos opcionales con nombres separados y 197 con la agrupación, después de excluir relaciones de una entidad consigo misma. URLs distintas podrían corresponder a material sindicado.

| Tratamiento | Ventaja con todas fuera / todas dentro | Extremos de la ventaja en asignaciones coherentes | Mínimo de URLs dentro para empate / victoria del rival |
|---|---:|---|---|
| Nombres separados, todos los hosts | Anthropic sobre OpenAI +20 / +25 | Anthropic tiene al menos 171 destinatarios y cada rival a lo sumo 160 | Imposible / imposible |
| Nombres separados, omitir anthropic.com | Anthropic sobre OpenAI +4 / +9 | −2 y +15 | 4 / 5 |
| Cinco etiquetas seleccionadas de Alphabet agrupadas en ambos extremos, todos los hosts | Anthropic sobre el grupo +3 / +9 | −4 y +16 | 3 / 4 |
| Misma agrupación, omitir anthropic.com | Grupo sobre Anthropic +13 / +7 | 0 y +20 | 9 / imposible |

El mínimo cuenta documentos asignados dentro, dejando fuera los demás opcionales. Con nombres separados y sin anthropic.com, cuatro documentos dan 155 a 155 y cinco dan 156 para OpenAI frente a 155 para Anthropic. La elección de incluir todas las fuentes sin fecha o excluirlas todas habría ocultado ese cambio de líder. Para la última fila, una asignación de nueve documentos produce 166 a 166 y ninguna permite una victoria estricta de Anthropic.

**Cómo se comprueban los extremos.** El numerador de cada proveedor es el tamaño de la unión de conjuntos de destinatarios. Para maximizar una diferencia se pueden incorporar primero los documentos que sólo añaden cobertura favorable y descartar los que ya sólo pueden aumentar la cobertura del rival. Se enumeran las decisiones restantes y se reconstruyen los testigos. Una segunda implementación calcula el coste mínimo de alcanzar cada pareja de conjuntos cubiertos, decidiendo para cada documento si entra o queda fuera. Para buscar empates o victorias mínimas del rival basta considerar documentos que podrían añadir un destinatario suyo. Se visitaron 256, 256 y 1.024 estados finales en las tres comparaciones con dos candidatos. Los recuentos de los testigos se reconstruyeron desde las filas originales. La primera implementación incluye 63 comparaciones con enumeración completa en ejemplos pequeños.

**Interpretación.** Los extremos cuantifican las clasificaciones compatibles con el campo de fecha incompleto de esta versión del conjunto. Asignar una URL a la ventana para construir un testigo aporta una posibilidad lógica. Determinar su fecha histórica exige evidencia primaria del documento. Las cinco etiquetas son una convención explícita de agrupación. El resultado es un suplemento posterior al manuscrito integrado y está pendiente de evaluación editorial propia.

Fuente primaria y datos fijados para reproducción: [Cen et al., versión 1](https://arxiv.org/html/2611.24927v1) y [revisión del conjunto de relaciones](https://huggingface.co/datasets/sarahcen/ai-supply-chain/tree/e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb). Los programas verifican el SHA-256 del archivo de entrada. Los archivos JSON contienen recuentos, extremos y testigos.
