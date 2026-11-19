# ¿A quién cuenta como destinatario una arista de provisión?

Se partió de tres artículos académicos del testigo de cinco URLs empleado en el análisis inicial de fechas. En las relaciones dirigidas de provisión establecida de la capa de modelos, esos tres artículos aportan cuatro filas que parten de OpenAI y tres etiquetas de destino distintas. La consulta se hizo por documento y pudo devolver tanto filas repetidas como múltiples destinos. Para estos tres pares no se encontró otra URL fechada inicialmente dentro de la ventana después de excluir anthropic.com.

| Artículo | Etiqueta de destino extraída | Interpretación comprobable |
|---|---|---|
| [Scientific Reports, 5 de diciembre de 2024](https://www.nature.com/articles/s41598-024-79705-4) | `dall-e` | El estudio usa DALL-E 2 como herramienta para generar imágenes. Esta etiqueta identifica el modelo. Contarla como destinatario económico distinto de OpenAI introduciría un error de categoría. |
| [Journal of Clinical Medicine, 21 de marzo de 2025](https://www.mdpi.com/2077-0383/14/7/2136) | `the study authors` (dos filas) | El estudio documenta el uso de DALL-E 3. La etiqueta omite la identidad de los autores. Las dos filas aportan un único destino al recuento por nombres. |
| [Frontiers in Plant Science, 21 de febrero de 2025](https://www.frontiersin.org/journals/plant-science/articles/10.3389/fpls.2024.1468676/full) | `yavuz selim şahin, nimet sema gençer, and hasan şahin` | La cadena corresponde a la firma de un equipo. Puede fundamentar una unidad de observación de usuarios si se define así. La firma por sí sola no acredita un contrato de suministro institucional. |

**Efecto medible.** Tras fijar las 18 fechas, el par OpenAI → dall-e aparece en todo escenario porque el primer artículo está dentro de la ventana. Excluir sólo ese par de una medida de destinatarios económicos reduce en una unidad el grado de OpenAI y deja intacto el de Anthropic. Con nombres separados y sin anthropic.com la ventaja de Anthropic pasa del conjunto {6, 7, 8, 9, 10} a {7, 8, 9, 10, 11}. Esta sensibilidad procede de una corrección comprobada. Las demás relaciones todavía pueden requerir correcciones en cualquiera de los dos sentidos.

**Alcance.** Los resultados de clasificación publicados en este suplemento corresponden al grafo de etiquetas del conjunto. Esta lectura de tres artículos refuta la interpretación de todas esas etiquetas como clientes distintos. La selección dirigida a documentos capaces de alterar el orden impide estimar la frecuencia del problema en el conjunto entero.

[Filas extraídas](article-rows.json) · [Consulta reproducible](article-rows.py) · [Análisis de fechas](orden-con-fechas.md).
