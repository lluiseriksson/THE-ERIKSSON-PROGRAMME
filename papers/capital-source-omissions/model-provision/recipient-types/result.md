# Qué ocurre al exigir que el destinatario sea una empresa según el registro

Se mantuvieron la ventana de noviembre de 2022 a octubre de 2026, las dieciocho fechas recuperadas, las reglas de agrupación y las decisiones por URL. La única modificación fue exigir que el destinatario orientado tuviera la etiqueta COMPANY en al menos una fila que respalda el par. En un control adicional se exigió que en la misma fila el proveedor también tuviera esa etiqueta.

| Definición de nombres y fuentes | Con todos los tipos de destinatario | Con destinatarios de tipo COMPANY |
|---|---|---|
| Separados, todos los hosts | Anthropic por 22 a 26 | Anthropic por 1 a 4 |
| Separados, sin anthropic.com | Anthropic por 6 a 10 | OpenAI por 3 a 6 |
| Agrupados, todos los hosts | Anthropic por 6 a 10 | Grupo Alphabet seleccionado por 7 a 9 |
| Agrupados, sin anthropic.com | Grupo Alphabet seleccionado por 6 a 10 | Grupo Alphabet seleccionado por 9 |

Cada margen se mide contra el segundo proveedor del recuento correspondiente. Todos los enteros de los intervalos son alcanzables asignando las URLs pendientes dentro o fuera del período. Se recalculó el conjunto de posibles líderes y segundos en cada configuración. Para ello, se conservaron todos los proveedores cuyo máximo alcanzaba el segundo mayor grado ya garantizado. Los excluidos quedan por debajo de al menos dos proveedores en toda asignación. Sólo hace falta enumerar las URLs que pueden aumentar el grado de alguno de los incluidos. Se reprodujeron las cuatro configuraciones publicadas sin filtro. Exigir COMPANY también en el extremo proveedor produjo los mismos líderes y márgenes que exigirlo únicamente en el extremo destinatario.

**Mecanismo de la inversión.** Con nombres separados, sin anthropic.com y dejando fuera las URLs aún sin fechar, Anthropic pasa de 166 etiquetas de destino a 99 y OpenAI de 159 a 105. El filtro quita 67 destinos a Anthropic y 54 a OpenAI. Esa diferencia de 13 transforma una ventaja de siete para Anthropic en una ventaja de seis para OpenAI. La incertidumbre de fecha restante puede reducir la ventaja de OpenAI a tres, pero conserva el primer puesto.

**Qué significa la etiqueta.** El propio conjunto clasifica el destino DALL-E como NOT_AN_ACTOR y a los autores de los otros dos artículos auditados como PERSON. El recuento anterior incluía todos esos tipos. Sería incorrecto atribuir al clasificador una identificación de DALL-E como empresa en esa fila. El contraejemplo afecta a la interpretación que se dé al recuento sin filtro. La etiqueta COMPANY también es un dato extraído y no acredita que se celebrara un contrato o que hubiera ingresos.

[Estudio de origen](https://arxiv.org/abs/2611.24927v1) · [Revisión de los datos](https://huggingface.co/datasets/sarahcen/ai-supply-chain/tree/e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb).
