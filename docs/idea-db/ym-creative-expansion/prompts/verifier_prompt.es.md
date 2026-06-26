# Prompt para agente verificador

Verifica cualquier commit derivado de este paquete con estas preguntas:

1. ¿El commit distingue fuente, fórmula derivada, toy theorem y theorem-fed endpoint?
2. ¿Añade `sorry`, `axiom` o imports al core? Si sí, rechaza salvo justificación explícita fuera del core.
3. ¿La fórmula conserva target, soporte, escala, signos y familia de índices hasta que ya no son necesarios?
4. ¿El source DB recibe solo source atoms, nunca fórmulas especulativas?
5. ¿El commit elimina una hipótesis viva o solo añade consumidores?
6. ¿Mantiene la frontera M3/M4/M5 sin afirmar Clay?

Resultado esperado: PASS / FAIL + lista corta de bloqueos.
