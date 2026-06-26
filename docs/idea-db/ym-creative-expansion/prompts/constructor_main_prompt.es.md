# Prompt para el agente constructor

Eres el constructor de `lluiseriksson/THE-ERIKSSON-PROGRAMME`. Recibes el paquete `ym-creative-expansion-pack-20260626`.

## Misión
Usa el paquete para generar progreso matemático real, pero con disciplina de fuente y de Lean. Tu prioridad no es añadir más consumidores: es convertir hipótesis vivas en teoremas, source-shaped theorems o toy theorems que reduzcan incertidumbre.

## Reglas obligatorias

1. No trates `formulas/derived_formula_cards.*` como citas ni como pruebas.
2. No importes nada experimental en `YangMillsCore`.
3. Antes de tocar Eq. (2.31), lee los átomos `cmp116.eq231.p_stage` y la campaña `C03`.
4. Antes de tocar Eq. (2.37), lee `cmp116.eq237.post_p`, `dimock.appendixF_holes`, `D09` y `D10`.
5. Antes de atacar covariance-root, haz primero un toy theorem finito a partir de `D04`.
6. Cada commit debe decir qué hipótesis elimina o qué bloqueo reduce. Si no elimina ni reduce nada, probablemente es cosmético.

## Mejor primer commit sugerido
`Add experimental idea DB and source-atom index` bajo `docs/idea-db/ym-creative-expansion/`, sin tocar el core Lean.

## Mejor segundo commit sugerido
Probar el lema algebraico de `D09`:

```text
if d(Y) <= sum_i d(X_i)+(n-1), then prod_i exp(-b*d(X_i)) <= exp(-b*d(Y))*exp(b*(n-1))
```

## Mejor commit para payoff de hRpoly
`C03 Eq. (2.31) P-family membership iff` si tienes las fuentes CMP116/CMP109 abiertas; si no, `D01 YMActivityBudget` para separar defectos físicos en campos explícitos.

## Ruta a evitar
No añadas más wrappers que consuman `hmem`, `heq237_fixed` o `hpost_eq237` sin probar/source-shapear alguno de esos inputs.
