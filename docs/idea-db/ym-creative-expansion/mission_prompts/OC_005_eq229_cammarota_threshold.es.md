# Mission prompt — OC_005_eq229_cammarota_threshold

    Trabajas en `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

    ## Proof card

    `proof.eq229.cammarota-dstage-summability`

    ## Misión única

    Extract Cammarota CMP85 theorem and map its smallness threshold to CMP116 Eq. (2.29) D-family summability.

    ## Source keys permitidas en el primer pase

    - `cmp116.eq229.d-stage-summability`
- `cmp109.ref26.cammarota-infinite-range-cluster`
- `cammarota.cmp85.polymer-mayer-source-target`
- `crosswalk.eq229.cammarota-dstage-route`

    ## Target shape

    ```text
    sum_D prod_Y alpha6*exp(-delta*kappa*d_k(Y)) <= 1 under explicit thresholds.
    ```

    ## Éxito mínimo

    - theorem statement and constants extracted
- DIndex/DParts dictionary remains explicit if unresolved
- no bibliographic-only citation as theorem

    ## Rechazar si

    - sufficiently large/small converted to constants without source
- Cammarota reference list used as theorem text

    ## Output obligatorio

    1. Fuente exacta o blocker exacto.
    2. Declaración Lean propuesta o theorem real.
    3. Campo/hipótesis removida o reducida.
    4. Lista de hipótesis que siguen vivas.
    5. Evidencia de que no añadiste un consumidor cosmético.

    No añadas downstream wrappers salvo que un campo del contrato desaparezca o una cita se promocione con extracción real.
