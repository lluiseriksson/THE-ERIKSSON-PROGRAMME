# Mission prompt — OC_006_eq237_two_premise_boundary

    Trabajas en `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

    ## Proof card

    `proof.eq237.fixed-z0prime-source-estimate`

    ## Misión única

    Extract Eq. (2.37) as two source premises: fixed-Z0' estimate and final summation, then feed existing post-P consumer.

    ## Source keys permitidas en el primer pase

    - `cmp116.eq237.post-p-resummation`
- `cmp116.constants.c3-alpha5`
- `crosswalk.eq237.combined-postp-route`

    ## Target shape

    ```text
    heq237_fixed + hpost_eq237 -> CMP116PostPResidualSourceBound.
    ```

    ## Éxito mínimo

    - two premises are exact and source-supported
- Z0/Z0' dictionary stated
- O(1) constants remain distinct or are majorized by theorem

    ## Rechazar si

    - unsupported split beyond paragraph order
- O(1) constants collapsed by naming
- D/P/Z0/Z0' dictionary omitted

    ## Output obligatorio

    1. Fuente exacta o blocker exacto.
    2. Declaración Lean propuesta o theorem real.
    3. Campo/hipótesis removida o reducida.
    4. Lista de hipótesis que siguen vivas.
    5. Evidencia de que no añadiste un consumidor cosmético.

    No añadas downstream wrappers salvo que un campo del contrato desaparezca o una cita se promocione con extracción real.
