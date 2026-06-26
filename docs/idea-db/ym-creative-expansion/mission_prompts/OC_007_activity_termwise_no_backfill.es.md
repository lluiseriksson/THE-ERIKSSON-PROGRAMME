# Mission prompt — OC_007_activity_termwise_no_backfill

    Trabajas en `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

    ## Proof card

    `proof.activity.termwise-identification`

    ## Misión única

    Identify H(Z) summands and termwise estimates before final Lemma 3 summation.

    ## Source keys permitidas en el primer pase

    - `cmp116.localized-activity.2.7-2.10`
- `cmp116.lemma3.window.2.14-2.38`
- `crosswalk.gaussian-root-activity-route`

    ## Target shape

    ```text
    physicalActivity.globalEval = source H term and norm <= termWeight.
    ```

    ## Éxito mínimo

    - source finite-sum dictionary extracted
- termwise estimate precedes final bound
- remaining physical construction blockers explicit

    ## Rechazar si

    - final Eq. (2.38) used to prove termwise estimate
- physical activity asserted equal without dictionary

    ## Output obligatorio

    1. Fuente exacta o blocker exacto.
    2. Declaración Lean propuesta o theorem real.
    3. Campo/hipótesis removida o reducida.
    4. Lista de hipótesis que siguen vivas.
    5. Evidencia de que no añadiste un consumidor cosmético.

    No añadas downstream wrappers salvo que un campo del contrato desaparezca o una cita se promocione con extracción real.
