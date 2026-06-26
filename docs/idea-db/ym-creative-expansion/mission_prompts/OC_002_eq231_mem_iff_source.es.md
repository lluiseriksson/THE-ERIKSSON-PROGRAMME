# Mission prompt — OC_002_eq231_mem_iff_source

    Trabajas en `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

    ## Proof card

    `proof.eq231.membership-iff.source-package`

    ## Misión única

    Extract the exact source definition of Balaban's P family and prove/state mem_iff_source without using the filtered Lean family as definition.

    ## Source keys permitidas en el primer pase

    - `cmp116.eq231.p-family-carrier-source-target`
- `crosswalk.eq231.p-family-source-dictionary-route`

    ## Target shape

    ```text
    P in PIndex Z D <-> sourceAdmissible Z D P.
    ```

    ## Éxito mínimo

    - sourceAdmissible has explicit source fields
- mem_iff_source is theorem-shaped
- remaining source_subset/admissible fields are listed

    ## Rechazar si

    - sourceAdmissible is just P ∈ PIndex
- proof uses cmp116Eq231SourcePIndex_mem_iff as source evidence

    ## Output obligatorio

    1. Fuente exacta o blocker exacto.
    2. Declaración Lean propuesta o theorem real.
    3. Campo/hipótesis removida o reducida.
    4. Lista de hipótesis que siguen vivas.
    5. Evidencia de que no añadiste un consumidor cosmético.

    No añadas downstream wrappers salvo que un campo del contrato desaparezca o una cita se promocione con extracción real.
