# Mission prompt — OC_001_eq231_source_subset_gapCarrier

    Trabajas en `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

    ## Proof card

    `proof.eq231.membership-iff.source-package`

    ## Misión única

    Discharge only the source_subset_gapCarrier field of CMP116Eq231BalabanPFamilySourcePackage, preferably through the existing base-cube projection reducer.

    ## Source keys permitidas en el primer pase

    - `cmp116.eq231.p-family-carrier-source-target`
- `cmp109.bond-convention.positive-oriented`
- `crosswalk.eq231.p-family-source-dictionary-route`

    ## Target shape

    ```text
    sourceAdmissible Z D P -> P subset gapCubes Z D × Fin 4, or the smaller premise forall b in P, b.1 in gapCubes Z D feeding cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes.
    ```

    ## Éxito mínimo

    - new source-extracted or source-shaped theorem for base-cube ownership
- one caller no longer supplies hPcarrier manually, or the exact remaining field is smaller
- proof card updates remaining fields

    ## Rechazar si

    - admissible is defined as decide(P in PIndex Z D)
- CMP109 is cited as the CMP116 carrier theorem
- lower bound on |P| is used as carrier upper bound
- new downstream wrapper added with all old hypotheses still present

    ## Output obligatorio

    1. Fuente exacta o blocker exacto.
    2. Declaración Lean propuesta o theorem real.
    3. Campo/hipótesis removida o reducida.
    4. Lista de hipótesis que siguen vivas.
    5. Evidencia de que no añadiste un consumidor cosmético.

    No añadas downstream wrappers salvo que un campo del contrato desaparezca o una cita se promocione con extracción real.
