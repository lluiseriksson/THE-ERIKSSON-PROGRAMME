# Mission prompt — OC_008_gaussian_root_hessian_order

    Trabajas en `lluiseriksson/THE-ERIKSSON-PROGRAMME`.

    ## Proof card

    `proof.gaussian.root.localization-certificate`

    ## Misión única

    Source-feed Gaussian pushforward/root localization only in the correct operator order.

    ## Source keys permitidas en el primer pase

    - `cmp116.gaussian-pushforward.2.5-2.6`
- `cmp116.localized-activity.2.7-2.10`
- `cmp95.covariance-green.bounds-source-target`
- `cmp96.one-step-covariance-law-source-target`

    ## Target shape

    ```text
    Hessian/coercivity -> covariance -> root -> map(dmu0, gaussianRootMap root) = physicalGaussian.
    ```

    ## Éxito mínimo

    - one dependency edge proved or source-extracted
- no root asserted before covariance identity
- Jacobian/determinant normalization tracked

    ## Rechazar si

    - Gaussian pushforward asserted from root existence alone
- scalar covariance copied into YM without field dictionary

    ## Output obligatorio

    1. Fuente exacta o blocker exacto.
    2. Declaración Lean propuesta o theorem real.
    3. Campo/hipótesis removida o reducida.
    4. Lista de hipótesis que siguen vivas.
    5. Evidencia de que no añadiste un consumidor cosmético.

    No añadas downstream wrappers salvo que un campo del contrato desaparezca o una cita se promocione con extracción real.
