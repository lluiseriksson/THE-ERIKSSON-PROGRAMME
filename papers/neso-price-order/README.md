# Prices and unused volume in Britain's demand flexibility auctions

Run `python reproduce.py` from any directory in a Linux reproduction environment. Python's standard library is sufficient. The script verifies SHA-256 for three archived CSVs, joins records by event, delivery date, UTC endpoints and direction, and prints the summary and all 206 price intervals. It runs without internet access. The archives also contain summaries from the initial Colab extraction.

Supported by National Energy SO Open Data. The CSVs remain under the [National Energy SO Open Data Licence v1.0](https://www.neso.energy/data-portal/neso-open-licence). The [operator dataset](https://www.neso.energy/data-portal/demand-flexibility) identifies the source resources and their licence. The paper and analysis do not imply endorsement by NESO. Publicly posted price and volume can describe decisions without revealing the operator's counterfactual valuation.

The contemporaneous protocols distinguish the frozen cohort, signed settlement amendment, bid reconciliation, within-zone tests and unrestricted threshold diagnostic. The archives preserve the original data snapshot even when the portal changes.
