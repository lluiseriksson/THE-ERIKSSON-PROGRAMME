# Documentary source omissions in AI investments

The source data are retrieved from the pinned Hugging Face revision in each script. The input remains under the dataset publisher's CC BY-NC-SA 4.0 licence. The repository does not include the upstream Parquet file. Each analysis script is meant to run in a fresh, dedicated Linux Colab runtime with /content available. Each downloads and hashes the original data. The solver-free checker embeds the certified host evidence and the explicit witness, so it can run by itself. It uses exactly the same input definitions as the generator.

- `host-certificate.py` constructs the hostname lower bound.
- `host-check.py` verifies the stored certificate and recounts the 38-host witness for every investor without an optimizer.
- `groups.py` constructs the title-date graph, verifies an integer lower bound and recounts the witness under each grouping rule. Its archive contains the components, witnesses and integer multipliers.
- `case-sensitive.py` reproduces the capitalization sensitivity and enumerates the two-host cases.

Each run prints the SHA-256 of its returned archive. See `host-audit.json` and `group-results.json` for the verified outputs. The manuscript uses the TeX files in this directory.

The extraction-agreement extension adds the same-URL pass comparison, its solver-free certificate check, the pair-retention control and the limited published alias example. Each Python program runs in a clean Colab environment. Results for these experiments are in follow-up/. The revised PDF also includes agreement.tex.

The model provision comparison uses the same public data revision. model-provision/factorial.py runs in a dedicated Colab CPU session with pandas, PyArrow and NumPy and returns factorial.json in /content/factorial.zip. Data are downloaded from the original publisher and checked by SHA-256. The predeclared groupings, per-cell single-host cases, all joint website cuts, and pair-loss and tie counts are included. The full upstream table is retrieved from its publisher. The estimate is a comparison of coverage, not market share. Source TeX for this section is provision.tex.

The document-date ledger and its URL hashes are in model-provision/source-dates.json. The scripts principal-dates.py and article-rows.py in that folder reconstruct the four ranking comparisons and three article checks. The JSON files with matching names contain the verified results.
