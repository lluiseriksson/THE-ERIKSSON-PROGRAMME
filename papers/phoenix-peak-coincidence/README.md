# Reproducing the Phoenix peak-hour comparison

On a Linux Colab runtime with Python and openpyxl, run `python peak-hour.py`. It downloads the three original trial inputs and the January–June 2025 EIA-930 balance file, verifies SHA-256 and writes `/content/phoenix-peak-hour.zip`. Its result.json should equal daily-peak-hour.json. An existing ZIP must be preserved before rerunning in a new runtime. The output records start- and end-labeled minutes and the unnormalized mean of each window.

The 48 original EIA hourly observations, the grid-only comparison and provenance are recorded in eia-compare.json. The recorded input hash identifies the historical file; a revised EIA export requires an explicitly identified new analysis. The workbook comparison reports the full row reconciliation. Upstream data and the papers/slides remain with their publishers. The PDF can be built with pdfLaTeX and the standard LaTeX recommended and lmodern packages.
