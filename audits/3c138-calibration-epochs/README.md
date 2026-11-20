# A certificate for the VLA 3C 138 correction table

This audit quantifies how closely the monthly corrections can be represented by one time-dependent amplitude and fixed band factors. Over all 47 months and eight bands the minimum worst proportional error is 0.28941622. Allowing successive band profiles gives a minimum of six contiguous profiles at 5% tolerance.

In Linux with NumPy and SciPy, run `python static-shape.py` and retain the resulting `/content/archive.zip` before running `python epochs.py`, which writes to the same location. The expected outputs are `certificado.json` and `epocas.json`. Static factors there minimize symmetric log error; divide their product by the hyperbolic cosine of the reported log optimum for ordinary relative error. The piecewise factors in `epocas.json` already use the ordinary relative-error convention. Different optimizers may return equally optimal profiles. Check achieved errors, endpoint certificates and segment counts.

Input SHA-256: ea19cb5f3152e2c4d1514afb9bffe737a77a970b7ee26b664c0bf0a2bd58565e. The analysis measures representation error in the published corrections, including where these are interpolated. The supplied factors concern only the tabulated epochs.

[Observing guide and original table](https://science.nrao.edu/facilities/vla/docs/manuals/obsguide/calibration) · [Outburst study](https://doi.org/10.1093/mnras/stag2220)
