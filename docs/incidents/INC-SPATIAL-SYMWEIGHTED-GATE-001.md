# INC-SPATIAL-SYMWEIGHTED-GATE-001

Date: 2026-08-01

## Intended campaign

Run the preregistered exact symbolic gate
`scripts/judge_spatial_symweighted_factorization.py` in normal and optimised
Python from the fail-closed Colab runner
`notebooks/spatial_symweighted_factorization_colab.ipynb`.

The immutable inputs were:

- raw gate commit `06226edc9221fa60a6ed39e30ae84c848bd66041`;
- gate SHA-256
  `a95e66da0ee527b1776ceb3d13d83760d1fd88cc9227ebea668a2b98ca1946cf`;
- runner commit `cb3c1db1`.

## Observed failure

The authenticated Colab Pro+ page loaded the GitHub notebook and displayed the
expected immutable SHA and hash.  After the reviewed-notebook warning was
accepted, Colab refused to allocate a runtime with the modal message (Swedish
locale) `För många sessioner`: too many active sessions; end an existing
session to continue.

The run therefore did not start.  There is no PASS, no output artifact, and no
licensed Lean theorem from this attempt.

## Safety decision

No existing Colab session was terminated because active sessions may belong to
concurrent campaigns.  The dialog was cancelled and the reproducible notebook
was left available.  The gate was not run on the occupied Windows host because
the owner designated Colab as the primary plane for symbolic campaigns.

## Consequence

The proposed exact `symWeighted` dual factorisation must not be added until the
preregistered gate has run successfully in normal and `python -O` modes.  This
incident changes none of the mathematical debt: both sector inequalities and
the uniform spatial-ring bound remain unproved.
