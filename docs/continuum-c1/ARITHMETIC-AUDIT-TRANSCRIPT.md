# CONTINUUM-C1 arithmetic audit transcripts

## KP beta cap

- Command:
  `python scripts/continuum_c1_beta_cap_audit.py`
- Python: 3.12.13
- Script SHA-256:
  `13CFDFAF610445630C47E431B0518955A846D129BFA2B26B57B2E678C1D2BFD3`
- Classification: VERIFIED binary64 diagnostic; not a proof.

```json
{
  "formula": "log1p(exp(-3)/(16*d+1)^2)/Nc",
  "rows": [
    {"dimension": 4, "colors": 3, "beta_cap": "3.927950692443e-06"},
    {"dimension": 4, "colors": 2, "beta_cap": "5.891926038665e-06"},
    {"dimension": 3, "colors": 2, "beta_cap": "1.036787842219e-05"}
  ]
}
```

The Lean theorem, rather than this binary64 computation, proves the cap.

## Auxiliary Haar arithmetic, exactly β = 0

- Command:
  `python scripts/continuum_c1_tail_audit.py --nc 2 --a-num 1 --a-den 10 --radius 1000`
- Python: 3.12.13
- Script SHA-256:
  `D044D87C8E29B0ABF67FCF3A562BE22EEE344F055A9B69ED6D141BC33EA06438`
- Classification: VERIFIED arithmetic diagnostic; not a proof.

```json
{
  "classification": "VERIFIED arithmetic diagnostic; not a proof",
  "identity_check": "Nc/2 + (3*Nc/2)*(1/3) = Nc",
  "inputs": {
    "a": "1/10",
    "compact_radius": 1000,
    "nc": 2
  },
  "python": "3.12.13",
  "tail_mass_lower_bound": "1/3",
  "tail_threshold": "10000/1",
  "threshold_strictly_outside_compact": true
}
```

No randomness, external package, credential, network call, or Colab runtime
is involved. This diagnostic says nothing about any `β>0` law; see
`HAAR-BETA-ZERO-APPENDIX.md`.
