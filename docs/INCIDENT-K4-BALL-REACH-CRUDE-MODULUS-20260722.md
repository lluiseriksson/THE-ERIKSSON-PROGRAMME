# Incident: K4 regular-ball crude Cauchy reach fails

**Date:** 2026-07-22  
**Prerequisite:** `SURFACE-K4-BALL-REACH-PROBE-PREREG-20260722.md`  
**Git head:** `ac5699741d1bfab328834e2bd72824791fc679d9`  
**Probe SHA-256:** `56471767B403729C4A528940030B7999119C9D9B15AB706A7EAC6A19D282F04E`  
**Driver SHA-256:** `142FB146FA7F724D361CE91740E4138F417BB2DE326A9AABABC37BB5D1A3D33B`

The fixed probe parameters were `rho=7/100`, `R=4`, `Phi=4*pi`,
`r=59/2000`, and degree cap `N<=16`.  It returned

```text
M_nuD_crude  ~7.507188691690812e321
best_N=16    tail2 ~9.326128920146840e318
headroom_half ~0.3621
K4 BALL REACH FAIL
```

This is a terminal failure of the registered *crude hyperbolic-sine modulus*
architecture, not a disproof of K4.  The regular-ball route would need a
substantially sharper complex exponential modulus (and still the moving-tail
and t-uniform certificates) before another production attempt is justified.
The probe output is archived in
`scripts/surface_k4_ball_reach_probe_20260722.txt`; no K4/G6 promotion follows.
