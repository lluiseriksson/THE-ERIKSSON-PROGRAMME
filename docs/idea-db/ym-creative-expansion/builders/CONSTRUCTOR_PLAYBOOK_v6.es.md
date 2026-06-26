# Constructor playbook v6

## Objetivo

Convertir el Batch 006 en una cola ejecutable de commits pequeños.  No mezcles
Eq. (2.31) con Gaussian/root/Hessian salvo que la dependencia sea solo un
blocker documentado.

## Workflow

```bash
python scripts/field_board.py --order
python scripts/batch006_prompt_compiler.py covariance_root_certificate
python scripts/generate_patch_intake.py OC_016_covariance_root_certificate_dictionary > patch_intake/oc016.json
python scripts/check_no_backfill.py patch_intake/oc016.json
python scripts/score_patch_intake_v6.py patch_intake/oc016.json
```

## Regla de oro

Un patch debe eliminar exactamente un campo, promocionar una fuente con evidencia,
probar un theorem skeleton útil o afilar un blocker.  Si solo añade wrappers,
recházalo.
