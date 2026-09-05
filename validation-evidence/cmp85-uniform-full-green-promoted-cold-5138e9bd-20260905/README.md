# F4 promoted uniform scalar full-Green amplitude — cold PASS

Source: `5138e9bd4bc88797c91c21df5bb5c630c71600ca`.
Runner: `96fa32b3dcb6b4bbf6a9eedc40f12c8f5c178450`.
Launcher: `63374ffc7e910d56ceb5eefb54779a4be0662556`.
Colab host `d478f8d6ded8`, CPU/high RAM, opened 2026-09-05T09:37:49.640007Z.
No project `.lake/build` restoration. Same checkout for focal and audits.

The cold graph finished exit0 in 2947.9569665789995 seconds. The independent
remote verifier finished exit0; after download, the same pinned verifier
independently checked all 20 stages locally and returned exit0. No local
Lean/Lake was used and no compilation was repeated for evidence transport.

| Child | Exit | Seconds |
|---|---:|---:|
| normalization_focal | 0 | 48.25389794199964 |
| normalization_audit | 0 | 7.640686002999701 |
| hybrid_focal | 0 | 2045.9754301259995 |
| hybrid_audit | 0 | 7.868090996999854 |
| uniform_focal | 0 | 670.1914135269999 |
| uniform_audit | 0 | 12.46231885799989 |

Eight exact public audit declarations, each with only and exactly
{Classical.choice, Quot.sound, propext}. Three production outputs were
materialized. Audit commands did not use `-o`; no audit output is claimed.

Hashes of preserved raw bytes:

- Outer tar (61420 bytes): `31210e330e32f5a361a67d2fb7840f6371dc9bbe2aa6d1d720a7b0d10fd698c5`.
- Inner archive: `763b8dd2c621de31c9c2f828266226f394f99e058251f9356a30cb8a97e6488a`.
- Evidence JSON file: `8ebd2808b8d67de3e7d9fde4340d85200d5442012f55848352d8483e3c888090`.
- Evidence JSON payload: `2f1dbc6d56cfb16fb1d650bcc0609c2fb71d0fed243769defd535997399a61e2`.
- Raw cold graph log: `3ab0d5f58827944c029f02ca3267f763d9371f40e54b07856b7cf61397d5a88c`.
- Raw archive verifier log: `dcfe4e147b65476e6cf68e6bd2cc05de507fe4fc3de3d33c728c7d5934f7a57d`.

Verification (downloaded LF scripts and helpers):

```text
python f4-promoted-cold-launch/verify_cmp85_uniform_full_green_promoted_cold.py --helpers f4-promoted-cold-launch --archive hrpoly-cmp85-uniform-full-green-promoted-cold-v1-evidence.tar.gz --sha256 763b8dd2c621de31c9c2f828266226f394f99e058251f9356a30cb8a97e6488a
```

Scope: fixed a>0,L>=2; positive rho,C chosen before every depth j;
literal full-Green scalar owner amplitude at most C R^-2, R=L^(j+1).
Not regional/derivative B0, not window15 attainment, not a root aggregate
build. Counters 20/41 and TermSource=0 remain unchanged.
Runtime retained temporarily for the separately labelled bounded F5 hot
diagnostic and evidence transfer; shutdown is recorded in continuity.
