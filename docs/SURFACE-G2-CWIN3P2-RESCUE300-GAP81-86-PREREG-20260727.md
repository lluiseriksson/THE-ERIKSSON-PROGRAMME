# G2 rescue-300 gap `[81,86]` — preregistration

**Registered:** 2026-07-27, before any result from this lane is read.

## Purpose

Repair the genuine `[81,86]` gap reported by the corrected authoritative
relay audit (`INCIDENT-G2-AUDIT-BETA-HI-20260727.md`).  This lane is an
independent current-contract production/replay campaign.  It carries no
promotion by itself; only a later role audit may assign theorem load.

## Frozen contract

- runner: `run_surface_scaled_bulk_cwin3p2_rescue300.py`
- `CWIN=3/2`, beta Taylor order 40, t order 50, Arb precision 300 bits;
  `MIN_DT=1/100000`;
- each unit covers `t=[3/5, PI_UP-3/(2*beta_hi)]`, with outward rounding;
- production and replay must be byte-identical and pass the independent
  rescue-300 validator;
- no unit may be split or widened after its result is observed.  If a unit
  fails, the failure is recorded and the next width is not inferred.

## Fixed beta partition

The twenty adjacent rational units are

```text
[81,81+1/4], [81+1/4,81+2/4], [81+2/4,81+3/4], [81+3/4,82],
[82,82+1/4], [82+1/4,82+2/4], [82+2/4,82+3/4], [82+3/4,83],
[83,83+1/4], [83+1/4,83+2/4], [83+2/4,83+3/4], [83+3/4,84],
[84,84+1/4], [84+1/4,84+2/4], [84+2/4,84+3/4], [84+3/4,85],
[85,85+1/4], [85+1/4,85+2/4], [85+2/4,85+3/4], [85+3/4,86].
```

The exact rational endpoints, not decimal aliases, are passed to the runner.
Each successful unit remains `current-candidate` until the corrected relay
audit and the contract owner explicitly review it.
