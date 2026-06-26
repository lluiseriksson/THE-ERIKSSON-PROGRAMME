# LLM fast-context update — Batch 006

Batch 006 adds a live-field map for the Gaussian/root/Hessian/activity/H# stack.

## What changed

- Added `gaussian-root-hessian-live-fields.json`.
- Added ordered field cards for `BalabanCMP116SourceAssumptions`.
- Added prompts for covariance/root, Gaussian pushforward, root localization, Wilson Hessian, local activity, termwise estimate and rooted H#.
- Added guards preventing final Lemma 3 or H# estimates from backfilling upstream source fields.

## Read first

```powershell
python scripts\source_db.py show proof.rawsource.m3.live-fields.v2
python scripts\source_db.py show proof.gaussian.covariance-root-certificate.v2
python scripts\source_db.py show proof.rooted-hsharp-remainder.identity.v2
```

## Main invariant

```text
final bound / H# identity != proof of Gaussian/root/Hessian/source dictionary
```
