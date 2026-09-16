# Physical real-slice HOT v1 — first error preserved

Draft source `e833ec7e7e52ce4dbb1431777e715039ae567c23`.
Runner `5e65c2d0e79e26a1e8e070f9dfc8f08351e16aa7`,
SHA256 `617f1a65e6ede2ff92c239ef05f2513bd67d17e4d963db3db268225bdab97817`.
One launch,PID32696,2026-09-05T12:44:45.646877+00:00, retained F5 runtime.
Cold parent archive97192a7e32c99c02e7663808019f9be149a075f24112ee4848d3af5b060fd18d.

Downloaded archive SHA256:
`15017c71e8b58582af23503bfde8b414af00fdddd1a097bd1eb417df8cbbf620`.
Independent read-only verifier accepted FAIL:12 files,7 stages,0 public
axioms. Physical prerequisites and actual physical draft were NOT RUN.

First error, mathlib_carrier_repro,exit1,4.967040919000283s:

```text
tmp/SourceFlowPhysicalCarrierRepro.lean:15:2: error: 'change' tactic failed, pattern
  f (e.symm (e x)) = f x
is not definitionally equal to target
  (ContinuousLinearEquiv.piCongrLeft ℂ (fun x => ℂ) e) f (e x) = f x
```

The existing Step7b carrier module uses explicit unfolding for this API.
Any repair remains PRE-VALIDATION until remote compilation. Cold F5 PASS
is unchanged;20/41,TermSource0,window15 unattained.
