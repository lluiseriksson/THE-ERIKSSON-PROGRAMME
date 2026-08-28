# C6d source-separated ambient Green cold FAIL

Classification: compiler FAIL at the first focal target; no later queue stage
was executed and no mathematical PASS is claimed.

- source: `bb51db164adb7840c383a7bf2d43d42b5494588e`
- runner: `5561deb67c4df88cc9247c397e6b0939f88adec5`
- runner revision: `c6d-source-separated-ambient-green-v1`
- first failing stage:
  `01_cmp99eq360c6dsourceseparatedambientgreen_focal`
- stage exit: `1`
- stage time: `2363.744 s`
- evidence JSON SHA-256:
  `AEFEF7CA413C1313BB7B7003ABEA08448A9BB8DFB8B3DCF868C5824821BD9376`
- archive SHA-256:
  `329105A61E745A8370B162755B8DF00BF1F9EABC55377533925F0F54421F165C`
- executed notebook SHA-256:
  `38F2E9948187FC1EEA2B31CFFCE78CE624B5614DDF44792AA0F58EC4A3E0B758`

The first real compiler error is failure to synthesize

```text
NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
```

at `BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen.lean:63:8`.
Subsequent invalid-argument, unknown-identifier and heartbeat messages occur
after the declaration graph has already lost this carrier instance and are
treated as cascade, not as independent failures.

The repair adds explicit private `NeZero` instances for the source large
block side and the full source ambient side.  It does not alter any theorem
statement, operator, constant or hypothesis.
