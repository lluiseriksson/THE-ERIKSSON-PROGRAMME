# 281C: pre-execution JSON serialization repair

This is a fabrication event and static serialization inventory, not acceptance
of the source, numerical output, an audit of this implementer's own code, or a
scientific/model assessment. Separate exact C source review is still required.
The complete 281B construction notes remain historical in CONSTRUCTION281.md
and in history-281B-before-serialization-C. Their preferred execution source
was B; the current preferred execution source is diagnostic281C.py.

The parent found a definite pre-execution blocker in B: tuple((np.array(k)+q)%n)
contains NumPy integer scalars. blocks.json passed list(h) directly to plain
json.dump, which does not serialize NumPy int64. Therefore B was not ready
for execution despite its earlier analytical review. The parent reports that
the analytical source auditor missed this engineering blocker; that complete
prior report remains immutable and is not retrospectively amended here.
No runtime had been allocated and no parent-authority relay had been created.
No runtime failure or numerical observation is invented from this static defect.

## Complete mathematical-source delta

Only two source lines changed from preserved B to preferred C:

1. h=tuple((np.array(k)+q)%n) becomes
   h=tuple(int(x) for x in ((np.array(k)+q)%n)).
2. The retained native source-copy filename changes diagnostic281B.py to
   diagnostic281C.py, so returned provenance names the actual source version.

The arithmetic values, block assembly, parameters, cutoffs, tolerances,
observation geometry, eigensolves, witness selection, eligibility threshold,
integrity predicates, fixed case count and mutation predicates are unchanged.
The complete textual diff is B-to-C-full-delta.diff. No generic NumPy JSON
encoder or silent conversion of arbitrary objects was introduced.

## Static inventory of every JSON-producing family

This inventory follows source types without importing or executing the code:

- blocks.json: k comes from numpy.ndindex's native index tuples; h now contains
  explicitly converted Python int values. frame dimensions come from ndarray
  shape integers; eigenvalues/explicit roots use ndarray.tolist, which converts
  numeric leaves to native Python scalars. Relative-root residual is float.
- original-row-labels.json: n/channel/i/component originate from Python fixed
  integer tuples/range. Interval lists use range; all are native integers.
- Case JSON and pre-acceptance measurements: dimensions/counts use len or int;
  spectra use tolist, extrema/eta values use float, flags use bool, text and
  timestamps are strings. The original component squared norms and eligibility
  threshold derive from explicitly cast Python float norms. No vector or NumPy
  integer object is sent to JSON; full vectors go to .npy files.
- Physical-integrity checks: explicit float norms/energy are used. A few
  divisions by numpy.sqrt can produce NumPy float64 scalar leaves. NumPy
  float64 is a Python float subclass, accepted by the plain JSON encoder;
  this is distinct from the unsupported NumPy integer h entries. There is no
  float32, complex scalar or raw ndarray JSON leaf. allow_nan=False remains
  active, so any nonfinite leaf is an actual retained serialization failure,
  never an invented success or stringified numerical observation.
- The M inventory casts rank with int, maxima/cutoffs with float arithmetic,
  arrays with tolist. matrix-relative diagnostics use float norms with only
  the recorded tiny floor; any NumPy floating result is float64 as above.
- Independent n4 report casts SVD ranks/nullity with int and eigenvalue with
  float; native n and dimensions are Python integers. All stored spectra are
  .npy, not raw arrays in the report.
- Mutation JSON: strings, native booleans, exception strings and source hash;
  no NumPy value is included in its result records. The unchanged real numeric
  predicates execute only later in the actual standalone mutation children.
- Native environment/package metadata: version/path/hash values are strings;
  file sizes are Python stat integers and environment values string or None.
- Top-level report and raw manifest: fixed native Python values, case records
  inventoried above, pathlib string conversion, Python stat integers/hashes.
- Bootstrap receipt and machine summary: subprocess exit values are native
  Python int, flags native bool, timestamps/hash/path/status strings, command
  lists native structures. Loaded JSON is already native. The base64 payload
  is not executed during preparation.

This is a static construction inventory with library-contract assumptions,
not an execution guarantee or an independent source-audit conclusion. A later
serialization failure must be preserved and reviewed, not hidden by loosening
the encoder or thresholds.

## Source binding and exact history

Before modification, the exact frozen B source, launch, template, outer,
capture, backend readback, manifest and notes were copied byte-for-byte into
history-281B-before-serialization-C. The B manifest remains
1b9d3d115b68f1250803c561a25728bc717d7b86218f2f2d071c7bdb5d97f1c7.
The earlier immutable D source-preparation and thread-bound-final packets
remain untouched. Their reports and histories retain their original meaning.

The current bootstrap template uses the actual C filename. launch281.py
embeds exact C source bytes/hash. The outer's exact diagnostic hash is rebound
to C; all operative file hashes/lengths are refreshed in RUNNER-HASHES.json,
which names diagnostic281C.py. Capture/backend readback bytes remain unchanged.
The bootstrap retains the explicit native thread environment1 requested by
the parent, three actual standalone child captures, normal/-O tiny mutation
checks, native failure retention and envelope hashes. The actual source Git
SHA and complete separate review reports must still be supplied by the
parent's genuine relay; no relay, permission or human response was fabricated.

No tests, numerical code, WSL, runtime, network, service, browser, commit,
push, original report or programme-state change occurred in this repair.
Actual involved identity is Codex/OpenAI in the same programme context;
exact backend model identity remains unavailable. No independence or new
scientific grade is claimed. Numerical and mathematical limitations in the
original construction notes remain in force. PR29 and continuum status are
unmodified. Execution and any returned evidence remain future parent work.
