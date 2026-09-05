# C6d retained-runtime post-cold runbook

Status: execution instructions only.  None of the three hot queues is seal evidence.

## Entry gate

Proceed only after the already-running notebook emits literal
`FINAL_STATUS=PASS`.  Do not rerun its cell.  Before changing the checkout,
preserve and download:

- `/content/hrpoly-c6d-source-coercivity-green-evidence.tar.gz`;
- the executed notebook;
- the printed archive hash and final sentinel.

Verify the archive locally with
`tmp/verify_c6d_source_coercivity_green_evidence.py <archive> <executed-ipynb>`.
The verifier cross-checks the exact executed cell, stage sequence, axiom
sections and printed evidence/archive hashes.  The cold source must be
`2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24`.

Download the executed notebook from Colab **before adding another cell**.  The
external verifier deliberately requires the original one-code-cell topology.
Then trigger the cold-archive download from a separate cell only after the
literal PASS; do not rerun the gate cell:

```python
from google.colab import files
files.download("/content/hrpoly-c6d-source-coercivity-green-evidence.tar.gz")
```

Keep the runtime assigned after the download and execute the three hot queues
below in order.

## Hot queue 1: six full-companion/compression pairs

Runner object:
`15eb873009aed90402183d1efba2bd3151096d04:tmp/c6d_full_companion_hot_queue.py`

SHA-256:
`3eac2645ede0c5bacdb22e133a8c22288ae634252b1b5e95bdf755eeb9441c35`

The runner itself checks out exact source
`ec4db69a54e0f47189940086476edf4c47a39abe` while preserving `.lake`.
Execute it once in a new Colab cell:

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/15eb873009aed90402183d1efba2bd3151096d04/tmp/c6d_full_companion_hot_queue.py"
expected = "3eac2645ede0c5bacdb22e133a8c22288ae634252b1b5e95bdf755eeb9441c35"
payload = urllib.request.urlopen(url, timeout=60).read()
actual = hashlib.sha256(payload).hexdigest()
assert actual == expected, (actual, expected)
path = pathlib.Path("/content/c6d_full_companion_hot_queue.py")
path.write_bytes(payload)
try:
    runpy.run_path(str(path), run_name="__main__")
except SystemExit as exc:
    if exc.code not in (None, 0):
        raise
```

Stop at its first real error.  Continue to queue 2 only on literal hot
`FINAL_STATUS=PASS`.

For a diagnostic retry after a measured failure in pair `n`, the same runner
may be invoked with `C6D_START_INDEX=n`; this does not replace the final
default run from index `1` used to assemble queue-1 evidence.

## Hot queue 2: ambient C6d producer plus region/Green transport

Runner object:
`84d80168ac39c43a67d1542cd51c21cb306d2fc3:tmp/c6d_ambient_region_hot_diagnostic.py`

SHA-256:
`8457436d9f821d4e011c848577a95bc25be4d0c79ea1fea0e9579c744257cc08`

The runner checks out exact scratch source
`58f11d92b49cc5b9334bc46136de0b097175dfe9`, materializes three source/audit
pairs under their intended module names, expects 10 carrier-transport, 7
ambient-producer and 4 canonical-Green transport axiom headers, and rejects anything outside
`{propext, Classical.choice, Quot.sound}`.

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/84d80168ac39c43a67d1542cd51c21cb306d2fc3/tmp/c6d_ambient_region_hot_diagnostic.py"
expected = "8457436d9f821d4e011c848577a95bc25be4d0c79ea1fea0e9579c744257cc08"
payload = urllib.request.urlopen(url, timeout=60).read()
actual = hashlib.sha256(payload).hexdigest()
assert actual == expected, (actual, expected)
path = pathlib.Path("/content/c6d_ambient_region_hot_diagnostic.py")
path.write_bytes(payload)
try:
    runpy.run_path(str(path), run_name="__main__")
except SystemExit as exc:
    if exc.code not in (None, 0):
        raise
```

Continue to queue 3 only on literal hot `FINAL_STATUS=PASS`.

For a measured failure in ambient pair `n`, diagnostic retries may set
`C6D_AMBIENT_START_INDEX=n`.  The evidence-producing run still uses the
default index `1` after all three pairs are green.

## Hot queue 3: exact depth-zero full companion and ambient coercivity

Runner object:
`32155c5ae3cd30a931483eaecc6278c565e0ddaa:tmp/c6d_zero_depth_hot_diagnostic.py`

SHA-256:
`bdd1c1cd2d3b6dc3f5b0b4ce53829545499c01854b94491ba0d6f1d06a57a3fd`

The runner checks out exact scratch source
`4cd9364e64fa039878ccfcb20a1dbb64b02cb5f5`, materializes the exact
depth-zero full-companion source/audit pair, expects three axiom headers, and
rejects anything outside `{propext, Classical.choice, Quot.sound}`.

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/32155c5ae3cd30a931483eaecc6278c565e0ddaa/tmp/c6d_zero_depth_hot_diagnostic.py"
expected = "bdd1c1cd2d3b6dc3f5b0b4ce53829545499c01854b94491ba0d6f1d06a57a3fd"
payload = urllib.request.urlopen(url, timeout=60).read()
actual = hashlib.sha256(payload).hexdigest()
assert actual == expected, (actual, expected)
path = pathlib.Path("/content/c6d_zero_depth_hot_diagnostic.py")
path.write_bytes(payload)
try:
    runpy.run_path(str(path), run_name="__main__")
except SystemExit as exc:
    if exc.code not in (None, 0):
        raise
```

Preserve all three hot evidence directories before continuing.  Hot
PASS authorizes only preparation of corrected PRE-VALIDATION promotion; a
later cold checkout is required to seal.  No hot queue moves `20/41`,
attains window 15, or instantiates `TermSource`.

## Exit gate: package the three hot diagnostics

Only after all three hot queues emit literal PASS, create one archive and print its
digest before requesting the browser download:

```python
import hashlib, pathlib, tarfile
from google.colab import files

archive = pathlib.Path("/content/hrpoly-c6d-post-cold-hot-evidence.tar.gz")
roots = [
    pathlib.Path("/content/hrpoly-c6d-full-companion-hot-evidence"),
    pathlib.Path("/content/hrpoly-c6d-ambient-region-hot-evidence"),
    pathlib.Path("/content/hrpoly-c6d-zero-depth-hot-evidence"),
]
for root in roots:
    assert root.is_dir(), root
with tarfile.open(archive, "w:gz") as tar:
    for root in roots:
        tar.add(root, arcname=root.name)
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
print("POST_COLD_HOT_ARCHIVE_SHA256=" + digest, flush=True)
files.download(str(archive))
```

Verify the downloaded digest outside Colab.  Download the executed notebook,
then run the fail-closed external verifier:

```text
python tmp/verify_c6d_post_cold_hot_evidence.py \
  <downloaded-hrpoly-c6d-post-cold-hot-evidence.tar.gz>
```

It requires exactly 34 stage logs, the three pinned source SHAs, all five text
guards, and exactly 49 allowed axiom headers (`25 + 21 + 3`).  Its result remains
classified `HOT_DIAGNOSTIC_ONLY`; it is not cold seal evidence.  Do not
disconnect yet.  A missing or mismatched download is an evidence-transport
failure, not a mathematical FAIL and not permission to rerun any queue.

## Hot queue 4: exact depth-zero Dirichlet Green

Run this queue only after queue 3 emitted literal PASS and after the
three-queue archive above has been created.  It is a separate dependent
diagnostic because the depth-zero coercivity brick had to receive its own
verdict first.

Runner object:
`e1b17096d3e9c5ac2c230a7cf0cfe8005f76583c:tmp/c6d_zero_depth_green_hot_diagnostic.py`

SHA-256:
`f43eb90eaa59927f163e1ea82c5d435a8b077d641c78526ccce3061857bdd6fb`

The runner checks out exact source
`be4e66a1262e132cf0721fb0f3768e9e884bb3ad`, rematerializes the already
green depth-zero coercivity pair and then materializes only the dependent
depth-zero Green pair.  It expects six axiom headers and rejects anything
outside `{propext, Classical.choice, Quot.sound}`.

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/e1b17096d3e9c5ac2c230a7cf0cfe8005f76583c/tmp/c6d_zero_depth_green_hot_diagnostic.py"
expected = "f43eb90eaa59927f163e1ea82c5d435a8b077d641c78526ccce3061857bdd6fb"
payload = urllib.request.urlopen(url, timeout=60).read()
actual = hashlib.sha256(payload).hexdigest()
assert actual == expected, (actual, expected)
path = pathlib.Path("/content/c6d_zero_depth_green_hot_diagnostic.py")
path.write_bytes(payload)
try:
    runpy.run_path(str(path), run_name="__main__")
except SystemExit as exc:
    if exc.code not in (None, 0):
        raise
```

On literal PASS, package and download its evidence separately:

```python
import hashlib, pathlib, tarfile
from google.colab import files

root = pathlib.Path("/content/hrpoly-c6d-zero-depth-green-hot-evidence")
archive = pathlib.Path("/content/hrpoly-c6d-zero-depth-green-hot-evidence.tar.gz")
assert root.is_dir(), root
with tarfile.open(archive, "w:gz") as tar:
    tar.add(root, arcname=root.name)
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
print("ZERO_DEPTH_GREEN_HOT_ARCHIVE_SHA256=" + digest, flush=True)
files.download(str(archive))
```

Verify it outside Colab with:

```text
python tmp/verify_c6d_zero_depth_green_hot_evidence.py \
  <downloaded-hrpoly-c6d-zero-depth-green-hot-evidence.tar.gz>
```

The expected result is `C6D_ZERO_DEPTH_GREEN_HOT_EVIDENCE_OK`, seven exact
archive members and six allowed axiom headers.  This remains
`HOT_DIAGNOSTIC_ONLY`.  Download the final executed notebook, then disconnect
and delete the runtime only after both hot archives and both verifier results
are preserved.
