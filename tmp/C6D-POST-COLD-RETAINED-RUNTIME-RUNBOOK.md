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
`tmp/verify_c6d_source_coercivity_green_evidence.py`.  The cold source must be
`2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24`.

Trigger the cold-archive download from a separate cell only after the literal
PASS; do not rerun the gate cell:

```python
from google.colab import files
files.download("/content/hrpoly-c6d-source-coercivity-green-evidence.tar.gz")
```

Keep the runtime assigned after the download and execute the three hot queues
below in order.

## Hot queue 1: six full-companion/compression pairs

Runner object:
`56e06b46494301cb416266c81946f5388959b2a3:tmp/c6d_full_companion_hot_queue.py`

SHA-256:
`f06bd515b0d640ab813d8919723aa7e7f189fd0e9beea56467bc76383a8e8fba`

The runner itself checks out exact source
`76bfe9c82ffd1e409d1c673b68324449171b3318` while preserving `.lake`.
Execute it once in a new Colab cell:

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/56e06b46494301cb416266c81946f5388959b2a3/tmp/c6d_full_companion_hot_queue.py"
expected = "f06bd515b0d640ab813d8919723aa7e7f189fd0e9beea56467bc76383a8e8fba"
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

## Hot queue 2: ambient C6d producer plus region/Green transport

Runner object:
`50eada4059a2c370a4d2aa5d399b84c9c9e9879a:tmp/c6d_ambient_region_hot_diagnostic.py`

SHA-256:
`deb609c74a7be535c5fe556b0bf4564b04a14ef352eb3ec101d065830ee2c99a`

The runner checks out exact scratch source
`1176948c6a511d017780a54f1cbc8a72b6dea972`, materializes three source/audit
pairs under their intended module names, expects 10 carrier-transport, 7
ambient-producer and 4 canonical-Green transport axiom headers, and rejects anything outside
`{propext, Classical.choice, Quot.sound}`.

```python
import hashlib, pathlib, runpy, urllib.request

url = "https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/50eada4059a2c370a4d2aa5d399b84c9c9e9879a/tmp/c6d_ambient_region_hot_diagnostic.py"
expected = "deb609c74a7be535c5fe556b0bf4564b04a14ef352eb3ec101d065830ee2c99a"
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

Preserve all three hot evidence directories before releasing the runtime.  Hot
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
classified `HOT_DIAGNOSTIC_ONLY`; it is not cold seal evidence.  Disconnect
and delete the runtime only after the archive and executed notebook are
preserved.  A missing or mismatched download is an evidence-transport
failure, not a mathematical FAIL and not permission to rerun either queue.
