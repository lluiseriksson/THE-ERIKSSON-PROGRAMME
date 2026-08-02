"""Fail-closed audit wrapper for the preregistered spatial-sector probe.

This licenses one VERIFIED numerical statement, not a Lean theorem: on the 21
registered cells, both block ratios obey q, the odd bound is observed sharp to
1e-8, and the printed even ratio does not exceed printed q^2 beyond rounding.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path


RAW_SHA = "3421aa1f"
RAW_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    f"THE-ERIKSSON-PROGRAMME/{RAW_SHA}/scripts/probe_sector_blocks.py"
)
EXPECTED_SOURCE_SHA256 = (
    "fb7b86e91d6899b73d3c6d704c0bee76ac8754fc568e59115447489f87e2ec36"
)
EXPECTED_ROWS = 21
ODD_SHARPNESS_TOL = 1.0e-8
# The upstream table prints q^2 and evenNP/lam to six decimals.  Each rounded
# value can move by 0.5e-6, hence 1.1e-6 is the fail-closed comparison budget.
PRINTED_Q2_OVERSHOOT_TOL = 1.1e-6

ROW_RE = re.compile(
    r"^\s*(?P<beta>\d+\.\d+)\s+(?P<gamma>\d+\.\d+)\s+(?P<L>\d+)\s+"
    r"(?P<q>\d+\.\d+)\s+(?P<odd>\d+\.\d+)\s+"
    r"(?P<even>\d+\.\d+)\s+(?P<q2>\d+\.\d+)\s+"
    r"(?P<odd_status>ok|FAIL)\s+(?P<even_status>ok|FAIL)\s*$"
)
SLACK_RE = re.compile(
    r"^smallest slack in the ODD obligation:\s*(?P<slack>[+-]?\d+\.\d+e[+-]\d+)\s*$",
    re.MULTILINE,
)


def fail(message: str, *, stdout: str = "", stderr: str = "") -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if stdout:
        print("--- upstream stdout ---", file=sys.stderr)
        print(stdout, file=sys.stderr)
    if stderr:
        print("--- upstream stderr ---", file=sys.stderr)
        print(stderr, file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    try:
        with urllib.request.urlopen(RAW_URL, timeout=60) as response:
            source = response.read()
    except Exception as exc:
        fail(f"could not download raw probe: {exc}")

    source_hash = hashlib.sha256(source).hexdigest()
    if source_hash != EXPECTED_SOURCE_SHA256:
        fail(f"source SHA-256 mismatch: {source_hash}")

    with tempfile.TemporaryDirectory(prefix="spatial-sector-probe-") as tmp:
        probe = Path(tmp) / "probe_sector_blocks.py"
        probe.write_bytes(source)
        run = subprocess.run(
            [sys.executable, str(probe)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    if run.returncode != 0:
        fail(
            f"upstream probe exited {run.returncode}",
            stdout=run.stdout,
            stderr=run.stderr,
        )

    rows = []
    for line in run.stdout.splitlines():
        match = ROW_RE.match(line)
        if match:
            rows.append(match.groupdict())
    if len(rows) != EXPECTED_ROWS:
        fail(f"expected {EXPECTED_ROWS} data rows, found {len(rows)}", stdout=run.stdout)

    if any(row["odd_status"] != "ok" or row["even_status"] != "ok" for row in rows):
        fail("upstream table contains a block violation", stdout=run.stdout)

    slack_match = SLACK_RE.search(run.stdout)
    if slack_match is None:
        fail("upstream output omitted the odd-slack measurement", stdout=run.stdout)
    odd_slack = float(slack_match.group("slack"))
    if odd_slack < -1.0e-12:
        fail(f"odd block violates q: slack={odd_slack:.17g}", stdout=run.stdout)
    if odd_slack > ODD_SHARPNESS_TOL:
        fail(f"odd block was not observed sharp: slack={odd_slack:.17g}", stdout=run.stdout)

    printed_q2_overshoot = max(float(row["even"]) - float(row["q2"]) for row in rows)
    if printed_q2_overshoot > PRINTED_Q2_OVERSHOOT_TOL:
        fail(
            "printed even non-Perron ratio exceeds printed q^2: "
            f"overshoot={printed_q2_overshoot:.17g}",
            stdout=run.stdout,
        )

    certificate = {
        "status": "PASS",
        "classification": "VERIFIED numerical evidence; not a Lean certificate",
        "raw_sha": RAW_SHA,
        "source_sha256": source_hash,
        "rows": len(rows),
        "smallest_odd_slack": odd_slack,
        "max_printed_even_minus_q2": printed_q2_overshoot,
    }
    print(run.stdout, end="")
    print(json.dumps(certificate, sort_keys=True))


if __name__ == "__main__":
    main()
