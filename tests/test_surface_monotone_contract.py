from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
SUMMARY = re.compile(r"node lists checked:\s*(\d+)\s*;\s*violations:\s*(\d+)")


def test_t1_quarantine_is_publicly_recorded() -> None:
    incident = ROOT / "docs" / "incidents" / "INC-T1-ZERO-SCAN.md"
    text = incident.read_text(encoding="utf-8")
    assert "**Status:** `QUARANTINED`" in text
    assert "INC-T1-ZERO-SCAN" in (ROOT / "README.md").read_text(encoding="utf-8")


@pytest.mark.xfail(
    strict=True,
    reason=(
        "T1 quarantine: committed scanner sees 78 lists and 16 live violations "
        "when invoked from scripts/; remove this marker only after v88 lands"
    ),
)
def test_live_surface_node_partitions_are_strictly_increasing() -> None:
    """Run T1 from the only cwd that scans the committed live scripts.

    Strict xfail is intentional: the known defect is visible today, while a future
    fix becomes an XPASS failure until the quarantine marker is deliberately removed.
    """

    result = subprocess.run(
        [sys.executable, "test_monotone_nodes.py"],
        cwd=SCRIPTS,
        check=False,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr
    match = SUMMARY.search(output)
    assert match is not None, output
    checked, violations = (int(value) for value in match.groups())
    assert checked > 0, "T1 scanned zero node lists"
    assert result.returncode == 0 and violations == 0, output
