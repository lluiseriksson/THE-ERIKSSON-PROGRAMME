from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
SUMMARY = re.compile(r"node lists checked:\s*(\d+)\s*;\s*violations:\s*(\d+)")


def test_t1_incident_and_repair_are_publicly_recorded() -> None:
    incident = ROOT / "docs" / "incidents" / "INC-T1-ZERO-SCAN.md"
    text = incident.read_text(encoding="utf-8")
    assert "**Status:** `T1_REPAIRED`; `V88_RERUN_AUDIT_IN_PROGRESS`" in text
    assert "INC-T1-ZERO-SCAN" in (ROOT / "README.md").read_text(encoding="utf-8")


def test_live_surface_node_partitions_are_strictly_increasing() -> None:
    """T1 must give the same nonzero passing result from root and scripts/."""

    invocations = (
        ([sys.executable, "scripts/test_monotone_nodes.py"], ROOT),
        ([sys.executable, "test_monotone_nodes.py"], SCRIPTS),
    )
    summaries: list[tuple[int, int]] = []
    for command, cwd in invocations:
        result = subprocess.run(
            command,
            cwd=cwd,
            check=False,
            capture_output=True,
            text=True,
        )
        output = result.stdout + result.stderr
        match = SUMMARY.search(output)
        assert match is not None, output
        checked, violations = (int(value) for value in match.groups())
        assert checked >= 78, output
        assert result.returncode == 0 and violations == 0, output
        summaries.append((checked, violations))
    assert summaries[0] == summaries[1]
