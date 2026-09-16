#!/usr/bin/env python3
"""Static contract shared by the Eq. (3.59) evidence verifiers."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99ComplexSpecialLinearAdjointAction", 3),
    ("BalabanCMP99ComplexTransportedBlockAverage", 8),
    ("BalabanCMP99ComplexRegionalTower", 6),
    ("BalabanCMP99ComplexPhysicalRegionalTower", 7),
    ("BalabanCMP99Eq359ComplexClosedPhysicalTower", 1),
    ("BalabanCMP99Eq359ComplexRegionalTowerPair", 6),
    ("BalabanCMP99Eq359ComplexClosedPhysicalTowerPair", 1),
)
PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]",
    re.MULTILINE,
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms",
    re.MULTILINE,
)


def git_blob(repo: Path, source_sha: str, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "show", f"{source_sha}:{path}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ359_GIT_BLOB_FAILED={path}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def stages() -> tuple[str, ...]:
    return (
        "eq359_materialize_dependencies",
        "eq359_prepare_build_dirs",
        *(
            stage
            for index, (module, _) in enumerate(MODULES, start=1)
            for stage in (
                f"eq359_{index:02d}_{module.lower()}_source",
                f"eq359_{index:02d}_{module.lower()}_audit",
            )
        ),
        "eq359_root",
    )
