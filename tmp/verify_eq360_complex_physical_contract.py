#!/usr/bin/env python3
"""Static contract shared by the source-specific Eq. (3.60) evidence tools."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99Eq360ComplexRegionalLaplacian", 8),
    ("BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice", 3),
    ("BalabanCMP99Eq360ComplexLocalLaplacianPerturbation", 3),
    ("BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation", 3),
    ("BalabanCMP99Eq360ComplexClosedPhysicalPrecision", 14),
)
PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]", re.MULTILINE
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", re.MULTILINE
)


def git_blob(repo: Path, source_sha: str, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "show", f"{source_sha}:{path}"],
        cwd=repo, check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ360_COMPLEX_PHYSICAL_GIT_BLOB_FAILED={path}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def stages() -> tuple[str, ...]:
    return (
        "eq360_complex_physical_materialize_dependencies",
        "eq360_complex_physical_prepare_build_dirs",
        *(
            stage
            for index, (module, _) in enumerate(MODULES, start=1)
            for stage in (
                f"eq360_complex_physical_{index:02d}_{module.lower()}_source",
                f"eq360_complex_physical_{index:02d}_{module.lower()}_audit",
            )
        ),
        "eq360_complex_physical_root",
    )
