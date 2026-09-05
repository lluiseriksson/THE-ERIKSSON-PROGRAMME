#!/usr/bin/env python3
"""Static contract for the CMP99 (3.50) adjoint-composition cold gate."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99ComplexSpecialLinearAdjointComposition", 3),
    ("BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization", 6),
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
            f"EQ351_ADJOINT_GIT_BLOB_FAILED={path}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def stages() -> tuple[str, ...]:
    return (
        "eq351_adjoint_materialize_dependencies",
        "eq351_adjoint_prepare_build_dirs",
        *(
            stage
            for index, (module, _) in enumerate(MODULES, start=1)
            for stage in (
                f"eq351_adjoint_{index:02d}_{module.lower()}_source",
                f"eq351_adjoint_{index:02d}_{module.lower()}_audit",
            )
        ),
        "eq351_adjoint_root",
    )
