#!/usr/bin/env python3
"""Static scope contract for the three canonical Eq. (3.51) inputs."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion", 1),
    ("BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization", 11),
    ("BalabanCMP99Eq351PhysicalComplexCovariantDivergence", 4),
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
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{source_sha}:{path}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ351_REGROUPING_INPUTS_GIT_BLOB_FAILED={path}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def stages() -> tuple[str, ...]:
    return (
        "eq351_regrouping_inputs_materialize_dependencies",
        "eq351_regrouping_inputs_prepare_build_dirs",
        *(
            stage
            for index, (module, _) in enumerate(MODULES, start=1)
            for stage in (
                f"eq351_regrouping_inputs_{index:02d}_{module.lower()}_source",
                f"eq351_regrouping_inputs_{index:02d}_{module.lower()}_audit",
            )
        ),
        "eq351_regrouping_inputs_root",
    )
