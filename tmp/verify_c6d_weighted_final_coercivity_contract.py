#!/usr/bin/env python3
"""Static contract for the combined weighted/final/coercivity cold gate."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99ActiveRegionCanonicalAmbientCompletion", 8),
    ("BalabanCMP99SourceWeightedGaugePrecisionDictionary", 3),
    ("BalabanCMP99Eq360WeightedPrecisionRealSlice", 1),
    ("BalabanCMP99Eq360C6dLocalizedRetainedPrecision", 30),
    ("BalabanCMP99SourceActiveRegionTerminalCoercivity", 6),
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
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_WFC_GIT_BLOB_FAILED={path}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def stages() -> tuple[str, ...]:
    return (
        "c6d_weighted_final_coercivity_materialize_dependencies",
        "c6d_weighted_final_coercivity_prepare_build_dirs",
        *(
            stage
            for index, (module, _) in enumerate(MODULES, start=1)
            for stage in (
                f"c6d_weighted_final_coercivity_{index:02d}_{module.lower()}_source",
                f"c6d_weighted_final_coercivity_{index:02d}_{module.lower()}_audit",
            )
        ),
        "c6d_weighted_final_coercivity_root",
    )
