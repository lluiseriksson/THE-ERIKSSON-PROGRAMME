from __future__ import annotations

import importlib.util
import sys
from argparse import Namespace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "source_citations", ROOT / "scripts" / "source_citations.py"
)
assert SPEC and SPEC.loader
source_citations = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = source_citations
SPEC.loader.exec_module(source_citations)


def test_loads_primary_and_operational_catalogs() -> None:
    _sources, citations = source_citations.load_catalogs()
    keys = {citation["key"] for citation in citations}

    assert "cmp116.eq231.p-family-carrier-source-target" in keys
    assert "crosswalk.eq231.p-family-source-dictionary-route" in keys


def test_show_prints_operational_crosswalk(capsys) -> None:
    args = Namespace(
        key="crosswalk.eq231.p-family-source-dictionary-route",
        format="compact",
    )

    assert source_citations.command_show(args) == 0
    captured = capsys.readouterr()
    assert "Operational route for closing the CMP116 Eq. (2.31)" in captured.out
    assert "do not use for:" in captured.out
    assert "dictionary links:" in captured.out


def test_validate_accepts_extended_catalogs(capsys) -> None:
    assert source_citations.command_validate(Namespace()) == 0
    captured = capsys.readouterr()
    assert "validated" in captured.out
