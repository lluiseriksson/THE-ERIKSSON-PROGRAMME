from __future__ import annotations

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_eq337_complex_ubar_radius_notebook.py"
CURRENT_NOTEBOOK = ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.ipynb"
COORDINATE_NOTEBOOK = ROOT / "scripts" / "colab_eq337_complex_coordinate_validation.ipynb"
C6D_NOTEBOOK = ROOT / "scripts" / "colab_c6d_localized_retained_tower_cold_validation.ipynb"


def load_generator():
    spec = importlib.util.spec_from_file_location("eq337_ubar_notebook_generator", GENERATOR)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_reproduces_published_notebook_semantics() -> None:
    generator = load_generator()
    generated = json.loads(
        generator.generate(
            "b1357760890c9551dd9786da0f691d652bf21eda",
            "bf081293b9abdd5d7e81485fd456c0de393a027e",
            "eq337-complex-ubar-radius-debug-v1",
        )
    )
    published = json.loads(CURRENT_NOTEBOOK.read_text(encoding="utf-8"))
    assert generated == published
    assert generated["cells"][0]["id"] == "gate-b83d7b4ec7f3e78a"


def test_reproduces_published_coordinate_notebook_semantics() -> None:
    generator = load_generator()
    generated = json.loads(
        generator.generate(
            "b70735b82216a0ab1cd9a3bd4e195db1426a83fe",
            "737b7b01badeba5811b1bb7ae557c6ea45c4a79e",
            "eq337-complex-coordinate-fresh-v4",
            "scripts/colab_eq337_complex_coordinate_validation.py",
        )
    )
    published = json.loads(COORDINATE_NOTEBOOK.read_text(encoding="utf-8"))
    assert generated == published
    assert generated["cells"][0]["id"] == "gate-e88d83c8636fe3b2"


def test_c6d_launcher_has_stable_transport_bound_cell_id() -> None:
    notebook = json.loads(C6D_NOTEBOOK.read_text(encoding="utf-8"))
    assert len(notebook["cells"]) == 1
    cell = notebook["cells"][0]
    assert cell["id"] == "gate-96cc53a1d3f27483"
    source = "".join(cell["source"])
    assert 'RUNNER_SHA256 = "96cc53a1d3f27483225d034b0b8a675ce24ee2dd1fedaacc3ab97372450838a7"' in source
