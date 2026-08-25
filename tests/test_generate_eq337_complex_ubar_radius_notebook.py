from __future__ import annotations

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_eq337_complex_ubar_radius_notebook.py"
CURRENT_NOTEBOOK = ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.ipynb"


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

