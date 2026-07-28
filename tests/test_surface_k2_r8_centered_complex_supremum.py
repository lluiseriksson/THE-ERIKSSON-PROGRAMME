from pathlib import Path
import sys

from flint import arb, ctx
import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import probe_surface_k2_r8_centered_complex_supremum as probe  # noqa: E402


def test_degree_eight_cauchy_contract():
    ctx.prec = 180
    retained, available, multiplier, required_m = probe.cauchy_budget()
    assert retained.is_finite()
    assert available > 0
    assert multiplier.overlaps(
        (arb(1)/1000/(arb(17)/2000))**8
        / (1-arb(1)/1000/(arb(17)/2000))
    )
    assert required_m > 47
    assert probe.COMPANION_ORDER == 8
    assert probe.LADDER == ((48, 64), (96, 128))


def test_entry_gate_rejects_missing_or_non_green_replay(tmp_path):
    production = tmp_path/"production.txt"
    replay = tmp_path/"replay.txt"
    production.write_text(
        "\n".join([f"Y{k} exact" for k in range(8)])
        + "\n" + probe.PASS_TOKEN + "\n",
        encoding="utf-8",
    )
    replay.write_text("not green\n", encoding="utf-8")
    with pytest.raises(RuntimeError, match="not green"):
        probe.require_exact_head_certificates(production, replay)


def test_entry_gate_accepts_identical_exact_lines(tmp_path):
    production = tmp_path/"production.txt"
    replay = tmp_path/"replay.txt"
    text = (
        "\n".join([f"Y{k} exact" for k in range(8)])
        + "\n" + probe.PASS_TOKEN + "\n"
    )
    production.write_text(text, encoding="utf-8")
    replay.write_text(text, encoding="utf-8")
    assert len(
        probe.require_exact_head_certificates(production, replay)
    ) == 8
