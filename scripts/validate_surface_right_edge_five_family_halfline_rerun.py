"""Validate and compare the independent G5 half-line rerun."""

import json

import certify_surface_right_edge_five_family_halfline as cert
import run_surface_right_edge_five_family_halfline_rerun_units as rerun
import validate_surface_right_edge_five_family_halfline_transcript as primary


def rows(path):
    return [json.loads(line[4:]) for line in path.read_text(
        encoding="utf-8").splitlines() if line.startswith("ROW ")]


def validate():
    primary_rows = primary.validate()
    rerun_rows = []
    head = rerun.current_head()
    frozen = rerun.FROZEN_SOURCE_HEAD
    assert rerun.source_dependency_hashes(frozen) == {
        relative: rerun.hashlib.sha256(
            (rerun.ROOT/relative).read_bytes()).hexdigest()
        for relative in cert.DEPENDENCIES
    }
    observed_heads = set()
    for unit in cert.UNITS:
        assert rerun.complete(unit, head)
        content = rerun.output_path(unit).read_text(encoding="utf-8")
        observed_heads.add(next(line.split()[-1]
                                for line in content.splitlines()
                                if line.startswith("PROVENANCE git_head ")))
        unit_rows = rows(rerun.output_path(unit))
        assert len(unit_rows) == 40
        rerun_rows.extend(unit_rows)
    assert len(rerun_rows) == 600
    assert observed_heads == {frozen}
    assert rerun_rows == primary_rows
    print("RIGHT-EDGE FIVE-FAMILY HALFLINE INDEPENDENT RERUN PASS: "
          "600/600 rows byte-equal after JSON parsing; head", head)
    return rerun_rows


if __name__ == "__main__":
    validate()
