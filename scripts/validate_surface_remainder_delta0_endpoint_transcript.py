"""Validate the exhaustive authoritative K2 endpoint transcript."""

from decimal import Decimal
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT/"scripts"/"certify_surface_remainder_delta0_endpoint_transcript.txt"
ROW = re.compile(
    r"^t-box \[([0-9.]+),([0-9.]+)\]: grid=(96|192).*?"
    r"margin_lower=\[([0-9.eE+-]+) ")
FINAL = ("CERTIFIED (K2 endpoint, Arb): "
         "abs(Y-T-r2*delta)<=Theta3*delta^2 on "
         "[0,1/1000] x [0,pi]; t_boxes=158 refined_grid_boxes=5")
EXPECTED = {
    "script": "scripts/certify_surface_remainder_delta0_endpoint.py",
    "script_sha256": "7287efbc541adf7a5a18bef45c75f4598d895dd929f7bb648bdb40c273413c03",
    "git_head": "46cdff0806cf07d2da87255cb40b813da0c0696b",
    "python": "3.12.6",
    "python_flint": "0.9.0",
    "arb_prec_bits": "140",
    "surface_remainder_delta0_series_cover_design_sha256": "d0f2529aae272ee99fcf83de400309cb96c60defb3ff09ff6ec966b92faf2428",
    "surface_remainder_delta0_series_design_sha256": "3bf631c2efca03284d2e1a0b6308a9536792f16b8003637114da143adbb9e063",
    "surface_remainder_delta0_companion_error_sha256": "c492b6f3183b8c03675418888e2aae8a974eea7c416ebba8d112c6698755b4d2",
    "surface_remainder_delta0_derivative_tail_sha256": "63a147ff86d9ae08e596f38629f0e490211a0ba5ac64ccd95823907eab43258b",
    "surface_remainder_s2_direct_judge_sha256": "b99267ae931e05c4d8d6e5535ebc5d62f85e863d367a8e66fd0f34b7d8b6b780",
    "surface_bessel_integral_remainder_sha256": "a872dec36e1dbfe89f357afcc89bfec64ae375b31325458f9f2fcfb9926c246e",
}
DEPENDENCIES = {
    "surface_remainder_delta0_series_cover_design_sha256":
        "scripts/surface_remainder_delta0_series_cover_design.py",
    "surface_remainder_delta0_series_design_sha256":
        "scripts/surface_remainder_delta0_series_design.py",
    "surface_remainder_delta0_companion_error_sha256":
        "scripts/surface_remainder_delta0_companion_error.py",
    "surface_remainder_delta0_derivative_tail_sha256":
        "scripts/surface_remainder_delta0_derivative_tail.py",
    "surface_remainder_s2_direct_judge_sha256":
        "scripts/surface_remainder_s2_direct_judge.py",
    "surface_bessel_integral_remainder_sha256":
        "scripts/surface_bessel_integral_remainder.py",
}


def validate(path=TRANSCRIPT):
    raw = Path(path).read_bytes()
    lines = raw.decode("utf-8").splitlines()
    if not lines or lines[-1] != FINAL:
        raise AssertionError("missing exact K2 endpoint CERTIFIED terminal")
    provenance = {}
    for line in lines:
        if line.startswith("PROVENANCE "):
            key, value = line[len("PROVENANCE "):].split("=", 1)
            provenance[key] = value
    if provenance != EXPECTED:
        raise AssertionError("K2 endpoint provenance mismatch")
    config = ("CONFIG delta=[0,1/1000] t_birth_width=1/50 "
              "grids=96,192 physical_band=1 radial_tail=32")
    if config not in lines:
        raise AssertionError("K2 endpoint configuration missing")
    paths = {"script_sha256": provenance["script"], **DEPENDENCIES}
    for key, rel in paths.items():
        data = (ROOT/rel).read_bytes()
        if hashlib.sha256(data).hexdigest() != provenance[key]:
            raise AssertionError("worktree hash mismatch for "+rel)
        blob = subprocess.check_output(
            ["git", "show", provenance["git_head"]+":"+rel], cwd=ROOT)
        if hashlib.sha256(blob).hexdigest() != provenance[key]:
            raise AssertionError("executed blob mismatch for "+rel)

    rows = []
    for line in lines:
        match = ROW.match(line)
        if match:
            rows.append((Decimal(match.group(1)), Decimal(match.group(2)),
                         int(match.group(3)), Decimal(match.group(4))))
    if len(rows) != 158:
        raise AssertionError("expected 158 K2 endpoint t boxes")
    cursor = Decimal("0.0")
    for lo, hi, grid, lower in rows:
        if lo != cursor or not (Decimal(0) < hi-lo <= Decimal("0.02")):
            raise AssertionError("K2 endpoint coverage gap/overlap at %s" % lo)
        if grid not in (96, 192) or lower <= 0:
            raise AssertionError("nonpositive K2 endpoint lower margin at %s" % lo)
        cursor = hi
    if cursor != Decimal("3.141592653589793"):
        raise AssertionError("K2 endpoint cover does not end at pi")
    if sum(grid == 192 for _, _, grid, _ in rows) != 5:
        raise AssertionError("K2 endpoint refined-grid count mismatch")
    return {"t_boxes": len(rows),
            "transcript_sha256": hashlib.sha256(raw).hexdigest()}


if __name__ == "__main__":
    result = validate()
    print("K2 endpoint transcript OK: {t_boxes} boxes, sha256="
          "{transcript_sha256}".format(**result))
