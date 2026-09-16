#!/usr/bin/env python3
"""Light fail-closed self-test for the H5e2 overlay builder."""
from __future__ import annotations
import importlib.util,time
from pathlib import Path
HERE=Path(__file__).resolve().parent; SCRIPT=HERE/"prepare_step8b24_c6c1_h5e2_residue_family_owner_bound_overlay.py"
spec=importlib.util.spec_from_file_location("h5e2",SCRIPT); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
def must_fail(text,needle):
    try: m.require_semantics(text)
    except AssertionError as e:
        if needle not in str(e): raise
    else: raise AssertionError(f"EXPECTED_FAILURE={needle}")
def main():
    t=time.perf_counter(); rows,p=m.build_payload(); source=rows[0][1].decode()
    assert len(rows)==2 and p["declarations"]==p["axiom_prints"]==1
    assert p["zero_residue_family"]=="CONSUMED" and p["rate_split"]=="FORBIDDEN"
    assert p["representative_prefactor"]==p["fine_cardinality"]=="ABSENT"
    m.require_semantics(source)
    must_fail(source.replace("min_le_left", "min_le_right"),"min_le_left")
    must_fail(source.replace("rho / (Kfine : ℝ)", "rho / 2",1),"RATE_SPLIT")
    print(f"PASS H5e2 overlay self-test: centered-residue, no-rate-split and no-cardinality gates; elapsed_seconds={time.perf_counter()-t:.6f}; peak_rss_bytes={m.shared.peak_rss_bytes()}")
if __name__=="__main__": main()
