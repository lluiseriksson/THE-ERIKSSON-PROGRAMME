#!/usr/bin/env python3
"""Light fail-closed self-test for the H5e3b overlay builder."""
from __future__ import annotations
import importlib.util,time
from pathlib import Path
HERE=Path(__file__).resolve().parent; SCRIPT=HERE/"prepare_step8b24_c6c1_h5e3b_localized_field_holder_owner_overlay.py"
spec=importlib.util.spec_from_file_location("h5e3b",SCRIPT); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
def must_fail(text,needle):
    try: m.require_semantics(text)
    except AssertionError as e:
        if needle not in str(e): raise
    else: raise AssertionError(f"EXPECTED_FAILURE={needle}")
def main():
    t=time.perf_counter(); rows,p=m.build_payload(); source=rows[0][1].decode()
    assert len(rows)==2 and p["declarations"]==p["axiom_prints"]==2
    assert p["identity_owner_reduction"]=="CONSUMED" and p["source_norm"]=="FINITE_SUP"
    assert p["owner_fibre_cardinality"]==p["fine_cardinality"]=="ABSENT"
    m.require_semantics(source)
    must_fail(source+"\n#check Fintype.card\n","CARDINALITY_LEAK")
    must_fail(source.replace("norm_apply_le_finitePiLpSupNorm","norm_nonneg"),"norm_apply_le_finitePiLpSupNorm")
    print(f"PASS H5e3b overlay self-test: identity-owner, sup-norm and no-cardinality gates; elapsed_seconds={time.perf_counter()-t:.6f}; peak_rss_bytes={m.shared.peak_rss_bytes()}")
if __name__=="__main__": main()
