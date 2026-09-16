#!/usr/bin/env python3
from __future__ import annotations
import importlib.util,tempfile,time
from pathlib import Path
HERE=Path(__file__).resolve().parent; SCRIPT=HERE/"prepare_step8b24_c6c1_h5e1_carrier_dictionary_overlay.py"
def load():
    s=importlib.util.spec_from_file_location("h5e1",SCRIPT); assert s and s.loader
    m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
def fail(fn,label):
    try: fn()
    except AssertionError:return
    raise AssertionError(f"expected rejection: {label}")
def main():
    t=time.perf_counter();m=load();rows,p=m.build_payload();assert len(rows)==2 and p["declarations"]==p["axiom_prints"]==5
    s=rows[0][1].decode();fail(lambda:m.semantics(s.replace("Equiv.apply_symm_apply","erased")),"inverse cast erased")
    a=m.INPUTS[1][0].read_text(encoding="utf-8");fail(lambda:m.shared.promote(a.replace("#print axioms ","-- removed ",1),5,True),"readout")
    with tempfile.TemporaryDirectory(prefix="h5e1-") as d:
        q=Path(d)/"bad";q.write_bytes(m.INPUTS[0][0].read_bytes()+b"\n");fail(lambda:m.shared.read_pinned(q,m.INPUTS[0][1]),"hash")
    print("PASS H5e1 overlay self-test: cast + shift + owner + axiom + hash gates; "f"elapsed_seconds={time.perf_counter()-t:.6f}; peak_rss_bytes={m.shared.peak_rss_bytes()}");return 0
if __name__=="__main__":raise SystemExit(main())
