#!/usr/bin/env python3
from __future__ import annotations
import importlib.util,tempfile,time
from pathlib import Path
HERE=Path(__file__).resolve().parent; SCRIPT=HERE/"prepare_step8b24_c6c1_h5e0_residue_owner_projection_overlay.py"
def load():
    s=importlib.util.spec_from_file_location("h5e0",SCRIPT); assert s and s.loader
    m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
def fail(fn,label):
    try: fn()
    except AssertionError: return
    raise AssertionError(f"expected fail-closed rejection: {label}")
def main():
    t=time.perf_counter(); m=load(); rows,p=m.build_payload(); assert len(rows)==2 and p["declarations"]==p["axiom_prints"]==3
    source=rows[0][1].decode()
    fail(lambda:m.require_semantics(source.replace("cmp99FlatIntegerZeroResidueClassQuotient_spec","erased_quotient")),"quotient erased")
    audit=m.INPUTS[1][0].read_text(encoding="utf-8")
    fail(lambda:m.shared.promote(audit.replace("#print axioms ","-- removed ",1),3,True),"missing readout")
    with tempfile.TemporaryDirectory(prefix="h5e0-") as d:
        q=Path(d)/"bad"; q.write_bytes(m.INPUTS[0][0].read_bytes()+b"\n")
        fail(lambda:m.shared.read_pinned(q,m.INPUTS[0][1]),"hash drift")
    print("PASS H5e0 overlay self-test: residue + carry + axiom + hash gates; "
      f"elapsed_seconds={time.perf_counter()-t:.6f}; peak_rss_bytes={m.shared.peak_rss_bytes()}"); return 0
if __name__=="__main__": raise SystemExit(main())
