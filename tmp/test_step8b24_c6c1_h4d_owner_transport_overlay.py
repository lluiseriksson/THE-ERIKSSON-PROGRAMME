#!/usr/bin/env python3
"""Fail-closed tests for H4d two-point owner overlay."""
from __future__ import annotations
import importlib.util, tempfile, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
SCRIPT=HERE/"prepare_step8b24_c6c1_h4d_owner_transport_overlay.py"
def load_module():
    spec=importlib.util.spec_from_file_location("h4d_owner",SCRIPT); assert spec and spec.loader
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module
def must_fail(fn,label):
    try: fn()
    except AssertionError: return
    raise AssertionError(f"expected fail-closed rejection: {label}")
def main():
    started=time.perf_counter(); module=load_module(); rows,payload=module.build_payload()
    assert len(rows)==2 and payload["declarations"]==payload["axiom_prints"]==9
    assert payload["endpoint_bounds_summed"] is False
    assert payload["target_only_owner_metric"] is False
    source=rows[0][1].decode()
    must_fail(lambda: module.require_semantics(source.replace("cmp116BondSource b","cmp116BondTarget b")),"source endpoint erased")
    must_fail(lambda: module.require_semantics(source+"\n#check PhysicalEndpointWeights_le_ownerWeight\n"),"old summed endpoint bridge")
    audit=module.INPUTS[1][0].read_text(encoding="utf-8")
    must_fail(lambda: module.shared.promote(audit.replace("#print axioms ","-- removed ",1),9,True),"missing axiom readout")
    with tempfile.TemporaryDirectory(prefix="h4d-owner-") as tmp:
        bad=Path(tmp)/"bad.lean"; bad.write_bytes(module.INPUTS[0][0].read_bytes()+b"\n")
        must_fail(lambda: module.shared.read_pinned(bad,module.INPUTS[0][1]),"input drift")
    print("PASS H4d overlay self-test: two-point + no-sum + axiom + hash gates; "
      f"elapsed_seconds={time.perf_counter()-started:.6f}; peak_rss_bytes={module.shared.peak_rss_bytes()}")
    return 0
if __name__ == "__main__": raise SystemExit(main())
