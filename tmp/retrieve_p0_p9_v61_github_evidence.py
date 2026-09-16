#!/usr/bin/env python3
"""Retrieve and independently audit the one terminal P0--P9 v61 artifact."""

import audit_p0_p9_v61_github_evidence as gate
import retrieve_p0_p9_v56_github_evidence as shared


shared.gate = gate
shared.RUN_ID = 32380193643
shared.EXPECTED_HEAD = gate.CONTROL_SHA
shared.EXPECTED_NAME = f"p0-p9-v61-{gate.contract.SOURCE_SHA}"
shared.VERSION_MARKER = "P0_P9_V61"
shared.DESTINATION_SLUG = "p0-p9-v61"


if __name__ == "__main__":
    raise SystemExit(shared.main())
