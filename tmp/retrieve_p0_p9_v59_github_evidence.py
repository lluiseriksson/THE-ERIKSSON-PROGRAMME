#!/usr/bin/env python3
"""Retrieve and independently audit the one terminal P0--P9 v59 artifact."""

import audit_p0_p9_v59_github_evidence as gate
import retrieve_p0_p9_v56_github_evidence as shared


shared.gate = gate
shared.RUN_ID = 32354884467
shared.EXPECTED_HEAD = gate.CONTROL_SHA
shared.EXPECTED_NAME = f"p0-p9-v59-{gate.contract.SOURCE_SHA}"
shared.VERSION_MARKER = "P0_P9_V59"
shared.DESTINATION_SLUG = "p0-p9-v59"


if __name__ == "__main__":
    raise SystemExit(shared.main())
