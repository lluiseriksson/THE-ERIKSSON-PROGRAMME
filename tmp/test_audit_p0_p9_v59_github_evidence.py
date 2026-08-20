#!/usr/bin/env python3
"""Synthetic positive/tamper tests for the P0--P9 v59 GitHub auditor."""

import audit_p0_p9_v59_github_evidence as gate
import github_p0_p9_v59_driver as contract
import test_audit_p0_p9_v56_github_evidence as shared


shared.gate = gate
shared.contract = contract


if __name__ == "__main__":
    shared.main()
