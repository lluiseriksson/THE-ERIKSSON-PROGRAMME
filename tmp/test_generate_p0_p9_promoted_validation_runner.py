#!/usr/bin/env python3
"""Synthetic scope and fail-closed tests for the promoted P0--P9 runner generator."""

from __future__ import annotations

from pathlib import Path
import shutil
import sys
import tempfile

import test_audit_p0_p9_v56_evidence as evidence_fixture
from test_promote_step8b24_c6c2_p0_p9 import command, make_fixture


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="p0-p9-runner-generator-") as raw:
        fixture, head, targets = make_fixture(Path(raw))
        generator = "generate_p0_p9_promoted_validation_runner.py"
        shutil.copyfile(ROOT / "tmp" / generator, fixture / "tmp" / generator)
        evidence = fixture / "v56-pass.tar.gz"
        evidence_fixture.write_archive(evidence)
        promoted = command(
            sys.executable, "tmp/promote_step8b24_c6c2_p0_p9.py",
            "--expected-head", head, "--evidence", str(evidence), "--write",
            cwd=fixture,
        )
        if promoted.returncode:
            raise AssertionError("fixture promotion failed\n" + promoted.stdout)
        added = sorted(
            str(target_relative).replace("\\", "/")
            for target_relative in targets.values()
            if (fixture / target_relative).is_file()
        )
        result = command("git", "add", *added, cwd=fixture)
        if result.returncode:
            raise AssertionError("fixture add failed\n" + result.stdout)
        result = command("git", "commit", "-qm", "promoted graph", cwd=fixture)
        if result.returncode:
            raise AssertionError("fixture commit failed\n" + result.stdout)
        source_sha = command("git", "rev-parse", "HEAD", cwd=fixture).stdout.strip()
        output = fixture / "tmp/generated_promoted_runner.py"
        generated = command(
            sys.executable, "tmp/" + generator,
            "--source-sha", source_sha, "--output", str(output), cwd=fixture,
        )
        if generated.returncode or "P0_P9_PROMOTED_RUNNER_GENERATED" not in generated.stdout:
            raise AssertionError("runner generation failed\n" + generated.stdout)
        payload = output.read_text(encoding="utf-8")
        compile(payload, str(output), "exec")
        for target_relative in targets.values():
            path = str(target_relative).replace("\\", "/")
            if payload.count(path) < 2:
                raise AssertionError(f"promoted runner path missing from blobs/queue: {path}")
        if "axiom_headers=199" not in generated.stdout or "audits=20" not in generated.stdout:
            raise AssertionError("runner audit contract missing")

        victim = next(
            target_relative for source_relative, target_relative in targets.items()
            if source_relative.name.startswith("P9") and not source_relative.name.endswith("Audit.lean")
        )
        result = command("git", "rm", "-q", str(victim).replace("\\", "/"), cwd=fixture)
        if result.returncode:
            raise AssertionError("fixture removal failed\n" + result.stdout)
        result = command("git", "commit", "-qm", "remove one promoted target", cwd=fixture)
        if result.returncode:
            raise AssertionError("fixture removal commit failed\n" + result.stdout)
        broken_sha = command("git", "rev-parse", "HEAD", cwd=fixture).stdout.strip()
        broken = command(
            sys.executable, "tmp/" + generator,
            "--source-sha", broken_sha,
            "--output", str(fixture / "tmp/should-not-exist.py"), cwd=fixture,
        )
        if broken.returncode == 0 or "GIT_FAIL show" not in broken.stdout:
            raise AssertionError("missing promoted target did not fail closed\n" + broken.stdout)

    print(
        "P0_P9_PROMOTED_RUNNER_GENERATOR_SELFTEST_OK "
        "paths=39 audits=20 axiom_headers=199 syntax=pass "
        "missing_git_blob=fail_closed"
    )


if __name__ == "__main__":
    main()
