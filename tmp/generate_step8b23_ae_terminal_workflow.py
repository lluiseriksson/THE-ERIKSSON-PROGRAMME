#!/usr/bin/env python3
"""Generate the single cold terminal workflow for Step 8b.23 Units A--E.

The workflow deliberately reuses ``validate-localized-carrier.yml`` because
that workflow path already exists on the repository default branch and is
therefore dispatchable at a draft-branch ref.  It compiles the immutable
source checkpoint, not its later workflow-vehicle child.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
RUNNER = runpy.run_path(str(ROOT / "tmp" / "generate_step8b23_ae_validation_runner.py"))
BRICKS: tuple[tuple[str, int], ...] = RUNNER["BRICKS"]
blob = RUNNER["blob"]
source_paths = RUNNER["source_paths"]

EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"


def indented(text: str, spaces: int) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + line if line else line for line in text.splitlines())


def generate_for_scope(
    source_sha: str,
    *,
    paths: list[str],
    bricks: tuple[tuple[str, int], ...],
    required_prevalidation: set[str],
    forbidden_prevalidation: set[str],
    workflow_name: str,
    job_id: str,
    archive_stem: str,
    expected_axioms: int,
) -> str:
    if set(required_prevalidation) & set(forbidden_prevalidation):
        raise SystemExit("PRE_VALIDATION_POLICY_OVERLAP")
    if set(required_prevalidation) | set(forbidden_prevalidation) != set(paths):
        raise SystemExit("PRE_VALIDATION_POLICY_SCOPE_MISMATCH")
    if len(paths) != len(set(paths)):
        raise SystemExit("DUPLICATE_SOURCE_PATH")
    if sum(count for _, count in bricks) != expected_axioms:
        raise SystemExit("AXIOM_TOTAL_MISMATCH")
    manifest_rows: list[str] = []
    for path in paths:
        data = blob(source_sha, path)
        text = data.decode("utf-8")
        if path in required_prevalidation and "PRE-VALIDATION:" not in text:
            raise SystemExit(f"MISSING_PRE_VALIDATION={path}")
        if path in forbidden_prevalidation and "PRE-VALIDATION:" in text:
            raise SystemExit(f"PREREQUISITE_NOT_SEALED={path}")
        manifest_rows.append(f"{hashlib.sha256(data).hexdigest()}  {path}")

    stages: list[str] = []
    expected: list[str] = []
    focal_modules: list[str] = []
    for index, (module, count) in enumerate(bricks, start=1):
        slug = module.removeprefix("Balaban").lower()
        focal = f"{index:02d}_{slug}_focal"
        audit = f"{index:02d}_{slug}_audit"
        stages.extend(
            (
                f"run_stage {focal} lake build YangMills.RG.{module}",
                f"run_stage {audit} lake env lean YangMills/RG/{module}Audit.lean",
            )
        )
        expected.append(f"    {audit!r}: {count},")
        focal_modules.append(f"    {focal!r}: {('YangMills/RG/' + module + '.lean')!r},")

    manifest = "\n".join(manifest_rows)
    run_stages = "\n".join(stages)
    expected_python = "\n".join(expected)
    focal_python = "\n".join(focal_modules)

    return f'''name: {workflow_name}

on:
  workflow_dispatch:
    inputs:
      cold:
        description: Require a cold checkout without project-graph restoration
        required: true
        default: true
        type: boolean

permissions:
  contents: read

env:
  SOURCE_SHA: {source_sha}
  EXPECTED_MATHLIB: {EXPECTED_MATHLIB}
  TOOLCHAIN_URL: {TOOLCHAIN_URL}
  TOOLCHAIN_SHA256: {TOOLCHAIN_SHA256}

jobs:
  {job_id}:
    runs-on: ubuntu-latest
    timeout-minutes: 360
    steps:
      - name: Require cold terminal mode
        shell: bash
        run: |
          set -euo pipefail
          test '${{{{ inputs.cold }}}}' = 'true'

      - name: Checkout exact source checkpoint
        uses: actions/checkout@v4
        with:
          ref: ${{{{ env.SOURCE_SHA }}}}
          fetch-depth: 1

      - name: Verify exact source checkpoint and {len(paths)} blobs
        shell: bash
        run: |
          set -euo pipefail
          mkdir -p evidence
          actual="$(git rev-parse HEAD)"
          printf 'SOURCE_SHA=%s\\nACTUAL_HEAD=%s\\nWORKFLOW_SHA=%s\\nCOLD_MODE=%s\\n' \\
            "$SOURCE_SHA" "$actual" "$GITHUB_SHA" '${{{{ inputs.cold }}}}' | \\
            tee evidence/checkpoint.txt
          test "$actual" = "$SOURCE_SHA"
          test "$(tr -d '\\r\\n' < lean-toolchain)" = "leanprover/lean4:v4.29.0-rc6"
          cat > evidence/source-blobs.sha256 <<'SOURCE_BLOBS'
{indented(manifest, 10)}
          SOURCE_BLOBS
          test "$(wc -l < evidence/source-blobs.sha256)" -eq {len(paths)}
          while read -r expected path; do
            actual_blob="$(git cat-file blob "$SOURCE_SHA:$path" | sha256sum | cut -d' ' -f1)"
            test "$actual_blob" = "$expected"
          done < evidence/source-blobs.sha256

      - name: Install exact Lean toolchain
        shell: bash
        run: |
          set -euo pipefail
          asset=/tmp/lean-4.29.0-rc6-linux.tar.zst
          curl --fail --location --retry 5 --retry-all-errors --retry-delay 2 \\
            -o "$asset" "$TOOLCHAIN_URL"
          printf '%s  %s\\n' "$TOOLCHAIN_SHA256" "$asset" | sha256sum -c -
          sudo apt-get update -qq
          sudo apt-get install -y -qq zstd
          mkdir -p /tmp/lean-toolchain
          tar --use-compress-program=unzstd -xf "$asset" -C /tmp/lean-toolchain
          bindir=/tmp/lean-toolchain/lean-4.29.0-rc6-linux/bin
          test -x "$bindir/lean"
          test -x "$bindir/lake"
          echo "$bindir" >> "$GITHUB_PATH"
          {{
            printf 'TOOLCHAIN_URL=%s\\nTOOLCHAIN_ASSET_SHA256=%s\\n' \\
              "$TOOLCHAIN_URL" "$TOOLCHAIN_SHA256"
            sha256sum "$bindir/lean" "$bindir/lake"
          }} | tee evidence/toolchain.txt

      - name: Materialize pinned dependencies
        shell: bash
        run: |
          set -euo pipefail
          lean --version | tee -a evidence/toolchain.txt
          lake --version | tee -a evidence/toolchain.txt
          manifest_before="$(sha256sum lake-manifest.json | cut -d' ' -f1)"
          toolchain_before="$(sha256sum lean-toolchain | cut -d' ' -f1)"
          lake update 2>&1 | tee evidence/lake-update.log
          test "$(sha256sum lake-manifest.json | cut -d' ' -f1)" = "$manifest_before"
          test "$(sha256sum lean-toolchain | cut -d' ' -f1)" = "$toolchain_before"
          mathlib="$(git -C .lake/packages/mathlib rev-parse HEAD)"
          printf 'MATHLIB_SHA=%s\\n' "$mathlib" | tee evidence/mathlib.txt
          test "$mathlib" = "$EXPECTED_MATHLIB"
          lake exe cache get 2>&1 | tee evidence/cache-get.log

      - name: Run {len(bricks)}-brick focal and audit queue stop on first error
        shell: bash
        run: |
          set -euo pipefail
          awk '{{print $2}}' evidence/source-blobs.sha256 > evidence/overlay-paths.txt
          python scripts/check_lean_overlay_text.py \\
            --paths-from evidence/overlay-paths.txt | tee evidence/text-guard.log
          mapfile -t overlay_paths < evidence/overlay-paths.txt
          python scripts/check_lean_import_prefix.py "${{overlay_paths[@]}}" | \\
            tee evidence/import-prefix-guard.log
          run_stage() {{
            local stage="$1"
            shift
            local started ended code
            started="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
            printf 'STAGE=%s STARTED=%s CMD=' "$stage" "$started" | tee -a evidence/stages.txt
            printf '%q ' "$@" | tee -a evidence/stages.txt
            printf '\\n' | tee -a evidence/stages.txt
            set +e
            "$@" 2>&1 | tee "evidence/${{stage}}.log"
            code=${{PIPESTATUS[0]}}
            set -e
            ended="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
            printf 'STAGE=%s EXIT=%s ENDED=%s\\n' "$stage" "$code" "$ended" | \\
              tee -a evidence/stages.txt
            test "$code" -eq 0
          }}

{indented(run_stages, 10)}

      - name: Verify {expected_axioms} axiom blocks and package cold evidence
        shell: bash
        run: |
          set -euo pipefail
          python - <<'PY'
          import json
          from pathlib import Path
          import re

          allowed = {{"propext", "Classical.choice", "Quot.sound"}}
          expected = {{
{indented(expected_python, 10)}
          }}
          focals = {{
{indented(focal_python, 10)}
          }}
          for stage, module_path in focals.items():
              text = Path(f"evidence/{{stage}}.log").read_text(encoding="utf-8")
              lines = [line.strip() for line in text.splitlines() if line.strip()]
              build = [line for line in lines if re.fullmatch(
                  r"Build completed successfully \\(\\d+ jobs\\)\\.", line
              )]
              if len(build) != 1 or lines[-1] != build[0]:
                  raise SystemExit(f"BAD_BUILD_SENTINEL={{stage}} count={{len(build)}}")
              if f"warning: {{module_path}}:" in text:
                  raise SystemExit(f"NEW_MODULE_LINTER_WARNING={{stage}}")
          parsed = {{}}
          total = 0
          for stage, count in expected.items():
              text = Path(f"evidence/{{stage}}.log").read_text(encoding="utf-8")
              compact = re.sub(r"\\s+", "", text)
              for forbidden in ("sorryAx", "ofReduceBool"):
                  if forbidden in compact:
                      raise SystemExit(f"FORBIDDEN_AXIOM={{forbidden}} STAGE={{stage}}")
              blocks = re.findall(r"dependsonaxioms:\\[([^\\]]*)\\]", compact)
              pure = compact.count("doesnotdependonanyaxioms")
              headers = len(blocks) + pure
              if headers != count:
                  raise SystemExit(
                      f"AXIOM_HEADER_COUNT={{headers}} EXPECTED={{count}} "
                      f"NONEMPTY={{len(blocks)}} EMPTY={{pure}} STAGE={{stage}}"
                  )
              values = []
              for body in blocks:
                  names = {{item for item in body.split(",") if item}}
                  if not names.issubset(allowed):
                      raise SystemExit(f"AXIOM_SET={{sorted(names)}} STAGE={{stage}}")
                  values.append(sorted(names))
              values.extend([[] for _ in range(pure)])
              parsed[stage] = values
              total += headers
          if total != {expected_axioms}:
              raise SystemExit(f"TOTAL_AXIOM_BLOCKS={{total}} EXPECTED={expected_axioms}")
          Path("evidence/axioms.json").write_text(
              json.dumps(parsed, sort_keys=True, indent=2) + "\\n", encoding="utf-8"
          )
          PY
          printf 'FINAL_STATUS=PASS\\n' | tee evidence/FINAL_STATUS
          sums="$(mktemp)"
          find evidence -maxdepth 1 -type f ! -name SHA256SUMS -print0 | \\
            sort -z | xargs -0 sha256sum > "$sums"
          mv "$sums" evidence/SHA256SUMS
          tar --sort=name --mtime='UTC 1970-01-01' --owner=0 --group=0 \\
            --numeric-owner -cf - evidence | gzip -n > {archive_stem}-evidence.tar.gz
          sha256sum {archive_stem}-evidence.tar.gz | tee evidence/ARCHIVE_SHA256

      - name: Upload durable evidence
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: {archive_stem}-${{{{ env.SOURCE_SHA }}}}
          path: |
            evidence
            {archive_stem}-evidence.tar.gz
          if-no-files-found: error
          retention-days: 14
'''


def generate(source_sha: str) -> str:
    paths: list[str] = source_paths()
    return generate_for_scope(
        source_sha,
        paths=paths,
        bricks=BRICKS,
        required_prevalidation=set(paths),
        forbidden_prevalidation=set(),
        workflow_name="Validate Step 8b.23 Units A-E",
        job_id="step8b23-ae",
        archive_stem="step8b23-ae",
        expected_axioms=124,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".github" / "workflows" / "validate-localized-carrier.yml",
    )
    args = parser.parse_args()
    content = generate(args.source_sha)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "STEP8B23_AE_TERMINAL_WORKFLOW_GENERATED "
        f"source_sha={args.source_sha} files=36 stages=36 axiom_blocks=124 "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
