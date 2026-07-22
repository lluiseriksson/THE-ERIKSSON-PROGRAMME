"""Run hybrid009 units into an independent replay directory.

This is intentionally separate from the authoritative launcher: it never
touches the canonical ``scripts/certify_*hybrid_*.txt`` files.
"""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
import os
import subprocess
import sys

import certify_surface_remainder_delta0_r4_extension_009_hybrid as cert


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "certify_surface_remainder_delta0_r4_extension_009_hybrid_"


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def complete_for_head(path, head, slug):
    if not path.is_file():
        return False
    text = path.read_text(encoding="utf-8", errors="replace")
    return (f"PROVENANCE git_head {head}\n" in text
            and f"CERTIFIED UNIT regular K2 r4 hybrid009 {slug} " in text
            and "CERTIFICATE FAIL" not in text)


def run_one(slug, outdir):
    out = outdir / f"{PREFIX}{slug}.txt"
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(
        [str(ROOT / "scripts"), env.get("PYTHONPATH", "")]
    )
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" /
         "certify_surface_remainder_delta0_r4_extension_009_hybrid.py"),
         "--unit", slug],
        cwd=ROOT, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    out.write_bytes(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{slug} failed; see {out}")
    return slug


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay-dir", type=Path, required=True)
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    args.replay_dir.mkdir(parents=True, exist_ok=True)
    head = current_head()
    pending = [slug for slug in cert.unit_map()
               if not complete_for_head(
                   args.replay_dir / f"{PREFIX}{slug}.txt", head, slug)]
    print("HYBRID009 REPLAY LAUNCH", "head", head,
          "pending", len(pending), "workers", args.workers, flush=True)
    if not pending:
        print("HYBRID009 REPLAY ALL COMPLETE already current", flush=True)
        return 0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        it = iter(pending)
        live = {pool.submit(run_one, next(it), args.replay_dir)
                for _ in range(min(args.workers, len(pending)))}
        done_count = 0
        while live:
            done, live = wait(live, return_when=FIRST_COMPLETED)
            for f in done:
                f.result()
                done_count += 1
                print("HYBRID009 REPLAY COMPLETE", done_count,
                      "of", len(pending), flush=True)
                try:
                    live.add(pool.submit(run_one, next(it), args.replay_dir))
                except StopIteration:
                    pass
    print("HYBRID009 REPLAY ALL COMPLETE", len(pending), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
