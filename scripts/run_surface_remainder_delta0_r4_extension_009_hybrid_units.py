"""Resumable local launcher for the frozen hybrid009 production units."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
from pathlib import Path
import subprocess
import sys
import time

import certify_surface_remainder_delta0_r4_extension_009_hybrid as cert


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "certify_surface_remainder_delta0_r4_extension_009_hybrid_"


def output_path(slug):
    return ROOT / "scripts" / f"{PREFIX}{slug}.txt"


def current_head():
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}",
         "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def complete_for_head(slug, head):
    path = output_path(slug)
    if not path.exists():
        return False
    text = path.read_text(encoding="utf-8", errors="replace")
    return (
        f"PROVENANCE git_head {head}\n" in text
        and f"CERTIFIED UNIT regular K2 r4 hybrid009 {slug} " in text
        and "CERTIFICATE FAIL" not in text
    )


def run_one(slug, head):
    path = output_path(slug)
    temporary = path.with_suffix(f".{os.getpid()}.tmp")
    lock = path.with_suffix(".lock")
    try:
        lock_handle = lock.open("x", encoding="utf-8")
    except FileExistsError as exc:
        raise RuntimeError(f"{slug} already has an active lock") from exc
    lock_handle.write(f"pid={os.getpid()} head={head}\n")
    lock_handle.close()
    env = os.environ.copy()
    pythonpath = [str(ROOT / "scripts")]
    inherited = env.get("PYTHONPATH")
    if inherited:
        pythonpath.append(inherited)
    env["PYTHONPATH"] = os.pathsep.join(pythonpath)
    try:
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts" /
             "certify_surface_remainder_delta0_r4_extension_009_hybrid.py"),
             "--unit", slug],
            cwd=ROOT,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=None,
        )
        temporary.write_bytes(result.stdout)
        if result.returncode != 0:
            failed = path.with_suffix(".failed.txt")
            temporary.replace(failed)
            raise RuntimeError(f"{slug} failed; see {failed.name}")
        temporary.replace(path)
        if not complete_for_head(slug, head):
            raise RuntimeError(
                f"{slug} lacks its terminal/provenance contract")
        return slug
    finally:
        # Windows indexers/antivirus can retain a just-closed lock file for
        # a short interval.  The certificate may already be complete; retry
        # cleanup without rerunning or weakening its terminal contract.
        for attempt in range(20):
            try:
                lock.unlink(missing_ok=True)
                break
            except PermissionError:
                if attempt == 19:
                    raise
                time.sleep(0.1)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, choices=(1, 2), default=2)
    parser.add_argument(
        "--max-units", type=int, default=None,
        help="run at most this many pending units (for resource-safe resumes)")
    args = parser.parse_args()
    head = current_head()
    pending = [slug for slug in cert.unit_map()
               if not complete_for_head(slug, head)]
    if args.max_units is not None:
        if args.max_units < 1:
            parser.error("--max-units must be positive")
        pending = pending[:args.max_units]
    print("HYBRID009 LAUNCH", "head", head, "pending", len(pending),
          "workers", args.workers, flush=True)
    if not pending:
        print("HYBRID009 LAUNCH COMPLETE already current", flush=True)
        return 0
    iterator = iter(pending)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        live = {pool.submit(run_one, next(iterator), head)
                for _ in range(min(args.workers, len(pending)))}
        completed = 0
        while live:
            done, live = wait(live, return_when=FIRST_COMPLETED)
            for future in done:
                slug = future.result()
                completed += 1
                print("HYBRID009 UNIT COMPLETE", slug, completed,
                      "of", len(pending), flush=True)
                try:
                    next_slug = next(iterator)
                except StopIteration:
                    continue
                live.add(pool.submit(run_one, next_slug, head))
    print("HYBRID009 LAUNCH COMPLETE", len(pending), "new units", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
