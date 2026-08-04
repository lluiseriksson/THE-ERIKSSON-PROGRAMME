#!/usr/bin/env python3
"""Fail-closed external verifier for the PR #39 instrumental bundle.

The verifier treats checkpoint A as the immutable source checkpoint and HEAD
as evidence commit B.  Acceptance-relevant sources are read from Git objects,
not from the checkout.  The checkout copy of this verifier is additionally
matched to its checkpoint-A blob before it is allowed to emit PASS.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn


SCHEMA = "pr39-instrumental-bundle-v2"
MANIFEST_PATH = (
    "docs/oracle-transcripts/PR39-INSTRUMENTAL-REPAIR-MANIFEST-20260731.json"
)
TRANSCRIPT_PATH = "docs/oracle-transcripts/PR39-INSTRUMENTAL-REPAIR-20260731.txt"
CERTIFICATE_PATH = "scripts/certify_su2_two_transporter_nogo.py"
ORACLE_PATH = "docs/SU2-TWO-TRANSPORTER-NOGO-ORACLE.lean"
MATHEMATICS_PATH = "YangMills/OS/TwoTransporterHaarProjection.lean"
VERIFIER_PATH = "scripts/verify_pr39_instrumental_bundle.py"
ALLOWED_EVIDENCE_PATHS = (MANIFEST_PATH, TRANSCRIPT_PATH)
EXPECTED_BASE_SHA = "5172a51b0fad455d9009b1805a48b8be54acbbcc"
EXPECTED_CERTIFICATE_OID = "9fac6370bb016d674465da6110c701e24f5f9de8"
EXPECTED_ORACLE_OID = "0b10c1ecebe1791cbdf6d3e02dbb5c7e2ecd6606"
EXPECTED_MATHEMATICS_OID = "e785ce28d92cb7a8d77a5ef901e8fd860f5b0c36"
EXPECTED_CERTIFICATE_CHECKS = 14
EXPECTED_VERIFIER_CHECKS = 313
CERTIFICATE_MUTATIONS = ("decisive-trace", "witness-condition", "omit-check")
ORACLE_HEADLINES = (
    "integral_weight_mul_inv_eq",
    "orientationD_inner_projection",
    "orientationD_twoTransporter_projection",
    "orientationE_uv_projection",
    "orientationE_twoTransporter_projection",
    "quadraticD_eq_partition_mul_mean_sq",
    "quadraticE_eq_partition_mul_mean_sq",
    "su2_trace_conjugate_inverse",
    "su2_trace_inv_eq",
    "su2WilsonWeight_conjugationInverseInvariant",
    "su2Wilson_orientationD_inner_projection",
    "su2Wilson_orientationD_twoTransporter_projection",
    "su2Wilson_orientationE_uv_projection",
    "su2Wilson_orientationE_twoTransporter_projection",
    "su2Wilson_quadraticD_eq_partition_mul_mean_sq",
    "su2Wilson_quadraticE_eq_partition_mul_mean_sq",
)
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
PASS_TOKEN = "PR39 EXTERNAL INSTRUMENTAL VERIFIER: PASS"
ERROR_PREFIX = "PR39 VERIFIER ERROR:"

CONTRACT: dict[str, Any] = {
    "schema": SCHEMA,
    "repository": "lluiseriksson/THE-ERIKSSON-PROGRAMME",
    "pull_request": 39,
    "pull_request_state": "draft",
    "remote_branch": "codex/su2-two-transporter-nogo-20260731",
    "paths": {
        "manifest": MANIFEST_PATH,
        "transcript": TRANSCRIPT_PATH,
        "certificate": CERTIFICATE_PATH,
        "oracle": ORACLE_PATH,
        "mathematics": MATHEMATICS_PATH,
        "verifier": VERIFIER_PATH,
    },
    "allowed_evidence_paths": list(ALLOWED_EVIDENCE_PATHS),
    "expected_base_sha": EXPECTED_BASE_SHA,
    "literal_source_oids": {
        "certificate": EXPECTED_CERTIFICATE_OID,
        "oracle": EXPECTED_ORACLE_OID,
        "mathematics": EXPECTED_MATHEMATICS_OID,
    },
    "expected_certificate_checks": EXPECTED_CERTIFICATE_CHECKS,
    "certificate_mutations": list(CERTIFICATE_MUTATIONS),
    "oracle_headlines": list(ORACLE_HEADLINES),
    "commits_after_checkpoint_a": 1,
    "eol_policy": (
        "raw hashes cover exact Git-blob or process bytes; LF hashes remove every "
        "CR byte before SHA-256; Git-blob raw bytes are canonical"
    ),
}


class VerificationFailure(Exception):
    """A fail-closed rejection of the proposed instrumental bundle."""


@dataclass
class Ledger:
    count: int = 0

    def require(self, condition: bool, label: str) -> None:
        self.count += 1
        if not condition:
            raise VerificationFailure(f"check {self.count} failed: {label}")

    def close(self) -> None:
        if self.count != EXPECTED_VERIFIER_CHECKS:
            raise VerificationFailure(
                "verifier check-count mismatch: "
                f"observed {self.count}, expected {EXPECTED_VERIFIER_CHECKS}"
            )


def reject(message: str) -> NoReturn:
    raise VerificationFailure(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def lf_bytes(data: bytes) -> bytes:
    return data.replace(b"\r", b"")


def canonical_json(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def payload_sha256(manifest: dict[str, Any]) -> str:
    unsigned = dict(manifest)
    unsigned.pop("payload_sha256", None)
    return sha256(canonical_json(unsigned))


def contract_sha256() -> str:
    return sha256(canonical_json(CONTRACT))


def run_process(
    command: list[str],
    *,
    cwd: Path,
    input_bytes: bytes | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            input=input_bytes,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            env=env,
        )
    except OSError as exc:
        reject(f"cannot execute {command[0]!r}: {exc}")


def git(
    root: Path, *arguments: str, input_bytes: bytes | None = None
) -> subprocess.CompletedProcess[bytes]:
    completed = run_process(
        ["git", *arguments], cwd=root, input_bytes=input_bytes
    )
    return completed


def git_ok(root: Path, *arguments: str, input_bytes: bytes | None = None) -> bytes:
    completed = git(root, *arguments, input_bytes=input_bytes)
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        reject(f"git {' '.join(arguments)} failed ({completed.returncode}): {detail}")
    return completed.stdout


def resolve_root() -> Path:
    completed = run_process(
        ["git", "rev-parse", "--show-toplevel"], cwd=Path.cwd()
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        reject(f"not inside the target Git repository: {detail}")
    try:
        return Path(completed.stdout.decode("utf-8").strip()).resolve()
    except UnicodeDecodeError as exc:
        reject(f"repository path is not UTF-8: {exc}")


def decode_utf8(data: bytes, label: str) -> str:
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as exc:
        reject(f"{label} is not UTF-8: {exc}")


def git_blob(root: Path, revision: str, path: str) -> bytes:
    return git_ok(root, "show", f"{revision}:{path}")


def git_blob_oid(root: Path, data: bytes) -> str:
    return decode_utf8(
        git_ok(root, "hash-object", "--stdin", input_bytes=data), "blob OID"
    ).strip()


def git_path_oid(root: Path, revision: str, path: str) -> str:
    return decode_utf8(
        git_ok(root, "rev-parse", f"{revision}:{path}"), f"{path} blob OID"
    ).strip()


def exact_keys(
    ledger: Ledger, value: dict[str, Any], expected: set[str], label: str
) -> None:
    ledger.require(set(value) == expected, f"{label} keys must be exactly {sorted(expected)}")


def require_mapping(ledger: Ledger, value: Any, label: str) -> dict[str, Any]:
    ledger.require(isinstance(value, dict), f"{label} must be an object")
    return value


def require_list(ledger: Ledger, value: Any, label: str) -> list[Any]:
    ledger.require(isinstance(value, list), f"{label} must be an array")
    return value


def verify_hash_record(
    ledger: Ledger,
    root: Path,
    checkpoint: str,
    head: str,
    label: str,
    record_value: Any,
) -> bytes:
    record = require_mapping(ledger, record_value, f"protected_blobs.{label}")
    exact_keys(
        ledger,
        record,
        {"path", "raw_sha256", "lf_sha256", "git_blob_oid"},
        f"protected_blobs.{label}",
    )
    expected_path = CONTRACT["paths"][label]
    ledger.require(record.get("path") == expected_path, f"{label} path changed")
    checkpoint_blob = git_blob(root, checkpoint, expected_path)
    head_blob = git_blob(root, head, expected_path)
    ledger.require(head_blob == checkpoint_blob, f"{label} was edited after checkpoint A")
    ledger.require(
        record.get("raw_sha256") == sha256(checkpoint_blob),
        f"{label} raw SHA-256 mismatch",
    )
    ledger.require(
        record.get("lf_sha256") == sha256(lf_bytes(checkpoint_blob)),
        f"{label} LF SHA-256 mismatch",
    )
    ledger.require(
        record.get("git_blob_oid") == git_blob_oid(root, checkpoint_blob),
        f"{label} Git blob OID mismatch",
    )
    return checkpoint_blob


def assignment_literal(module: ast.Module, name: str) -> Any:
    matches: list[Any] = []
    for statement in module.body:
        if isinstance(statement, (ast.Assign, ast.AnnAssign)):
            targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
            if any(isinstance(target, ast.Name) and target.id == name for target in targets):
                try:
                    matches.append(ast.literal_eval(statement.value))
                except (ValueError, TypeError):
                    matches.append(None)
    if len(matches) != 1:
        return None
    return matches[0]


def find_function(module: ast.Module, name: str) -> ast.FunctionDef | None:
    matches = [node for node in ast.walk(module) if isinstance(node, ast.FunctionDef) and node.name == name]
    if len(matches) != 1:
        return None
    return matches[0]


def call_name(call: ast.Call) -> str | None:
    if isinstance(call.func, ast.Name):
        return call.func.id
    if isinstance(call.func, ast.Attribute):
        return call.func.attr
    return None


def call_lines(function: ast.FunctionDef, names: set[str]) -> dict[str, list[int]]:
    result = {name: [] for name in names}
    for node in ast.walk(function):
        if isinstance(node, ast.Call):
            name = call_name(node)
            if name in result:
                result[name].append(node.lineno)
    return result


def verify_certificate_ast(ledger: Ledger, source: bytes) -> None:
    text = decode_utf8(source, CERTIFICATE_PATH)
    try:
        module = ast.parse(text, filename=CERTIFICATE_PATH)
    except SyntaxError as exc:
        reject(f"certificate AST parse failed: {exc}")
    ledger.require(not any(isinstance(node, ast.Assert) for node in ast.walk(module)), "certificate contains decisive assert")
    ledger.require(
        assignment_literal(module, "EXPECTED_CHECKS") == EXPECTED_CERTIFICATE_CHECKS,
        "certificate EXPECTED_CHECKS is not 14",
    )
    ledger.require(
        assignment_literal(module, "MUTATIONS") == CERTIFICATE_MUTATIONS,
        "certificate mutation contract changed",
    )
    check_functions: list[ast.FunctionDef] = []
    for name in ("finite_word_checks", "quaternion_checks"):
        function = find_function(module, name)
        ledger.require(function is not None, f"missing unique certificate function {name}")
        if function is not None:
            check_functions.append(function)
    require_calls = [
        node
        for function in check_functions
        for node in ast.walk(function)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "checks"
        and node.func.attr == "require"
    ]
    ledger.require(
        len(require_calls) == EXPECTED_CERTIFICATE_CHECKS,
        "certificate must contain exactly 14 checks.require calls",
    )

    ledger_class = next(
        (
            node
            for node in module.body
            if isinstance(node, ast.ClassDef) and node.name == "CheckLedger"
        ),
        None,
    )
    ledger.require(ledger_class is not None, "missing CheckLedger class")
    require_method = None
    close_method = None
    if ledger_class is not None:
        require_method = next(
            (node for node in ledger_class.body if isinstance(node, ast.FunctionDef) and node.name == "require"),
            None,
        )
        close_method = next(
            (node for node in ledger_class.body if isinstance(node, ast.FunctionDef) and node.name == "close"),
            None,
        )
    ledger.require(require_method is not None, "missing CheckLedger.require")
    ledger.require(close_method is not None, "missing CheckLedger.close")
    if require_method is not None:
        increments = [
            node
            for node in ast.walk(require_method)
            if isinstance(node, ast.AugAssign)
            and isinstance(node.target, ast.Attribute)
            and isinstance(node.target.value, ast.Name)
            and node.target.value.id == "self"
            and node.target.attr == "count"
            and isinstance(node.op, ast.Add)
            and isinstance(node.value, ast.Constant)
            and node.value.value == 1
        ]
        ledger.require(len(increments) == 1, "check counter increment changed")
        ledger.require(
            any(isinstance(node, ast.Raise) for node in ast.walk(require_method)),
            "CheckLedger.require no longer raises",
        )
    if close_method is not None:
        ledger.require(
            any(
                isinstance(node, ast.Compare)
                and any(isinstance(operator, ast.NotEq) for operator in node.ops)
                for node in ast.walk(close_method)
            ),
            "CheckLedger.close lost its mismatch comparison",
        )
        ledger.require(
            any(isinstance(node, ast.Raise) for node in ast.walk(close_method)),
            "CheckLedger.close no longer raises",
        )

    certify = find_function(module, "certify")
    ledger.require(certify is not None, "missing unique certify function")
    if certify is None:
        return
    lines = call_lines(
        certify, {"finite_word_checks", "quaternion_checks", "close", "print"}
    )
    for name in ("finite_word_checks", "quaternion_checks", "close", "print"):
        ledger.require(len(lines[name]) == 1, f"certify must call {name} exactly once")
    if all(len(lines[name]) == 1 for name in lines):
        ledger.require(
            lines["finite_word_checks"][0]
            < lines["quaternion_checks"][0]
            < lines["close"][0]
            < lines["print"][0],
            "certificate finalize/print order changed",
        )
    pass_constants = [
        node
        for node in ast.walk(certify)
        if isinstance(node, ast.Constant) and node.value == "RESULT: PASS"
    ]
    ledger.require(len(pass_constants) == 1, "certify PASS literal count changed")
    if pass_constants and lines["close"] and lines["print"]:
        ledger.require(
            lines["close"][0] < pass_constants[0].lineno < lines["print"][0],
            "certificate PASS moved before finalize or after print",
        )
    check_fragments = [
        node
        for node in ast.walk(certify)
        if isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and node.value.startswith("CHECKS:")
    ]
    ledger.require(len(check_fragments) == 1, "certify CHECKS output changed")
    if check_fragments and pass_constants:
        ledger.require(
            check_fragments[0].lineno <= pass_constants[0].lineno,
            "certificate PASS precedes the check-count output",
        )


def verify_verifier_ast(ledger: Ledger, source: bytes) -> None:
    text = decode_utf8(source, VERIFIER_PATH)
    try:
        module = ast.parse(text, filename=VERIFIER_PATH)
    except SyntaxError as exc:
        reject(f"verifier AST parse failed: {exc}")
    ledger.require(
        not any(isinstance(node, ast.Assert) for node in ast.walk(module)),
        "external verifier contains decisive assert",
    )
    ledger.require(
        assignment_literal(module, "EXPECTED_VERIFIER_CHECKS")
        == EXPECTED_VERIFIER_CHECKS,
        "verifier explicit check-count contract changed",
    )
    ledger.require(
        assignment_literal(module, "PASS_TOKEN") == PASS_TOKEN,
        "verifier PASS token changed",
    )


def parse_oracle(ledger: Ledger, source: bytes) -> list[str]:
    text = decode_utf8(source, ORACLE_PATH)
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    expected_import = "import YangMills.OS.TwoTransporterHaarProjection"
    ledger.require(bool(lines) and lines[0] == expected_import, "oracle import changed")
    pattern = re.compile(
        r"#print axioms YangMills\.OS\.TwoTransporterHaarProjection\.([A-Za-z0-9_]+)\Z"
    )
    headlines: list[str] = []
    for line in lines[1:]:
        match = pattern.fullmatch(line)
        ledger.require(match is not None, f"unexpected oracle line: {line!r}")
        if match is not None:
            headlines.append(match.group(1))
    ledger.require(len(headlines) == len(ORACLE_HEADLINES), "oracle headline count is not 16")
    ledger.require(len(set(headlines)) == len(headlines), "oracle contains a duplicate headline")
    ledger.require(tuple(headlines) == ORACLE_HEADLINES, "oracle headline sequence changed")
    return headlines


def hash_observation(data: bytes) -> dict[str, str]:
    return {"raw_sha256": sha256(data), "lf_sha256": sha256(lf_bytes(data))}


def expected_run_keys() -> set[str]:
    return {
        "label",
        "optimize",
        "exit_code",
        "stdout_raw_sha256",
        "stdout_lf_sha256",
        "stderr_raw_sha256",
        "stderr_lf_sha256",
        "result_pass_hits",
    }


def run_certificate(
    script: Path, optimize: int, extra: list[str], cwd: Path
) -> subprocess.CompletedProcess[bytes]:
    flags = ["-O"] if optimize == 1 else []
    environment = dict(os.environ)
    environment.update(
        {
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONHASHSEED": "0",
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
        }
    )
    return run_process(
        [sys.executable, *flags, str(script), *extra], cwd=cwd, env=environment
    )


def compare_run(
    ledger: Ledger,
    actual: subprocess.CompletedProcess[bytes],
    expected_value: Any,
    label: str,
    optimize: int,
) -> None:
    expected = require_mapping(ledger, expected_value, f"execution {label}")
    exact_keys(ledger, expected, expected_run_keys(), f"execution {label}")
    ledger.require(expected.get("label") == label, f"execution label changed: {label}")
    ledger.require(expected.get("optimize") == optimize, f"optimization flag changed: {label}")
    ledger.require(expected.get("exit_code") == actual.returncode, f"exit code mismatch: {label}")
    stdout_hashes = hash_observation(actual.stdout)
    stderr_hashes = hash_observation(actual.stderr)
    for key, value in stdout_hashes.items():
        ledger.require(expected.get(f"stdout_{key}") == value, f"stdout {key} mismatch: {label}")
    for key, value in stderr_hashes.items():
        ledger.require(expected.get(f"stderr_{key}") == value, f"stderr {key} mismatch: {label}")
    pass_hits = (actual.stdout + actual.stderr).count(b"RESULT: PASS")
    ledger.require(expected.get("result_pass_hits") == pass_hits, f"PASS count mismatch: {label}")


def verify_executions(
    ledger: Ledger, certificate_blob: bytes, execution_value: Any
) -> None:
    execution = require_mapping(ledger, execution_value, "execution")
    exact_keys(
        ledger,
        execution,
        {"certificate_runs", "self_tests", "mutations", "stale_pass"},
        "execution",
    )
    with tempfile.TemporaryDirectory(prefix="pr39-verifier-") as temp_name:
        temp_root = Path(temp_name)
        script = temp_root / "certificate.py"
        script.write_bytes(certificate_blob)

        certificate_runs = require_list(
            ledger, execution.get("certificate_runs"), "execution.certificate_runs"
        )
        expected_acceptance = (
            ("normal_1", 0),
            ("normal_2", 0),
            ("optimized_1", 1),
            ("optimized_2", 1),
        )
        ledger.require(
            len(certificate_runs) == len(expected_acceptance),
            "certificate run count changed",
        )
        acceptance_results: list[subprocess.CompletedProcess[bytes]] = []
        for index, (label, optimize) in enumerate(expected_acceptance):
            actual = run_certificate(script, optimize, [], temp_root)
            acceptance_results.append(actual)
            if index < len(certificate_runs):
                compare_run(ledger, actual, certificate_runs[index], label, optimize)
            ledger.require(actual.returncode == 0, f"acceptance run failed: {label}")
            ledger.require(
                actual.stdout.count(b"RESULT: PASS") == 1,
                f"acceptance run did not emit exactly one PASS: {label}",
            )
            ledger.require(not actual.stderr, f"acceptance stderr is not empty: {label}")
        if len(acceptance_results) == len(expected_acceptance):
            baseline = acceptance_results[0].stdout
            ledger.require(
                all(result.stdout == baseline for result in acceptance_results[1:]),
                "normal/optimized certificate stdout is not deterministic",
            )

        self_tests = require_list(
            ledger, execution.get("self_tests"), "execution.self_tests"
        )
        expected_self_tests = (("self_test_normal", 0), ("self_test_optimized", 1))
        ledger.require(len(self_tests) == 2, "self-test run count changed")
        self_test_results: list[subprocess.CompletedProcess[bytes]] = []
        for index, (label, optimize) in enumerate(expected_self_tests):
            actual = run_certificate(script, optimize, ["--self-test"], temp_root)
            self_test_results.append(actual)
            if index < len(self_tests):
                compare_run(ledger, actual, self_tests[index], label, optimize)
            ledger.require(actual.returncode == 0, f"certificate self-test failed: {label}")
            ledger.require(not actual.stderr, f"self-test stderr is not empty: {label}")
        if len(self_test_results) == 2:
            ledger.require(
                self_test_results[0].stdout == self_test_results[1].stdout,
                "normal/optimized self-test stdout differs",
            )

        mutations = require_list(
            ledger, execution.get("mutations"), "execution.mutations"
        )
        expected_mutations = tuple(
            (f"mutation_{mutation}_{mode}", optimize, mutation)
            for mutation in CERTIFICATE_MUTATIONS
            for mode, optimize in (("normal", 0), ("optimized", 1))
        )
        ledger.require(
            len(mutations) == len(expected_mutations), "mutation run count changed"
        )
        mutation_results: list[tuple[str, int, str, subprocess.CompletedProcess[bytes]]] = []
        for index, (label, optimize, mutation) in enumerate(expected_mutations):
            actual = run_certificate(
                script, optimize, ["--_mutation", mutation], temp_root
            )
            mutation_results.append((label, optimize, mutation, actual))
            if index < len(mutations):
                compare_run(ledger, actual, mutations[index], label, optimize)
            ledger.require(actual.returncode != 0, f"mutation was accepted: {label}")
            ledger.require(
                b"RESULT: PASS" not in actual.stdout + actual.stderr,
                f"mutation emitted stale PASS: {label}",
            )

        stale = require_mapping(ledger, execution.get("stale_pass"), "execution.stale_pass")
        exact_keys(
            ledger,
            stale,
            {"seed_sha256", "tested_labels", "stdout_open_mode"},
            "execution.stale_pass",
        )
        stale_seed = b"RESULT: PASS\n"
        ledger.require(stale.get("seed_sha256") == sha256(stale_seed), "stale PASS seed hash changed")
        ledger.require(stale.get("stdout_open_mode") == "wb", "stale PASS truncation mode changed")
        ledger.require(
            stale.get("tested_labels") == [item[0] for item in expected_mutations],
            "stale PASS tested-label sequence changed",
        )
        environment = dict(os.environ)
        environment.update(
            {
                "PYTHONDONTWRITEBYTECODE": "1",
                "PYTHONHASHSEED": "0",
                "LC_ALL": "C",
                "LANG": "C",
                "TZ": "UTC",
            }
        )
        for label, optimize, mutation, recorded in mutation_results:
            stdout_file = temp_root / f"{label}.stdout"
            stdout_file.write_bytes(stale_seed)
            flags = ["-O"] if optimize == 1 else []
            try:
                with stdout_file.open("wb") as output:
                    replay = subprocess.run(
                        [
                            sys.executable,
                            *flags,
                            str(script),
                            "--_mutation",
                            mutation,
                        ],
                        cwd=temp_root,
                        stdout=output,
                        stderr=subprocess.PIPE,
                        check=False,
                        env=environment,
                    )
            except OSError as exc:
                reject(f"cannot execute stale-PASS replay {label}: {exc}")
            replay_stdout = stdout_file.read_bytes()
            ledger.require(replay.returncode != 0, f"stale-PASS replay accepted: {label}")
            ledger.require(replay_stdout == recorded.stdout, f"stale-PASS replay stdout differs: {label}")
            ledger.require(replay.stderr == recorded.stderr, f"stale-PASS replay stderr differs: {label}")
            ledger.require(b"RESULT: PASS" not in replay_stdout, f"stale PASS survived truncation: {label}")


def verify_bundle(root: Path, head_argument: str) -> bytes:
    ledger = Ledger()
    head = decode_utf8(git_ok(root, "rev-parse", f"{head_argument}^{{commit}}"), "HEAD").strip()
    ledger.require(bool(re.fullmatch(r"[0-9a-f]{40}", head)), "HEAD is not a full commit ID")
    manifest_blob = git_blob(root, head, MANIFEST_PATH)
    manifest_text = decode_utf8(manifest_blob, MANIFEST_PATH)
    try:
        manifest_value = json.loads(manifest_text)
    except json.JSONDecodeError as exc:
        reject(f"manifest JSON parse failed: {exc}")
    manifest = require_mapping(ledger, manifest_value, "manifest")
    exact_keys(
        ledger,
        manifest,
        {
            "schema",
            "repository",
            "pull_request",
            "pull_request_state",
            "remote_branch",
            "checkpoint_a",
            "contract_sha256",
            "payload_sha256",
            "eol_policy",
            "evidence_policy",
            "protected_blobs",
            "certificate_contract",
            "oracle_contract",
            "execution",
            "verifier_execution",
            "audit_status",
        },
        "manifest",
    )
    ledger.require(manifest.get("payload_sha256") == payload_sha256(manifest), "manifest payload SHA-256 mismatch")
    for key in ("schema", "repository", "pull_request", "pull_request_state", "remote_branch"):
        ledger.require(manifest.get(key) == CONTRACT[key], f"manifest {key} changed")
    ledger.require(manifest.get("contract_sha256") == contract_sha256(), "verifier contract SHA-256 mismatch")
    ledger.require(manifest.get("eol_policy") == CONTRACT["eol_policy"], "EOL policy changed")
    ledger.require(
        manifest.get("audit_status") == "fresh independent audit required",
        "fresh-audit status changed",
    )

    checkpoint = manifest.get("checkpoint_a")
    ledger.require(
        isinstance(checkpoint, str) and bool(re.fullmatch(r"[0-9a-f]{40}", checkpoint)),
        "checkpoint A must be a full commit ID",
    )
    if not isinstance(checkpoint, str):
        reject("checkpoint A is not a string")
    exists = git(root, "cat-file", "-e", f"{checkpoint}^{{commit}}")
    ledger.require(exists.returncode == 0, "checkpoint A does not exist")
    resolved_base = decode_utf8(
        git_ok(root, "rev-parse", f"{EXPECTED_BASE_SHA}^{{commit}}"),
        "literal base commit",
    ).strip()
    ledger.require(resolved_base == EXPECTED_BASE_SHA, "literal base commit changed")
    base_ancestor = git(root, "merge-base", "--is-ancestor", EXPECTED_BASE_SHA, checkpoint)
    ledger.require(base_ancestor.returncode == 0, "literal base is not an ancestor of checkpoint A")
    for label, path, expected_oid in (
        ("certificate", CERTIFICATE_PATH, EXPECTED_CERTIFICATE_OID),
        ("oracle", ORACLE_PATH, EXPECTED_ORACLE_OID),
        ("mathematics", MATHEMATICS_PATH, EXPECTED_MATHEMATICS_OID),
    ):
        resolved_oid = git_path_oid(root, checkpoint, path)
        ledger.require(
            resolved_oid == expected_oid,
            f"{label} Git blob OID differs from literal trust anchor",
        )
    ancestor = git(root, "merge-base", "--is-ancestor", checkpoint, head)
    ledger.require(ancestor.returncode == 0, "checkpoint A is not an ancestor of HEAD")
    count_text = decode_utf8(git_ok(root, "rev-list", "--count", f"{checkpoint}..{head}"), "commit count").strip()
    ledger.require(count_text == "1", "A..HEAD must contain exactly evidence commit B")
    parent = decode_utf8(git_ok(root, "rev-parse", f"{head}^"), "HEAD parent").strip()
    ledger.require(parent == checkpoint, "checkpoint A must be the direct parent of evidence commit B")

    evidence_policy = require_mapping(ledger, manifest.get("evidence_policy"), "evidence_policy")
    exact_keys(
        ledger,
        evidence_policy,
        {"allowed_paths", "commits_after_checkpoint_a", "transcript"},
        "evidence_policy",
    )
    ledger.require(
        evidence_policy.get("allowed_paths") == list(ALLOWED_EVIDENCE_PATHS),
        "allowed evidence paths changed",
    )
    ledger.require(
        evidence_policy.get("commits_after_checkpoint_a") == 1,
        "evidence commit-count policy changed",
    )
    changed_raw = git_ok(root, "diff", "--name-only", "-z", checkpoint, head)
    changed_paths = [decode_utf8(item, "changed path") for item in changed_raw.split(b"\0") if item]
    ledger.require(
        sorted(changed_paths) == sorted(ALLOWED_EVIDENCE_PATHS),
        f"A..HEAD paths are not the exact allowed evidence set: {changed_paths}",
    )
    transcript_record = require_mapping(
        ledger, evidence_policy.get("transcript"), "evidence_policy.transcript"
    )
    exact_keys(
        ledger,
        transcript_record,
        {"path", "raw_sha256", "lf_sha256", "git_blob_oid"},
        "evidence_policy.transcript",
    )
    ledger.require(transcript_record.get("path") == TRANSCRIPT_PATH, "transcript path changed")
    transcript_blob = git_blob(root, head, TRANSCRIPT_PATH)
    ledger.require(transcript_record.get("raw_sha256") == sha256(transcript_blob), "transcript raw SHA-256 mismatch")
    ledger.require(transcript_record.get("lf_sha256") == sha256(lf_bytes(transcript_blob)), "transcript LF SHA-256 mismatch")
    ledger.require(transcript_record.get("git_blob_oid") == git_blob_oid(root, transcript_blob), "transcript blob OID mismatch")

    protected = require_mapping(ledger, manifest.get("protected_blobs"), "protected_blobs")
    exact_keys(
        ledger,
        protected,
        {"certificate", "oracle", "mathematics", "verifier"},
        "protected_blobs",
    )
    certificate_blob = verify_hash_record(ledger, root, checkpoint, head, "certificate", protected.get("certificate"))
    oracle_blob = verify_hash_record(ledger, root, checkpoint, head, "oracle", protected.get("oracle"))
    verify_hash_record(ledger, root, checkpoint, head, "mathematics", protected.get("mathematics"))
    verifier_blob = verify_hash_record(ledger, root, checkpoint, head, "verifier", protected.get("verifier"))

    checkout_verifier = Path(__file__).resolve().read_bytes()
    ledger.require(
        sha256(lf_bytes(checkout_verifier)) == sha256(lf_bytes(verifier_blob)),
        "executing verifier does not match checkpoint-A verifier blob under EOL policy",
    )
    verify_certificate_ast(ledger, certificate_blob)
    verify_verifier_ast(ledger, verifier_blob)

    certificate_contract = require_mapping(
        ledger, manifest.get("certificate_contract"), "certificate_contract"
    )
    exact_keys(
        ledger,
        certificate_contract,
        {"expected_checks", "mutations", "scope"},
        "certificate_contract",
    )
    ledger.require(
        certificate_contract.get("expected_checks") == EXPECTED_CERTIFICATE_CHECKS,
        "manifest expected_checks is not 14",
    )
    ledger.require(
        certificate_contract.get("mutations") == list(CERTIFICATE_MUTATIONS),
        "manifest certificate mutation names changed",
    )
    ledger.require(
        certificate_contract.get("scope")
        == "finite free-word arithmetic and exact Q(sqrt(2)) witness; not Haar integration",
        "certificate scope changed",
    )

    parsed_headlines = parse_oracle(ledger, oracle_blob)
    oracle_contract = require_mapping(ledger, manifest.get("oracle_contract"), "oracle_contract")
    exact_keys(ledger, oracle_contract, {"oracle_headlines", "headlines"}, "oracle_contract")
    ledger.require(oracle_contract.get("oracle_headlines") == 16, "manifest oracle_headlines is not 16")
    ledger.require(oracle_contract.get("headlines") == list(ORACLE_HEADLINES), "manifest oracle headline sequence changed")
    ledger.require(parsed_headlines == list(ORACLE_HEADLINES), "parsed oracle headline sequence mismatch")

    verify_executions(ledger, certificate_blob, manifest.get("execution"))

    verifier_execution = require_mapping(
        ledger, manifest.get("verifier_execution"), "verifier_execution"
    )
    exact_keys(
        ledger,
        verifier_execution,
        {"check_count", "stdout_raw_sha256", "stdout_lf_sha256", "stderr_sha256"},
        "verifier_execution",
    )
    ledger.require(
        verifier_execution.get("check_count") == EXPECTED_VERIFIER_CHECKS,
        "manifest verifier check count changed",
    )
    final_output = (
        f"PR39 VERIFIER CHECKS: {EXPECTED_VERIFIER_CHECKS}/{EXPECTED_VERIFIER_CHECKS}\n"
        f"{PASS_TOKEN}\n"
    ).encode("utf-8")
    ledger.require(
        verifier_execution.get("stdout_raw_sha256") == sha256(final_output),
        "verifier stdout raw SHA-256 mismatch",
    )
    ledger.require(
        verifier_execution.get("stdout_lf_sha256") == sha256(lf_bytes(final_output)),
        "verifier stdout LF SHA-256 mismatch",
    )
    ledger.require(
        verifier_execution.get("stderr_sha256") == EMPTY_SHA256,
        "verifier success stderr SHA-256 mismatch",
    )
    ledger.close()
    return final_output


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Verify the fail-closed PR #39 checkpoint-A/evidence-B bundle."
    )
    parser.add_argument(
        "--head",
        default="HEAD",
        help="commit to treat as evidence commit B (default: HEAD)",
    )
    return parser.parse_args()


def main() -> int:
    try:
        args = parse_args()
        root = resolve_root()
        final_output = verify_bundle(root, args.head)
    except VerificationFailure as exc:
        print(f"{ERROR_PREFIX} {exc}", file=sys.stderr)
        return 1
    except Exception as exc:
        print(f"{ERROR_PREFIX} unexpected {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    sys.stdout.buffer.write(final_output)
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
