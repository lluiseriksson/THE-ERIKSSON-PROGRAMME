# codex_autocontinue.py
# Vigila Codex (izquierda) y Cowork (derecha) en paralelo.
#
# Codex (modo "ready"):
#   Captura el botón ENVIAR (círculo con flecha ↑) que aparece cuando termina.
#   Parche coincide con guardado -> LISTO -> enviar.
#
# Cowork (modo "busy"):
#   Captura el botón circular STOP (o el botón "Cola" rojo) que solo aparece
#   mientras procesa. Parche coincide -> ocupado.
#   Parche NO coincide (botón ya no está) -> LISTO -> enviar.
#
# Calibración (una vez por app):
#   python codex_autocontinue.py --calibrate-codex
#   python codex_autocontinue.py --calibrate-cowork
#
# Ejecución:
#   python codex_autocontinue.py
#   python codex_autocontinue.py --codex-only
#   python codex_autocontinue.py --cowork-sidecar-interval 300

import argparse
import json
import os
import site
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import mss
import numpy as np
import pyautogui
import pyperclip
import yaml
from PIL import Image

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

# --- Configuración ---------------------------------------------------------

REPO_ROOT = Path(r"C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME")
CANONICAL_DISPATCHER = REPO_ROOT / "scripts" / "agent_next_instruction.py"
CONTINUOUS_IMPROVEMENT = REPO_ROOT / "scripts" / "continuous_improvement.py"
STATE_FILE = REPO_ROOT / "dashboard" / "agent_state.json"
SCRIPT_DIR = Path(__file__).resolve().parent

PATCH_HALF = 22

# Umbrales por modo. Tras correr verás las distancias en consola; sube/baja
# si fuera necesario.
THRESHOLD_READY = 22.0   # Codex: d < esto = listo
THRESHOLD_BUSY  = 20.0   # Cowork: d > esto = listo

# Si d es ABSURDAMENTE alta (cambio brusco de pantalla, overlay, ventana
# perdida, etc.), no fiamos del estado y no disparamos. En modo busy la
# distancia "limpia" suele ser ~40-50; >100 es señal de que algo raro pasó.
SANITY_MAX_BUSY = 100.0

CHECK_INTERVAL = 0.7
STABLE_CHECKS = 3
POST_SEND_COOLDOWN = 6.0

# Orquestación: Codex implementa; Cowork trabaja como segundo motor continuo.
# Las auditorías polling repetidas siguen bloqueadas si no hay cambio real,
# pero Cowork cae a tareas creativas/no-polling o META para no quedar parado.
PRIMARY_AGENT = "Codex"
DEFAULT_COWORK_SIDECAR_INTERVAL = 30.0

# Sin tope de envíos. Pon un número si quieres limitarlo; None = infinito.
MAX_SENDS_PER_APP = None

# Tras enviar, esperamos hasta REARM_TIMEOUT segundos para confirmar que la
# app pasa por "ocupado". Si no la vemos ocuparse, rearmamos de todas formas.
REARM_TIMEOUT = 12.0
REARM_POLL = 0.4
SEND_METHOD_CONFIRM_SECONDS = 4.0
SEND_METHOD_CONFIRM_POLL = 0.25
DETECTOR_REACTION_DELTA = 3.0
STALE_BUSY_REACTION_DELTA = 25.0
CODEX_KEYBOARD_SUBMIT_SETTLE_SECONDS = 0.20
SUBMIT_OBSERVABILITY = True

# Codex is detected by the visible ready/send button. If the button reference is
# stale or the UI paints differently, Codex can look "busy" forever even though
# the dispatcher has concrete work. This rescue only applies to Codex startup or
# stale visual states; after a confirmed delivery it waits a long grace period so
# real long-running work is not interrupted.
CODEX_STALE_BUSY_RESCUE_SECONDS = 18.0
CODEX_CONFIRMED_BUSY_GRACE_SECONDS = 10 * 60.0

# Cuando salta el FailSafe (ratón en una esquina), pausamos en vez de morir.
FAILSAFE_RECOVERY_SECONDS = 5.0
KEYBOARD_INTERRUPT_RECOVERY_SECONDS = 15.0

# Salvaguarda contra "envío fantasma": si la app aparece como LISTO con la
# MISMA d exacta durante demasiados envíos seguidos sin pasar por ocupado,
# es que el clic no está llegando. En vez de spammear, pausamos esa app un
# rato para no hacer 1000 envíos al vacío. None = desactivado.
GHOST_SEND_LIMIT = 4          # nº de envíos seguidos sin ver "ocupado"
GHOST_PAUSE_SECONDS = 15.0    # cuánto pausar la app si se detecta

# Even when the screen detector cannot confirm that an app became busy, do not
# resend the exact same task id in a tight loop. Keep these guards short enough
# that a 24/7 run continues to make progress without needing a watcher restart.
REPEAT_TASK_PAUSE_SECONDS = 60.0
META_TASK_PAUSE_SECONDS = 180.0
FAILED_DELIVERY_RETRY_SECONDS = 15.0

# No conviertas un detector visual inestable en una manguera de prompts. Si un
# envío no queda confirmado, permitimos dos reintentos pausados; después la app
# descansa poco tiempo y vuelve a pedir una tarea fresca al dispatcher.
UNCONFIRMED_RETRY_LIMIT = 2
UNCONFIRMED_FAILURE_PAUSE_SECONDS = 15.0

# Cowork es valioso cuando audita un cambio real; es caro cuando re-audita por
# polling el mismo estado. Estas tareas solo se envían si ha cambiado una
# superficie matemática/ledger desde el último envío de Cowork.
COWORK_NO_TRIGGER_PAUSE_SECONDS = 20.0
COWORK_TRIGGER_FILES = [
    REPO_ROOT / "AXIOM_FRONTIER.md",
    REPO_ROOT / "UNCONDITIONALITY_LEDGER.md",
    REPO_ROOT / "YangMills" / "ClayCore" / "LatticeAnimalCount.lean",
    REPO_ROOT / "CLAY_HORIZON.md",
    REPO_ROOT / "F3_COUNT_DEPENDENCY_MAP.md",
]
COWORK_POLLING_TASK_PREFIXES = (
    "COWORK-LEDGER-FRESHNESS-AUDIT",
    "COWORK-DELIVERABLES-CONSISTENCY-AUDIT",
    "COWORK-DELIVERABLES-INDEX-REFRESH",
    "COWORK-AUDIT-FRESH-PERCENTAGE-MOVE",
    "COWORK-AUDIT-MATHLIB-PR-DRAFT-STATUS",
)
COWORK_POLLING_MESSAGE_MARKERS = (
    "Periodic audit",
    "periodic audit",
    "Cosmetic-only periodic check",
)

META_TASK_IDS = {
    "META-GENERATE-TASKS-001",
    "META-DISPATCHER-FAILSAFE-001",
}

# Per-process cooldown after a confirmed delivery of the same task id. This is a
# guardrail, not a manual intervention point: short values keep the loop alive
# during all-night runs while still damping accidental duplicate sends.
SESSION_TASK_COOLDOWN_SECONDS = {
    "Codex": 90.0,
    "Cowork": 60.0,
}

CODEX_CFG = SCRIPT_DIR / "codex_coords.json"
CODEX_REF = SCRIPT_DIR / "codex_send.png"
COWORK_CFG = SCRIPT_DIR / "cowork_coords.json"
COWORK_REF = SCRIPT_DIR / "cowork_busy.png"

pyautogui.FAILSAFE = True
pyautogui.PAUSE = 0.05


# --- Utilidades ------------------------------------------------------------

def grab_patch(cx, cy):
    region = {
        "left": cx - PATCH_HALF,
        "top": cy - PATCH_HALF,
        "width": PATCH_HALF * 2,
        "height": PATCH_HALF * 2,
    }
    with mss.mss() as sct:
        raw = sct.grab(region)
    return np.array(Image.frombytes("RGB", raw.size, raw.rgb))


def distance(a, b):
    return float(np.mean(np.abs(a.astype(np.int16) - b.astype(np.int16))))


def countdown(secs, msg):
    for i in range(secs, 0, -1):
        print(f"  {msg} en {i}...", end="\r")
        sys.stdout.flush()
        time.sleep(1)
    print(" " * 60, end="\r")


def safe_move_to(x, y, duration=0.1):
    """Mueve el ratón sin romper coordenadas de monitores a la izquierda.

    Windows usa coordenadas negativas para pantallas situadas a la izquierda o
    encima del monitor principal. Solo evitamos la esquina primaria (0, 0), que
    dispara el FailSafe de pyautogui; no normalizamos coordenadas negativas.
    """
    if x == 0 and y == 0:
        x, y = 1, 1
    pyautogui.moveTo(x, y, duration=duration)


# --- Calibración -----------------------------------------------------------

def calibrate_codex():
    print("=== Calibración de CODEX ===\n")
    print("Codex en estado LISTO (botón circular ↑ visible).")
    print("Pon el ratón sobre el botón ENVIAR. NO clic.\n")
    input("ENTER cuando estés sobre el botón... ")
    countdown(3, "capturando")
    x_ref, y_ref = pyautogui.position()
    Image.fromarray(grab_patch(x_ref, y_ref)).save(CODEX_REF)
    print(f"  Botón: ({x_ref}, {y_ref})\n")

    print("Ahora el RECUADRO de chat. NO clic.\n")
    input("ENTER cuando estés sobre el recuadro... ")
    countdown(3, "capturando")
    x_box, y_box = pyautogui.position()
    print(f"  Recuadro: ({x_box}, {y_box})\n")

    CODEX_CFG.write_text(json.dumps({
        "ref_x": x_ref, "ref_y": y_ref,
        "box_x": x_box, "box_y": y_box,
        "mode": "ready",
    }))
    print(f"Guardado {CODEX_CFG}.")


def calibrate_cowork():
    print("=== Calibración de COWORK ===\n")
    print("Cowork tiene que estar PROCESANDO ahora mismo.")
    print("Si no lo está, pídele algo lento antes de seguir.\n")
    print("Pon el ratón sobre el BOTÓN ROJO 'Cola' (es el más grande y")
    print("estable visualmente, mejor que el círculo stop). NO clic.\n")
    input("ENTER cuando estés sobre el botón Cola... ")
    countdown(3, "capturando")
    x_ref, y_ref = pyautogui.position()
    Image.fromarray(grab_patch(x_ref, y_ref)).save(COWORK_REF)
    print(f"  Botón: ({x_ref}, {y_ref})\n")

    print("Ahora el RECUADRO de chat de Cowork. NO clic.\n")
    input("ENTER cuando estés sobre el recuadro... ")
    countdown(3, "capturando")
    x_box, y_box = pyautogui.position()
    print(f"  Recuadro: ({x_box}, {y_box})\n")

    COWORK_CFG.write_text(json.dumps({
        "ref_x": x_ref, "ref_y": y_ref,
        "box_x": x_box, "box_y": y_box,
        "mode": "busy",
    }))
    print(f"Guardado {COWORK_CFG}.")


def diagnose_coords():
    print("=== Diagnóstico de coordenadas ===")
    for name, cfg_path in (("Codex", CODEX_CFG), ("Cowork", COWORK_CFG)):
        if not cfg_path.exists():
            print(f"{name}: sin config ({cfg_path})")
            continue
        cfg = json.loads(cfg_path.read_text())
        print(
            f"{name}: ref=({cfg.get('ref_x', cfg.get('btn_x'))}, "
            f"{cfg.get('ref_y', cfg.get('btn_y'))}), "
            f"box=({cfg.get('box_x')}, {cfg.get('box_y')}), "
            f"mode={cfg.get('mode', 'ready')}"
        )
    print("Nota: coordenadas negativas son válidas en monitores a la izquierda.")


# --- Acción ----------------------------------------------------------------

def dispatcher_python_env():
    env = os.environ.copy()
    user_home = Path.home()
    candidate_sites = [
        Path(site.getusersitepackages()),
        user_home / "AppData" / "Roaming" / "Python" / "Python312" / "site-packages",
        user_home / "AppData" / "Roaming" / "Python" / "Python311" / "site-packages",
        user_home / "AppData" / "Roaming" / "Python" / "Python310" / "site-packages",
    ]
    existing_sites = [str(p) for p in candidate_sites if p.exists()]
    env["PYTHONPATH"] = os.pathsep.join(
        existing_sites + ([env["PYTHONPATH"]] if env.get("PYTHONPATH") else [])
    )
    env["PYTHONIOENCODING"] = "utf-8"
    preferred_python = Path(r"C:\Python312\python.exe")
    python_exe = str(preferred_python if preferred_python.exists() else Path(sys.executable))
    return python_exe, env


def build_dispatch_message(agent_role, peek=False, skip_cowork_polling=False):
    if agent_role not in {"Codex", "Cowork"}:
        raise ValueError(f"Unknown agent role: {agent_role}")
    if not CANONICAL_DISPATCHER.exists():
        raise FileNotFoundError(f"Missing canonical dispatcher: {CANONICAL_DISPATCHER}")
    python_exe, env = dispatcher_python_env()
    command = [python_exe, str(CANONICAL_DISPATCHER), agent_role]
    if peek:
        command.append("--peek")
    if skip_cowork_polling:
        command.append("--skip-cowork-polling")
    result = subprocess.run(
        command,
        cwd=str(REPO_ROOT),
        env=env,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        stderr_tail = "\n".join(result.stderr.splitlines()[-30:])
        stdout_tail = "\n".join(result.stdout.splitlines()[-20:])
        return "\n".join([
            "## Structured Agent Dispatch",
            "",
            f"Agent role: {agent_role}",
            "Task id: META-DISPATCHER-FAILSAFE-001",
            "Task title: Repair canonical dispatcher failure",
            "Task priority: 0",
            "Task status at dispatch: EMERGENCY",
            "",
            "Files to read:",
            f"- {CANONICAL_DISPATCHER}",
            "- registry/agent_tasks.yaml",
            "- registry/recommendations.yaml",
            "- dashboard/agent_state.json",
            "- dashboard/last_yaml_error.json",
            "",
            "Objective:",
            "The canonical task dispatcher exited nonzero, so the watcher is sending this failsafe repair prompt instead of stopping the automation loop. Diagnose the dispatcher failure, repair the smallest broken registry or script surface, and restore structured dispatch for both agents.",
            "",
            "Validation requirements:",
            "- python scripts\\agent_next_instruction.py Codex --peek",
            "- python scripts\\agent_next_instruction.py Cowork --peek",
            "- python C:\\Users\\lluis\\Downloads\\codex_autocontinue.py --codex-only",
            "",
            "Stop conditions:",
            "- Do not delete task history or existing task records to make the dispatcher run",
            "- Do not mark mathematical work DONE while repairing dispatcher infrastructure",
            "- Stop if duplicate task ids or conflicting registry edits require human review",
            "",
            "Required updates:",
            "- AGENT_BUS.md",
            "- registry/agent_tasks.yaml",
            "- registry/agent_history.jsonl",
            "- dashboard/agent_state.json",
            "- dashboard/last_yaml_error.json if present",
            "",
            "Dispatcher stdout tail:",
            stdout_tail or "<empty>",
            "",
            "Dispatcher stderr tail:",
            stderr_tail or "<empty>",
            "",
            "Next exact instruction:",
        f"> {agent_role}, take task `META-DISPATCHER-FAILSAFE-001`. Read the files above, repair the dispatcher or malformed registry without deleting existing tasks, run the validation commands, update the bus/history/dashboard, and stop if conflicting registry edits require human review.",
        ])
    return result.stdout


def load_agent_state():
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8-sig"))
    except Exception:
        return {}


def cowork_dispatch_suspended():
    return bool(load_agent_state().get("cowork_dispatch_suspended"))


def cowork_dispatch_blocker():
    return load_agent_state().get(
        "cowork_dispatch_blocker",
        "Cowork workspace dispatch is suspended.",
    )


def record_delivery_state(agent_role, task_id, state_name, method="", distance=None):
    """Tell the canonical dispatcher whether the visual send was confirmed."""
    if not task_id or task_id == "<unknown>":
        return
    python_exe, env = dispatcher_python_env()
    command = [
        python_exe,
        str(CANONICAL_DISPATCHER),
        "--record-delivery",
        "--agent",
        agent_role,
        "--task-id",
        task_id,
        "--state",
        state_name,
    ]
    if method:
        command.extend(["--method", str(method)])
    if distance is not None:
        command.extend(["--distance", f"{float(distance):.1f}"])
    result = subprocess.run(
        command,
        cwd=str(REPO_ROOT),
        env=env,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        tail = "\n".join((result.stderr or result.stdout).splitlines()[-5:])
        print(f"[!] No pude registrar entrega {state_name} para {task_id}: {tail}")


def parse_registry_time(value):
    if not isinstance(value, str):
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


def print_inprogress_delivery_diagnostics(tasks_doc):
    tasks = (tasks_doc or {}).get("tasks", [])
    now = datetime.now(timezone.utc)
    states = {
        "DISPATCH_MUTATED_PENDING_CONFIRMATION",
        "UNCONFIRMED_SEND_RETRY_PENDING",
        "ABANDONED_UNCONFIRMED",
    }
    candidates = []
    for task in tasks:
        if task.get("status") != "IN_PROGRESS":
            continue
        state = str(task.get("delivery_state", "")).upper()
        dispatched_at = parse_registry_time(task.get("dispatched_at") or task.get("updated_at"))
        if state not in states or dispatched_at is None:
            continue
        age = (now - dispatched_at).total_seconds()
        if age >= 15 * 60:
            candidates.append((task.get("id"), state, int(age // 60)))
    if candidates:
        print("[!] IN_PROGRESS con entrega no confirmada detectados:")
        for task_id, state, age_min in candidates[:5]:
            print(f"    - {task_id}: {state}, edad ~{age_min} min")
        print("    No se resetean automáticamente; quedan como diagnóstico conservador.")


def preflight_dispatcher():
    """Comprueba registros y peeks sin mutar la cola.

    Esto no sustituye al failsafe del dispatcher: solo imprime una lectura
    temprana para runs largos, de modo que un YAML roto o un task duplicado
    sea visible antes de dejar la automatización sola durante horas.
    """
    print("=== Preflight dispatcher ===")
    try:
        tasks_doc = yaml.safe_load((REPO_ROOT / "registry" / "agent_tasks.yaml").read_text(
            encoding="utf-8"
        ))
        yaml.safe_load((REPO_ROOT / "registry" / "recommendations.yaml").read_text(
            encoding="utf-8"
        ))
        json.loads((REPO_ROOT / "dashboard" / "agent_state.json").read_text(
            encoding="utf-8"
        ))
        history_path = REPO_ROOT / "registry" / "agent_history.jsonl"
        for line_no, line in enumerate(history_path.read_text(encoding="utf-8").splitlines(), 1):
            if line.strip():
                json.loads(line)
        ids = [t.get("id") for t in (tasks_doc or {}).get("tasks", []) if t.get("id")]
        duplicates = sorted({task_id for task_id in ids if ids.count(task_id) > 1})
        if duplicates:
            print(f"[!] Task ids duplicados: {', '.join(duplicates[:10])}")
        else:
            print("[OK] YAML/JSON/JSONL parsean y no hay task ids duplicados.")
        print_inprogress_delivery_diagnostics(tasks_doc)
        print_guardrail_diagnostics()
    except Exception as exc:
        print(f"[!] Preflight registry falló: {type(exc).__name__}: {exc}")
        print("    El watcher seguirá; si el dispatcher falla, enviará META-DISPATCHER-FAILSAFE.")

    for agent in ("Codex", "Cowork"):
        try:
            msg = build_dispatch_message(agent, peek=True)
            print(f"[OK] Peek {agent}: Task id: {extract_task_id(msg)}")
        except Exception as exc:
            print(f"[!] Peek {agent} falló: {type(exc).__name__}: {exc}")
    try:
        if CONTINUOUS_IMPROVEMENT.exists():
            print(f"[OK] Continuous improvement script: {CONTINUOUS_IMPROVEMENT}")
            python_exe, env = dispatcher_python_env()
            result = subprocess.run(
                [python_exe, str(CONTINUOUS_IMPROVEMENT)],
                cwd=str(REPO_ROOT),
                env=env,
                text=True,
                encoding="utf-8",
                errors="replace",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
            )
            output = (result.stdout or result.stderr).strip()
            if result.returncode == 0:
                print(output)
            else:
                print(f"[!] Continuous improvement falló: {output}")
    except Exception as exc:
        print(f"[!] Continuous improvement no pudo ejecutarse: {type(exc).__name__}: {exc}")
    print()


def extract_task_id(message):
    for line in message.splitlines():
        if line.startswith("Task id:"):
            return line.split(":", 1)[1].strip()
    return "<unknown>"


def repeat_pause_seconds(task_id):
    if task_id == "META-GENERATE-TASKS-001":
        return META_TASK_PAUSE_SECONDS
    return REPEAT_TASK_PAUSE_SECONDS


def is_meta_task_id(task_id):
    return task_id in META_TASK_IDS or str(task_id or "").startswith("META-")


def codex_stale_busy_rescue_allowed(app, args):
    if app.name != "Codex" or app.mode != "ready":
        return False, None
    if args.codex_stale_busy_rescue <= 0:
        return False, None
    if app.pending_message is not None:
        return True, app.pending_task_id
    if app.busy_since <= 0:
        return False, None
    now = time.time()
    if now - app.busy_since < args.codex_stale_busy_rescue:
        return False, None
    if (
        app.last_confirmed_busy_at
        and now - app.last_confirmed_busy_at < args.codex_confirmed_busy_grace
    ):
        return False, None
    preview = build_dispatch_message("Codex", peek=True)
    task_id = extract_task_id(preview)
    if not task_id or is_meta_task_id(task_id):
        return False, task_id
    return True, task_id


def repo_trigger_signature():
    """Compact signature for surfaces that should wake Cowork audits."""
    signature = []
    for path in COWORK_TRIGGER_FILES:
        try:
            stat = path.stat()
        except OSError:
            signature.append((str(path), None, None))
            continue
        signature.append((str(path), stat.st_mtime_ns, stat.st_size))
    return tuple(signature)


def is_cowork_polling_task(task_id, message=""):
    # META tasks generate fresh queue work; gating them as Cowork polling can
    # starve both agents during 24/7 runs.
    if is_meta_task_id(task_id):
        return False
    return (
        any(task_id.startswith(prefix) for prefix in COWORK_POLLING_TASK_PREFIXES)
        or any(marker in message for marker in COWORK_POLLING_MESSAGE_MARKERS)
    )


def cowork_non_polling_fallback(peek=True):
    return build_dispatch_message(
        "Cowork",
        peek=peek,
        skip_cowork_polling=True,
    )


def stale_busy_reaction_confirmed(ready, baseline_d, current_d):
    """Return whether a stale-busy send attempt really changed app state.

    Small detector-distance oscillations are common while the app still looks
    busy. They must not confirm delivery. Confirmation requires either an
    actual ready-state transition or a large visual jump.
    """
    if ready:
        return True
    return (
        baseline_d is not None
        and current_d is not None
        and abs(current_d - baseline_d) >= STALE_BUSY_REACTION_DELTA
    )


def print_guardrail_diagnostics():
    meta_polling = is_cowork_polling_task("META-GENERATE-TASKS-001", "")
    small_oscillation_confirms = stale_busy_reaction_confirmed(
        ready=False,
        baseline_d=45.6,
        current_d=45.6 + max(1.0, STALE_BUSY_REACTION_DELTA / 4.0),
    )
    large_jump_confirms = stale_busy_reaction_confirmed(
        ready=False,
        baseline_d=45.6,
        current_d=45.6 + STALE_BUSY_REACTION_DELTA + 1.0,
    )
    status = "OK" if (
        not meta_polling and not small_oscillation_confirms and large_jump_confirms
    ) else "!"
    try:
        cowork_fallback = cowork_non_polling_fallback(peek=True)
        cowork_fallback_task = extract_task_id(cowork_fallback)
    except Exception:
        cowork_fallback_task = "<unavailable>"
    print(
        f"[{status}] Guardrails 24/7: META no es Cowork polling="
        f"{not meta_polling}; stale-busy small-oscillation blocks="
        f"{not small_oscillation_confirms}; large-jump confirms={large_jump_confirms}; "
        f"Cowork fallback no-polling={cowork_fallback_task}."
    )


def confirm_app_reacted(
        app,
        timeout=SEND_METHOD_CONFIRM_SECONDS,
        baseline_ready=None,
        baseline_d=None):
    deadline = time.time() + timeout
    last_d = None
    while time.time() < deadline:
        ready, d = app.is_ready()
        last_d = d
        if baseline_ready is False:
            # A stale-busy rescue starts from a detector that already says
            # "busy"; small animation/overlay changes must not be treated as a
            # confirmed delivery. Require either a real ready-state transition
            # or a large visual jump.
            if stale_busy_reaction_confirmed(ready, baseline_d, d):
                return True, d
        elif not ready:
            return True, d
        time.sleep(SEND_METHOD_CONFIRM_POLL)
    return False, last_d


def submit_obs(app, method, phase, **fields):
    """Small send-path breadcrumb for post-mortem watcher logs.

    Observability only: this must not participate in delivery confirmation.
    Stale-busy confirmation still lives exclusively in
    stale_busy_reaction_confirmed/confirm_app_reacted.
    """
    if not SUBMIT_OBSERVABILITY:
        return
    details = " ".join(f"{key}={value}" for key, value in fields.items())
    suffix = f" {details}" if details else ""
    print(f"  [{app.name}] OBS submit method={method} phase={phase}{suffix}")


def submit_current_prompt(app, baseline_ready=None, baseline_d=None):
    if app.mode == "ready":
        def codex_keyboard_enter(method_name):
            # Codex has had false visual confirmations from the calibrated
            # button/hover path. Keep the prompt box focused and submit by
            # keyboard first; the calibrated button is only a fallback.
            submit_obs(app, method_name, "prompt-box-focus",
                       box=f"({app.box_x},{app.box_y})")
            safe_move_to(app.box_x, app.box_y, duration=0.05)
            time.sleep(0.05)
            pyautogui.click()
            time.sleep(0.08)
            submit_obs(app, method_name, "keyboard-submit", key="enter")
            pyautogui.press("enter")
            time.sleep(CODEX_KEYBOARD_SUBMIT_SETTLE_SECONDS)

        def codex_keyboard_ctrl_enter(method_name):
            submit_obs(app, method_name, "prompt-box-focus",
                       box=f"({app.box_x},{app.box_y})")
            safe_move_to(app.box_x, app.box_y, duration=0.05)
            time.sleep(0.05)
            pyautogui.click()
            time.sleep(0.08)
            submit_obs(app, method_name, "keyboard-submit", key="ctrl-enter")
            pyautogui.hotkey("ctrl", "enter")
            time.sleep(CODEX_KEYBOARD_SUBMIT_SETTLE_SECONDS)

        def codex_button_click(method_name):
            submit_obs(app, method_name, "fallback-button-submit",
                       button=f"({app.ref_x},{app.ref_y})", clicks=1)
            safe_move_to(app.ref_x, app.ref_y, duration=0.08)
            time.sleep(0.05)
            pyautogui.click()

        def codex_button_double_click(method_name):
            submit_obs(app, method_name, "fallback-button-submit",
                       button=f"({app.ref_x},{app.ref_y})", clicks=2)
            safe_move_to(app.ref_x, app.ref_y, duration=0.08)
            time.sleep(0.05)
            pyautogui.doubleClick(interval=0.12)

        if baseline_ready is False:
            # In stale-busy rescue the ready-button coordinate is not trustworthy.
            # Keep the prompt box focused and use keyboard submits only.
            strategies = (
                ("codex-enter", codex_keyboard_enter),
                ("codex-ctrl-enter", codex_keyboard_ctrl_enter),
            )
        else:
            strategies = (
                ("codex-enter", codex_keyboard_enter),
                ("codex-ctrl-enter", codex_keyboard_ctrl_enter),
                ("calibrated-button", codex_button_click),
                ("double-calibrated-button", codex_button_double_click),
            )
    else:
        strategies = (
            ("enter", lambda method_name: (
                submit_obs(app, method_name, "keyboard-submit", key="enter"),
                pyautogui.press("enter"),
            )),
            ("ctrl-enter", lambda method_name: (
                submit_obs(app, method_name, "keyboard-submit", key="ctrl-enter"),
                pyautogui.hotkey("ctrl", "enter"),
            )),
        )
    submit_obs(app, "dispatch", "baseline",
               ready=baseline_ready,
               d=f"{baseline_d:.1f}" if baseline_d is not None else "None",
               stale_busy_rescue=(baseline_ready is False))
    for name, action in strategies:
        action(name)
        ok, d = confirm_app_reacted(
            app,
            baseline_ready=baseline_ready,
            baseline_d=baseline_d,
        )
        delta = abs(d - baseline_d) if d is not None and baseline_d is not None else None
        submit_obs(app, name, "visual-reaction",
                   ok=ok,
                   d=f"{d:.1f}" if d is not None else "None",
                   delta=f"{delta:.1f}" if delta is not None else "None",
                   stale_busy_requires_large_jump=(baseline_ready is False))
        if ok:
            return True, name, d
        if d is None:
            print(f"  [{app.name}] método {name} sin lectura de detector.")
        elif baseline_ready is False:
            delta = abs(d - baseline_d) if baseline_d is not None else 0.0
            print(f"  [{app.name}] método {name} no mostró cambio visual "
                  f"suficiente (d={d:.1f}, Δ={delta:.1f}); probando fallback.")
        else:
            print(f"  [{app.name}] método {name} no activó ocupado "
                  f"(d={d:.1f}); probando fallback.")
        # Refocus the input before the next fallback. This also keeps the prompt
        # text in the box if the first method only inserted a newline.
        safe_move_to(app.box_x, app.box_y, duration=0.05)
        time.sleep(0.05)
        pyautogui.click()
        time.sleep(0.1)
    return False, "all-methods-failed", d


def send_reply(app, message):
    prev = pyautogui.position()
    baseline_ready, baseline_d = app.is_ready()
    safe_move_to(app.box_x, app.box_y, duration=0.15)
    time.sleep(0.1)
    pyautogui.click()
    time.sleep(0.25)
    pyperclip.copy(message)
    if pyperclip.paste() != message:
        raise RuntimeError("Clipboard verification failed before paste")
    pyautogui.hotkey("ctrl", "a")
    time.sleep(0.05)
    pyautogui.hotkey("ctrl", "v")
    time.sleep(0.2)
    ok, method, d = submit_current_prompt(
        app,
        baseline_ready=baseline_ready,
        baseline_d=baseline_d,
    )
    time.sleep(0.1)
    safe_move_to(prev.x, prev.y, duration=0.05)
    return ok, method, d


# --- Modelo ----------------------------------------------------------------

class WatchedApp:
    def __init__(self, name, cfg_path, ref_path):
        self.name = name
        self.cfg_path = cfg_path
        self.ref_path = ref_path
        self.ref_x = 0
        self.ref_y = 0
        self.box_x = 0
        self.box_y = 0
        self.mode = "ready"
        self.threshold = THRESHOLD_READY
        self.ref_img = None
        self.stable_ready = 0
        self.sends = 0
        self.enabled = False
        self.armed = True
        # Detección de envío fantasma
        self.ghost_streak = 0
        self.paused_until = 0.0
        self.last_sent_task_id = None
        self.last_sent_at = 0.0
        self.last_confirmed_busy_at = 0.0
        self.busy_since = 0.0
        self.pending_message = None
        self.pending_task_id = None
        self.pending_attempts = 0
        self.session_sent_tasks = {}

    def load(self):
        if not (self.cfg_path.exists() and self.ref_path.exists()):
            return False
        cfg = json.loads(self.cfg_path.read_text())
        self.ref_x = cfg.get("ref_x", cfg.get("btn_x"))
        self.ref_y = cfg.get("ref_y", cfg.get("btn_y"))
        self.box_x = cfg["box_x"]
        self.box_y = cfg["box_y"]
        self.mode = cfg.get("mode", "ready")
        self.threshold = THRESHOLD_BUSY if self.mode == "busy" else THRESHOLD_READY
        self.ref_img = np.array(Image.open(self.ref_path).convert("RGB"))
        self.enabled = True
        return True

    def is_ready(self):
        cur = grab_patch(self.ref_x, self.ref_y)
        d = distance(cur, self.ref_img)
        if self.mode == "ready":
            ready = d < self.threshold
        else:
            ready = d > self.threshold
        return ready, d

    def is_sane_ready(self, d):
        if self.mode == "busy" and d > SANITY_MAX_BUSY:
            return False
        return True

    def is_paused(self):
        return time.time() < self.paused_until


# --- Bucle -----------------------------------------------------------------

def run(args):
    apps = []
    codex = WatchedApp("Codex", CODEX_CFG, CODEX_REF)
    cowork = WatchedApp("Cowork", COWORK_CFG, COWORK_REF)
    last_cowork_dispatch_at = 0.0
    # Allow one Cowork sidecar after startup.  After that, polling-style Cowork
    # tasks are gated on real frontier/ledger/Lean changes.
    last_cowork_trigger_signature = None

    if codex.load():
        codex.threshold = args.codex_ready_threshold
        apps.append(codex)
        print(f"[+] {codex.name} (modo={codex.mode}, umbral={codex.threshold}) "
              f"en ({codex.ref_x}, {codex.ref_y})")
    else:
        print(f"[-] {codex.name}: sin calibrar (--calibrate-codex)")

    if cowork_dispatch_suspended():
        print(f"[-] Cowork: suspendido por estado del agente: {cowork_dispatch_blocker()}")
    elif not args.codex_only and cowork.load():
        cowork.threshold = args.cowork_busy_threshold
        apps.append(cowork)
        print(f"[+] {cowork.name} (modo={cowork.mode}, umbral={cowork.threshold}) "
              f"en ({cowork.ref_x}, {cowork.ref_y})")
    elif args.codex_only:
        print("[-] Cowork: desactivado por --codex-only")
    else:
        print(f"[-] {cowork.name}: sin calibrar (--calibrate-cowork)")

    if not apps:
        print("\nNada que vigilar.")
        return

    cap_msg = "sin tope" if MAX_SENDS_PER_APP is None else f"tope {MAX_SENDS_PER_APP}"
    print(f"\nMODO AUTOMÁTICO ({cap_msg}). Ctrl+C pausa y reanuda; "
          "usa --stop-on-ctrl-c si quieres parar con Ctrl+C.")
    print("Política: Codex implementa; Cowork trabaja continuo como auditor/sidecar creativo.")
    print(f"Cowork triggered-sidecar: pausa mínima {args.cowork_sidecar_interval:.0f}s "
          "entre tareas confirmadas; auditorías polling sin trigger caen a tareas "
          "no-polling/META para mantener Cowork ocupado.")
    print("Si el ratón toca (0,0) el script PAUSA 5s y reanuda solo.\n")

    last_state = {}

    while True:
        try:
            ready_apps = []
            for app in apps:
                if not app.enabled:
                    continue
                if app.name == "Cowork" and cowork_dispatch_suspended():
                    app.enabled = False
                    print(f"[-] Cowork: suspendido durante ejecución: {cowork_dispatch_blocker()}")
                    continue
                if app.is_paused():
                    continue

                ready, d = app.is_ready()
                if ready:
                    app.busy_since = 0.0
                elif app.busy_since <= 0:
                    app.busy_since = time.time()
                if not ready:
                    rescue, rescued_task_id = codex_stale_busy_rescue_allowed(app, args)
                    if rescue:
                        ready = True
                        if last_state.get(("rescue", app.name)) != rescued_task_id:
                            print(
                                f"  [{app.name}] rescate stale-busy: d={d:.1f} "
                                f"durante {time.time() - app.busy_since:.0f}s; "
                                f"dispatcher tiene {rescued_task_id}. Intento enviar."
                            )
                            last_state[("rescue", app.name)] = rescued_task_id
                tag = "LISTO " if ready else "ocupado"

                state_key = (tag, app.armed, round(d))
                if last_state.get(app.name) != state_key:
                    armed_tag = "" if app.armed else " [desarmado]"
                    print(f"  [{app.name:6s}] {tag} | d={d:5.1f} "
                          f"(umbral {app.threshold:.0f}){armed_tag}")
                    last_state[app.name] = state_key

                if ready:
                    if not app.is_sane_ready(d):
                        if last_state.get(("warn", app.name)) != round(d):
                            print(f"  [{app.name}] LISTO ignorado: d={d:.1f} "
                                  f"sospechosa (>{SANITY_MAX_BUSY:.0f}). "
                                  f"¿Pantalla movida o overlay?")
                            last_state[("warn", app.name)] = round(d)
                        app.stable_ready = 0
                        continue

                    if app.armed:
                        app.stable_ready += 1
                        if app.stable_ready >= STABLE_CHECKS:
                            ready_apps.append(app)
                else:
                    app.stable_ready = 0
                    app.armed = True
                    # Vimos ocupado de verdad: la racha fantasma se rompe. Do not
                    # clear a Codex retry just because the stale ready-button
                    # detector still reads busy.
                    if not (
                        app.name == "Codex"
                        and app.mode == "ready"
                        and app.pending_message is not None
                    ):
                        app.ghost_streak = 0
                        app.pending_message = None
                        app.pending_task_id = None
                        app.pending_attempts = 0

            ready_apps.sort(key=lambda a: 0 if a.name == PRIMARY_AGENT else 1)
            codex_pending = any(
                a.name == PRIMARY_AGENT and a.pending_message for a in apps
            )
            for app in ready_apps:
                if app.name == "Cowork":
                    now = time.time()
                    if codex_pending:
                        app.stable_ready = 0
                        app.armed = True
                        print("[SKIP] Cowork: Codex tiene un envío pendiente no "
                              "confirmado; evito interferir hasta reintento.")
                        continue
                    if (last_cowork_dispatch_at
                            and now - last_cowork_dispatch_at
                            < args.cowork_sidecar_interval):
                        remaining = int(round(
                            args.cowork_sidecar_interval
                            - (now - last_cowork_dispatch_at)
                        ))
                        app.paused_until = max(
                            app.paused_until,
                            last_cowork_dispatch_at
                            + args.cowork_sidecar_interval,
                        )
                        app.stable_ready = 0
                        app.armed = True
                        print(f"[SKIP] Cowork: sidecar interval active for "
                              f"{remaining}s; reintento en cuanto venza.")
                        continue
                is_retry = app.pending_message is not None
                if is_retry:
                    message = app.pending_message
                    task_id = app.pending_task_id or extract_task_id(message)
                else:
                    preview = build_dispatch_message(app.name, peek=True)
                    task_id = extract_task_id(preview)
                    if app.name == "Cowork" and is_cowork_polling_task(task_id, preview):
                        current_signature = repo_trigger_signature()
                        if last_cowork_trigger_signature == current_signature:
                            fallback_preview = cowork_non_polling_fallback(peek=True)
                            fallback_task_id = extract_task_id(fallback_preview)
                            if fallback_task_id and fallback_task_id != task_id:
                                print(
                                    "[INFO] Cowork: "
                                    f"{task_id} es polling sin trigger; cambio a "
                                    f"{fallback_task_id} para mantener sidecar activo."
                                )
                                preview = fallback_preview
                                task_id = fallback_task_id
                            else:
                                app.paused_until = max(
                                    app.paused_until,
                                    time.time() + COWORK_NO_TRIGGER_PAUSE_SECONDS,
                                )
                                app.stable_ready = 0
                                app.armed = True
                                print(
                                    "[SKIP] Cowork: "
                                    f"{task_id} no tiene cambio matemático/ledger "
                                    "y no hay fallback no-polling; pauso Cowork "
                                    f"{COWORK_NO_TRIGGER_PAUSE_SECONDS:.0f}s."
                                )
                                continue
                task_line = f"Task id: {task_id}"
                now = time.time()
                pause_seconds = repeat_pause_seconds(task_id)
                if is_retry:
                    pause_seconds = min(pause_seconds, FAILED_DELIVERY_RETRY_SECONDS)
                if (app.last_sent_task_id == task_id
                        and now - app.last_sent_at < pause_seconds):
                    remaining = int(round(pause_seconds - (now - app.last_sent_at)))
                    app.paused_until = max(app.paused_until,
                                           app.last_sent_at + pause_seconds)
                    app.stable_ready = 0
                    app.armed = True
                    print(f"[SKIP] {app.name}: {task_line} already sent; "
                          f"repeat guard active for {remaining}s.")
                    continue
                session_last = app.session_sent_tasks.get(task_id)
                session_pause = SESSION_TASK_COOLDOWN_SECONDS.get(app.name, 0.0)
                if (not is_retry and session_last is not None
                        and now - session_last < session_pause):
                    remaining = int(round(session_pause - (now - session_last)))
                    app.paused_until = max(app.paused_until,
                                           now + min(remaining, 60))
                    app.stable_ready = 0
                    app.armed = True
                    print(f"[SKIP] {app.name}: {task_line} ya fue entregado "
                          f"en esta sesión; cooldown {remaining}s. Reinicia "
                          "el watcher para forzar reenvío manual.")
                    continue
                if not is_retry:
                    skip_polling = app.name == "Cowork" and preview is not None and task_id == extract_task_id(
                        cowork_non_polling_fallback(peek=True)
                    )
                    message = build_dispatch_message(
                        app.name,
                        peek=False,
                        skip_cowork_polling=skip_polling,
                    )
                    task_id = extract_task_id(message)
                    task_line = f"Task id: {task_id}"
                    app.pending_message = message
                    app.pending_task_id = task_id
                    app.pending_attempts = 0
                else:
                    app.pending_attempts += 1

                print(f"[OK] {app.name} listo. Enviando #{app.sends+1}: {task_line}")
                delivered, method, d_after_send = send_reply(app, message)
                app.sends += 1
                app.last_sent_task_id = task_id
                app.last_sent_at = time.time()
                if delivered:
                    record_delivery_state(
                        app.name,
                        task_id,
                        "CONFIRMED_BUSY",
                        method=method,
                        distance=d_after_send,
                    )
                    app.session_sent_tasks[task_id] = app.last_sent_at
                if app.name == "Cowork":
                    last_cowork_dispatch_at = app.last_sent_at
                    last_cowork_trigger_signature = repo_trigger_signature()
                app.stable_ready = 0
                app.armed = False

                if MAX_SENDS_PER_APP is not None and app.sends >= MAX_SENDS_PER_APP:
                    print(f"[!] {app.name}: tope de {MAX_SENDS_PER_APP}.")
                    app.enabled = False
                    continue

                deadline = time.time() + REARM_TIMEOUT
                rearmed_with_busy = delivered
                if delivered:
                    app.armed = True
                    app.last_confirmed_busy_at = time.time()
                    app.pending_message = None
                    app.pending_task_id = None
                    app.pending_attempts = 0
                    print(f"  [{app.name}] ocupado confirmado vía {method} "
                          f"(d={d_after_send:.1f}), rearmado.")
                while not rearmed_with_busy and time.time() < deadline:
                    r, d = app.is_ready()
                    if not r:
                        app.armed = True
                        rearmed_with_busy = True
                        app.last_confirmed_busy_at = time.time()
                        record_delivery_state(
                            app.name,
                            task_id,
                            "CONFIRMED_BUSY",
                            method="detector",
                            distance=d,
                        )
                        app.pending_message = None
                        app.pending_task_id = None
                        app.pending_attempts = 0
                        print(f"  [{app.name}] ocupado confirmado "
                              f"(d={d:.1f}), rearmado.")
                        break
                    time.sleep(REARM_POLL)
                if not rearmed_with_busy:
                    app.armed = True
                    app.ghost_streak += 1
                    print(f"  [{app.name}] timeout sin ver ocupado, "
                          f"rearmado por seguridad. "
                          f"(racha fantasma {app.ghost_streak}/{GHOST_SEND_LIMIT})")
                    if app.pending_attempts >= UNCONFIRMED_RETRY_LIMIT:
                        record_delivery_state(
                            app.name,
                            task_id,
                            "ABANDONED_UNCONFIRMED",
                            method=method,
                            distance=d_after_send,
                        )
                        app.pending_message = None
                        app.pending_task_id = None
                        app.pending_attempts = 0
                        app.paused_until = max(
                            app.paused_until,
                            time.time() + UNCONFIRMED_FAILURE_PAUSE_SECONDS,
                        )
                        print(
                            f"[!] {app.name}: envío no confirmado tras "
                            f"{UNCONFIRMED_RETRY_LIMIT + 1} intento(s). "
                            "No reenvío la misma tarea en bucle; pauso "
                            f"{UNCONFIRMED_FAILURE_PAUSE_SECONDS:.0f}s."
                        )
                    else:
                        record_delivery_state(
                            app.name,
                            task_id,
                            "UNCONFIRMED_SEND_RETRY_PENDING",
                            method=method,
                            distance=d_after_send,
                        )
                else:
                    app.ghost_streak = 0

                # Salvaguarda anti-spam: si llevamos N envíos seguidos sin
                # que la app reaccione, casi seguro los clics no llegan.
                if (GHOST_SEND_LIMIT
                        and app.ghost_streak >= GHOST_SEND_LIMIT):
                    app.paused_until = time.time() + GHOST_PAUSE_SECONDS
                    app.ghost_streak = 0
                    print(f"[!] {app.name}: posibles envíos fantasma "
                          f"({GHOST_SEND_LIMIT} seguidos sin reacción). "
                          f"Pausando esta app {GHOST_PAUSE_SECONDS:.0f}s. "
                          f"Comprueba que la ventana tiene foco y los "
                          f"mensajes están llegando.")

                last_state.pop(app.name, None)

            if ready_apps:
                time.sleep(POST_SEND_COOLDOWN)
                continue

            if not any(a.enabled for a in apps):
                print("Todas las apps deshabilitadas. Fin.")
                return

            time.sleep(CHECK_INTERVAL)

        except pyautogui.FailSafeException:
            print(f"\n[!] FailSafe disparado (ratón en esquina). "
                  f"Pausa de {FAILSAFE_RECOVERY_SECONDS:.0f}s y sigo...")
            try:
                time.sleep(FAILSAFE_RECOVERY_SECONDS)
            except KeyboardInterrupt:
                if args.stop_on_ctrl_c:
                    print("\nInterrumpido durante pausa.")
                    return
                print("\n[!] KeyboardInterrupt durante pausa FailSafe; "
                      "ignorado en modo 24/7, reanudo.")
            last_state.clear()
            continue

        except KeyboardInterrupt:
            if args.stop_on_ctrl_c:
                print("\nInterrumpido.")
                return
            print(f"\n[!] KeyboardInterrupt recibido; NO detengo el watcher 24/7. "
                  f"Pausa {KEYBOARD_INTERRUPT_RECOVERY_SECONDS:.0f}s y reanudo. "
                  "Para detenerlo, cierra la terminal o usa --stop-on-ctrl-c.")
            try:
                time.sleep(KEYBOARD_INTERRUPT_RECOVERY_SECONDS)
            except KeyboardInterrupt:
                print("\n[!] Segundo KeyboardInterrupt ignorado también en modo 24/7; reanudo.")
            last_state.clear()
            continue

        except Exception as e:
            print(f"\n[!] Error inesperado: {type(e).__name__}: {e}")
            print("    Pausa de 3s y sigo...")
            try:
                time.sleep(3.0)
            except KeyboardInterrupt:
                if args.stop_on_ctrl_c:
                    print("\nInterrumpido durante pausa.")
                    return
                print("\n[!] KeyboardInterrupt durante recuperación de error; "
                      "ignorado en modo 24/7, reanudo.")
            last_state.clear()
            continue


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("agent", nargs="?", choices=["Codex", "Cowork"],
                   help="Print one structured task dispatch for this agent and exit.")
    p.add_argument("--calibrate-codex", action="store_true")
    p.add_argument("--calibrate-cowork", action="store_true")
    p.add_argument("--diagnose-coords", action="store_true")
    p.add_argument("--preflight-only", action="store_true",
                   help="Validate registries and dispatcher peeks, then exit.")
    p.add_argument("--stop-on-ctrl-c", action="store_true",
                   help="Restore old behavior: exit immediately on Ctrl+C.")
    p.add_argument("--codex-only", action="store_true",
                   help="Watch only Codex; useful while debugging left-screen delivery.")
    p.add_argument("--cowork-sidecar-interval", type=float,
                   default=DEFAULT_COWORK_SIDECAR_INTERVAL,
                   help="Minimum seconds between Cowork sidecar dispatches.")
    p.add_argument("--codex-stale-busy-rescue", type=float,
                   default=CODEX_STALE_BUSY_RESCUE_SECONDS,
                   help="Seconds Codex may look busy before trying a concrete non-META task anyway; 0 disables.")
    p.add_argument("--codex-confirmed-busy-grace", type=float,
                   default=CODEX_CONFIRMED_BUSY_GRACE_SECONDS,
                   help="Seconds after confirmed Codex delivery during which stale-busy rescue is disabled.")
    p.add_argument("--codex-ready-threshold", type=float,
                   default=THRESHOLD_READY,
                   help="Codex ready detector threshold; raise if ready button reads just above threshold.")
    p.add_argument("--cowork-busy-threshold", type=float,
                   default=THRESHOLD_BUSY,
                   help="Cowork busy-mode threshold; lower/raise only after calibration diagnostics.")
    args = p.parse_args()
    if args.agent:
        print(build_dispatch_message(args.agent))
    elif args.calibrate_codex:
        calibrate_codex()
    elif args.calibrate_cowork:
        calibrate_cowork()
    elif args.diagnose_coords:
        diagnose_coords()
    elif args.preflight_only:
        preflight_dispatcher()
    else:
        preflight_dispatcher()
        run(args)
