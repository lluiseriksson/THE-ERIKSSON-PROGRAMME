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
#   python codex_autocontinue.py --cowork-sidecar-interval 900

import argparse
import json
import os
import site
import subprocess
import sys
import time
from pathlib import Path

import mss
import numpy as np
import pyautogui
import pyperclip
from PIL import Image

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

# --- Configuración ---------------------------------------------------------

REPO_ROOT = Path(r"C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME")
CANONICAL_DISPATCHER = REPO_ROOT / "scripts" / "agent_next_instruction.py"
SCRIPT_DIR = Path(__file__).resolve().parent

PATCH_HALF = 22

# Umbrales por modo. Tras correr verás las distancias en consola; sube/baja
# si fuera necesario.
THRESHOLD_READY = 15.0   # Codex: d < esto = listo
THRESHOLD_BUSY  = 20.0   # Cowork: d > esto = listo

# Si d es ABSURDAMENTE alta (cambio brusco de pantalla, overlay, ventana
# perdida, etc.), no fiamos del estado y no disparamos. En modo busy la
# distancia "limpia" suele ser ~40-50; >100 es señal de que algo raro pasó.
SANITY_MAX_BUSY = 100.0

CHECK_INTERVAL = 0.7
STABLE_CHECKS = 3
POST_SEND_COOLDOWN = 6.0

# Orquestación: Codex es el agente primario; Cowork es sidecar de auditoría.
# En modo normal se atiende primero a Codex y se limita la frecuencia de Cowork
# para que no capture el baton mientras Codex todavía necesita trabajo.
PRIMARY_AGENT = "Codex"
DEFAULT_COWORK_SIDECAR_INTERVAL = 900.0

# Sin tope de envíos. Pon un número si quieres limitarlo; None = infinito.
MAX_SENDS_PER_APP = None

# Tras enviar, esperamos hasta REARM_TIMEOUT segundos para confirmar que la
# app pasa por "ocupado". Si no la vemos ocuparse, rearmamos de todas formas.
REARM_TIMEOUT = 8.0
REARM_POLL = 0.4
SEND_METHOD_CONFIRM_SECONDS = 2.0
SEND_METHOD_CONFIRM_POLL = 0.25

# Cuando salta el FailSafe (ratón en una esquina), pausamos en vez de morir.
FAILSAFE_RECOVERY_SECONDS = 5.0

# Salvaguarda contra "envío fantasma": si la app aparece como LISTO con la
# MISMA d exacta durante demasiados envíos seguidos sin pasar por ocupado,
# es que el clic no está llegando. En vez de spammear, pausamos esa app un
# rato para no hacer 1000 envíos al vacío. None = desactivado.
GHOST_SEND_LIMIT = 5          # nº de envíos seguidos sin ver "ocupado"
GHOST_PAUSE_SECONDS = 30.0    # cuánto pausar la app si se detecta

# Even when the screen detector cannot confirm that an app became busy, do not
# resend the exact same task id in a tight loop. META tasks get a longer pause
# because they are queue-repair tasks, not normal work assignments.
REPEAT_TASK_PAUSE_SECONDS = 180.0
META_TASK_PAUSE_SECONDS = 1800.0
FAILED_DELIVERY_RETRY_SECONDS = 20.0

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

def build_dispatch_message(agent_role):
    if agent_role not in {"Codex", "Cowork"}:
        raise ValueError(f"Unknown agent role: {agent_role}")
    if not CANONICAL_DISPATCHER.exists():
        raise FileNotFoundError(f"Missing canonical dispatcher: {CANONICAL_DISPATCHER}")
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
    result = subprocess.run(
        [python_exe, str(CANONICAL_DISPATCHER), agent_role],
        cwd=str(REPO_ROOT),
        env=env,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise RuntimeError(
            "Canonical dispatcher failed via fallback python:\n"
            f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
        )
    return result.stdout


def extract_task_id(message):
    for line in message.splitlines():
        if line.startswith("Task id:"):
            return line.split(":", 1)[1].strip()
    return "<unknown>"


def repeat_pause_seconds(task_id):
    if task_id == "META-GENERATE-TASKS-001":
        return META_TASK_PAUSE_SECONDS
    return REPEAT_TASK_PAUSE_SECONDS


def confirm_app_reacted(app, timeout=SEND_METHOD_CONFIRM_SECONDS):
    deadline = time.time() + timeout
    last_d = None
    while time.time() < deadline:
        ready, d = app.is_ready()
        last_d = d
        if not ready:
            return True, d
        time.sleep(SEND_METHOD_CONFIRM_POLL)
    return False, last_d


def submit_current_prompt(app):
    if app.mode == "ready":
        strategies = (
            ("enter", lambda: pyautogui.press("enter")),
            ("calibrated-button", lambda: (
                safe_move_to(app.ref_x, app.ref_y, duration=0.08),
                time.sleep(0.05),
                pyautogui.click(),
            )),
            ("ctrl-enter", lambda: pyautogui.hotkey("ctrl", "enter")),
        )
    else:
        strategies = (
            ("enter", lambda: pyautogui.press("enter")),
            ("ctrl-enter", lambda: pyautogui.hotkey("ctrl", "enter")),
        )
    for name, action in strategies:
        action()
        ok, d = confirm_app_reacted(app)
        if ok:
            return True, name, d
        if d is None:
            print(f"  [{app.name}] método {name} sin lectura de detector.")
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
    ok, method, d = submit_current_prompt(app)
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
        self.pending_message = None
        self.pending_task_id = None

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

    if codex.load():
        apps.append(codex)
        print(f"[+] {codex.name} (modo={codex.mode}, umbral={codex.threshold}) "
              f"en ({codex.ref_x}, {codex.ref_y})")
    else:
        print(f"[-] {codex.name}: sin calibrar (--calibrate-codex)")

    if not args.codex_only and cowork.load():
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
    print(f"\nMODO AUTOMÁTICO ({cap_msg}). Ctrl+C para parar.")
    print(f"Política: Codex primario; Cowork sidecar cada "
          f"{args.cowork_sidecar_interval:.0f}s como mínimo.")
    print("Si el ratón toca (0,0) el script PAUSA 5s y reanuda solo.\n")

    last_state = {}

    while True:
        try:
            ready_apps = []
            for app in apps:
                if not app.enabled:
                    continue
                if app.is_paused():
                    continue

                ready, d = app.is_ready()
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
                    # Vimos ocupado de verdad: la racha fantasma se rompe
                    app.ghost_streak = 0
                    app.pending_message = None
                    app.pending_task_id = None

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
                              f"{remaining}s; Codex remains primary.")
                        continue
                if app.pending_message:
                    message = app.pending_message
                    task_id = app.pending_task_id or extract_task_id(message)
                else:
                    message = build_dispatch_message(app.name)
                    task_id = extract_task_id(message)
                    app.pending_message = message
                    app.pending_task_id = task_id
                task_line = f"Task id: {task_id}"
                now = time.time()
                pause_seconds = repeat_pause_seconds(task_id)
                if app.pending_message:
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

                print(f"[OK] {app.name} listo. Enviando #{app.sends+1}: {task_line}")
                delivered, method, d_after_send = send_reply(app, message)
                app.sends += 1
                app.last_sent_task_id = task_id
                app.last_sent_at = time.time()
                if app.name == "Cowork":
                    last_cowork_dispatch_at = app.last_sent_at
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
                    print(f"  [{app.name}] ocupado confirmado vía {method} "
                          f"(d={d_after_send:.1f}), rearmado.")
                while not rearmed_with_busy and time.time() < deadline:
                    r, d = app.is_ready()
                    if not r:
                        app.armed = True
                        rearmed_with_busy = True
                        app.last_confirmed_busy_at = time.time()
                        app.pending_message = None
                        app.pending_task_id = None
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
                print("\nInterrumpido durante pausa.")
                return
            last_state.clear()
            continue

        except KeyboardInterrupt:
            print("\nInterrumpido.")
            return

        except Exception as e:
            print(f"\n[!] Error inesperado: {type(e).__name__}: {e}")
            print("    Pausa de 3s y sigo...")
            try:
                time.sleep(3.0)
            except KeyboardInterrupt:
                print("\nInterrumpido durante pausa.")
                return
            last_state.clear()
            continue


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("agent", nargs="?", choices=["Codex", "Cowork"],
                   help="Print one structured task dispatch for this agent and exit.")
    p.add_argument("--calibrate-codex", action="store_true")
    p.add_argument("--calibrate-cowork", action="store_true")
    p.add_argument("--diagnose-coords", action="store_true")
    p.add_argument("--codex-only", action="store_true",
                   help="Watch only Codex; useful while debugging left-screen delivery.")
    p.add_argument("--cowork-sidecar-interval", type=float,
                   default=DEFAULT_COWORK_SIDECAR_INTERVAL,
                   help="Minimum seconds between Cowork sidecar dispatches.")
    args = p.parse_args()
    if args.agent:
        print(build_dispatch_message(args.agent))
    elif args.calibrate_codex:
        calibrate_codex()
    elif args.calibrate_cowork:
        calibrate_cowork()
    elif args.diagnose_coords:
        diagnose_coords()
    else:
        run(args)
