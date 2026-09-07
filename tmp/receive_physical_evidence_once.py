"""Single-process loopback evidence receiver; 25-second total deadline."""
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import parse_qs
from pathlib import Path
import base64, hashlib, io, time
from PIL import Image

EXPECTED = 'f75abadc466198d1db07eefeafc00894803ea9cc4b4127c2f30b266ae3b75b6b'
DEST = Path('C:/Users/lluis/Downloads/hrpoly-neumann-physical-character-promoted-cold-v1-evidence.tar.gz')
done = False
class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        body = b'<html><body><h1>Local evidence receiver</h1><form method="post"><label>Evidence PNG base64<textarea name="payload"></textarea></label><button type="submit">Preserve evidence</button></form></body></html>'
        self.send_response(200); self.end_headers(); self.wfile.write(body)
    def do_POST(self):
        global done
        try:
            size = int(self.headers['Content-Length'])
            assert 0 < size < 500000
            raw = parse_qs(self.rfile.read(size).decode())['payload'][0]
            image = Image.open(io.BytesIO(base64.b64decode(raw, validate=True)))
            assert image.mode == 'RGB' and image.size == (256, 201)
            payload = image.tobytes()[:153915]
            assert hashlib.sha256(payload).hexdigest() == EXPECTED
            if DEST.exists():
                assert DEST.read_bytes() == payload
            else:
                DEST.write_bytes(payload)
            message = 'LOCAL_TRANSFER_PASS ' + EXPECTED
            self.send_response(200)
            done = True
        except Exception as error:
            message = 'LOCAL_TRANSFER_FAIL ' + repr(error)
            self.send_response(400)
            done = True
        self.end_headers(); self.wfile.write(message.encode())
        print(message, flush=True)

server = HTTPServer(('127.0.0.1', 8766), Handler)
deadline = time.monotonic() + 25
print('RECEIVER_READY http://127.0.0.1:8766', flush=True)
while not done and time.monotonic() < deadline:
    server.timeout = min(1, deadline - time.monotonic())
    server.handle_request()
server.server_close()
if not done:
    raise SystemExit('RECEIVER_TIMEOUT')
