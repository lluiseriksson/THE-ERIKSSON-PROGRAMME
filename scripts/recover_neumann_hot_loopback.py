"""One-shot local evidence transport, not a compiler or mathematical check.

Serves only loopback for at most 25 seconds, without threads/process pools.
Accepts one bounded base64 payload and writes only after the pinned SHA matches.
"""
import base64
import hashlib
import html
import json
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
import secrets
import time
from urllib.parse import parse_qs

EXPECTED = 'd3a73641df6341b62f29b25682927993224957ce603e1098d380b6ed62bde996'
DEST = Path('C:/Users/lluis/Downloads/neumann-integer-image-owner-hot-v1.tar.gz')
START = time.monotonic()
ROUTE = '/recover-' + secrets.token_hex(12)
done = False


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def reply(self, status, body):
        self.send_response(status)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(body.encode())

    def do_GET(self):
        if self.path != ROUTE:
            self.reply(404, 'Unknown route')
            return
        self.reply(200, '<h1>Local evidence recovery</h1><p>No external transfer. '
                   'Pinned archive SHA required.</p><form method="post">'
                   '<label for="payload">Verified Colab archive text</label>'
                   '<textarea id="payload" name="payload"></textarea>'
                   '<button type="submit">Preserve exact archive</button></form>')

    def do_POST(self):
        global done
        try:
            assert self.path == ROUTE, 'UNEXPECTED_ROUTE'
            assert self.headers.get('Origin', '') in ('', 'http://127.0.0.1:8765'), 'ORIGIN'
            size = int(self.headers.get('Content-Length', '0'))
            assert 0 < size <= 200000, 'SIZE_LIMIT'
            self.connection.settimeout(2)
            raw = self.rfile.read(size)
            assert len(raw) == size, 'INCOMPLETE_BODY'
            fields = parse_qs(raw.decode('ascii'), strict_parsing=True)
            assert set(fields) == {'payload'} and len(fields['payload']) == 1, 'FIELDS'
            text = fields['payload'][0].strip()
            begin, end = 'HRPOLY_ARCHIVE_BASE64_BEGIN', 'HRPOLY_ARCHIVE_BASE64_END'
            assert text.startswith(begin) and text.endswith(end), 'MARKERS'
            payload = base64.b64decode(''.join(text[len(begin):-len(end)].split()), validate=True)
            assert hashlib.sha256(payload).hexdigest() == EXPECTED, 'HASH_MISMATCH'
            assert not DEST.exists(), 'DESTINATION_EXISTS_NO_OVERWRITE'
            with DEST.open('xb') as out:
                out.write(payload)
            assert hashlib.sha256(DEST.read_bytes()).hexdigest() == EXPECTED
            print(json.dumps({'status': 'TRANSPORT_PASS', 'sha256': EXPECTED,
                              'bytes': len(payload), 'destination': str(DEST),
                              'seconds': time.monotonic() - START}), flush=True)
            self.reply(200, '<h1>TRANSPORT_PASS</h1><p>' + EXPECTED + '</p>')
            done = True
        except Exception as exc:
            self.reply(400, '<h1>TRANSPORT_REJECTED</h1><p>' + html.escape(str(exc)) + '</p>')
            print('TRANSPORT_REJECTED=' + type(exc).__name__, flush=True)


with HTTPServer(('127.0.0.1', 8765), Handler) as server:
    server.timeout = 0.2
    print('LOCAL_RECOVERY_URL=http://127.0.0.1:8765' + ROUTE, flush=True)
    while not done and time.monotonic() - START < 25:
        server.handle_request()
print('LOCAL_RECOVERY_SECONDS=' + str(time.monotonic() - START), flush=True)
raise SystemExit(0 if done else 2)
