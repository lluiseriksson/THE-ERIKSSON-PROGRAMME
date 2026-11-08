"""Export existing Colab bytes only; run one chosen part, never rerun the build."""
import base64
import hashlib
import json
import platform
import textwrap

if platform.system() != 'Linux':
    raise RuntimeError('Existing own Colab Linux session required')

PART = 0  # Replace only this index for the next already-existing byte range.
CHARS = 500000  # Multiple of four: each piece decodes to its exact byte range.
if 'encoded195' not in globals() or 'bundle' not in globals():
    raise RuntimeError('Build bytes are not present; do not infer or regenerate them')
pieces = (len(encoded195)+CHARS-1)//CHARS
if PART < 0 or PART >= pieces:
    raise ValueError('Part outside existing archive')
piece = encoded195[PART*CHARS:(PART+1)*CHARS]
decoded = base64.b64decode(piece, validate=True)
print('CHUNK195='+json.dumps({'part': PART, 'parts': pieces, 'base64_chars': len(piece),
                            'decoded_bytes': len(decoded),
                            'decoded_sha256': hashlib.sha256(decoded).hexdigest(),
                            'archive_bytes': bundle.stat().st_size}))
print('\n'.join(textwrap.wrap(piece, 120)))
print('END195')
