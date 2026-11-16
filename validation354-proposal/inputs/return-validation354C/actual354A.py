"""Actual portable-return CLI; accepts no prepared fake receipt as actual input."""
import json,sys
from pathlib import Path
from validate354A import validate_file,need,SOURCE
if len(sys.argv)!=4:raise ValueError('usage: actual354A.py ARCHIVE BYTES SHA256')
need(sys.argv[2].isdigit(),'Decimal transport byte count')
answer=validate_file(Path(sys.argv[1]),int(sys.argv[2]),sys.argv[3])
print(json.dumps(dict(status='RAW_RETURN_VALIDATED_PENDING_VISUAL_AND_EXACT_PDF_ASSESSMENT',**answer),sort_keys=True))
