# Bounded byte transport, not evidence validation or a compiler invocation.
# Reads only the explicit archive marker block copied from the Colab output.
$ErrorActionPreference = 'Stop'
$timer = [Diagnostics.Stopwatch]::StartNew()
$expected = 'd3a73641df6341b62f29b25682927993224957ce603e1098d380b6ed62bde996'
$destination = Join-Path $env:USERPROFILE 'Downloads/neumann-integer-image-owner-hot-v1.tar.gz'
if (Test-Path -LiteralPath $destination) { throw 'NO_OVERWRITE' }
$text = Get-Clipboard -Raw
if ($text.Length -gt 1048576) { throw 'TEXT_SIZE' }
$match = [regex]::Match($text, '\AHRPOLY_ARCHIVE_BASE64_BEGIN\r?\n([A-Za-z0-9+/=\r\n]+)\r?\nHRPOLY_ARCHIVE_BASE64_END\s*\z')
if (-not $match.Success) { throw 'ARCHIVE_MARKERS_ABSENT_NO_CLIPBOARD_CONTENT_PRINTED' }
$bytes = [Convert]::FromBase64String($match.Groups[1].Value)
$sha = [Security.Cryptography.SHA256]::Create()
$actual = [BitConverter]::ToString($sha.ComputeHash($bytes)).Replace('-', '').ToLowerInvariant()
if ($actual -ne $expected) { throw 'ARCHIVE_HASH_MISMATCH_NO_WRITE' }
if ($timer.Elapsed.TotalSeconds -gt 25) { throw 'LOCAL_TIME_BUDGET' }
$stream = [IO.File]::Open($destination, [IO.FileMode]::CreateNew, [IO.FileAccess]::Write)
try { $stream.Write($bytes, 0, $bytes.Length) } finally { $stream.Dispose() }
$timer.Stop()
'ARCHIVE_BYTE_RECOVERY=PASS'
'SHA256=' + $actual
'BYTES=' + $bytes.Length
'SECONDS=' + $timer.Elapsed.TotalSeconds
'PATH=' + $destination
