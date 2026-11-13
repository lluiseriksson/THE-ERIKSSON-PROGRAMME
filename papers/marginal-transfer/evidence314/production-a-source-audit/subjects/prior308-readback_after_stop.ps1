Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
. (Join-Path $PSScriptRoot 'capture_cli_atomic.ps1')
$out='D:\Datos\the-eriksson-programme\autonomia\evidencia-308\production-a\attempt-a'
if(-not(Test-Path -LiteralPath (Join-Path $out 'release.exit'))){throw 'Actual stop capture required first'}
$command='export GOOGLE_APPLICATION_CREDENTIALS=/mnt/c/Users/lluis/AppData/Roaming/gcloud/application_default_credentials.json; exec /home/lluis/.local/bin/colab --auth adc --config /home/lluis/.config/colab-cli/tep308-build-a-sessions.json sessions'
$code=Invoke-CapturedWsl -Name 'backend-readback' -ShellCommand $command -OutputDirectory $out
if($code -ne 0){throw 'Actual backend readback nonzero'}
Get-Content -LiteralPath (Join-Path $out 'backend-readback.log')
Get-Content -LiteralPath (Join-Path $out 'backend-readback.stderr.log')
# Query zero alone never proves inactivity; parent must read the actual backend log.
