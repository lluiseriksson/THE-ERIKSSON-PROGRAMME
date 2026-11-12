param([Parameter(Mandatory=$true)][ValidatePattern('^[a-f0-9]{64}$')][string]$ApprovedManifestSha256,[Parameter(Mandatory=$true)][ValidatePattern('^[a-f0-9]{40}$')][string]$SourceSha)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$diagnosticHash='495a00952c4869f313c2245c1a089498fe8775dccb789ee617a078271eb23ee0'
$constructionBase='4ba7c61adb94d80f4cb985ab78e84d8346171b02'
. (Join-Path $PSScriptRoot 'capture_cli_atomic.ps1')
$manifest=Join-Path $PSScriptRoot 'RUNNER-HASHES.json'
if((Get-FileHash -LiteralPath $manifest).Hash.ToLowerInvariant() -cne $ApprovedManifestSha256){throw 'Exact281 runner manifest required'}
$entries=@(Get-Content -LiteralPath $manifest -Raw|ConvertFrom-Json)
if($entries.Count -ne 5){throw 'Five frozen operative files required'}
foreach($entry in $entries){$p=Join-Path $PSScriptRoot $entry.path;if((Get-Item -LiteralPath $p).Length -ne $entry.bytes -or (Get-FileHash -LiteralPath $p).Hash.ToLowerInvariant() -cne $entry.sha256){throw ('Frozen281 input differs: '+$entry.path)}}
$evidence='D:\Datos\the-eriksson-programme\autonomia\evidencia-281'
$authority=Get-Content -LiteralPath (Join-Path $evidence 'parent-authority-relay.json') -Raw|ConvertFrom-Json
if($authority.source -cne $SourceSha -or $authority.diagnostic_source_sha256 -cne $diagnosticHash -or $authority.runner_manifest_sha256 -cne $ApprovedManifestSha256 -or $authority.parent_full_mathematical_report_read -ne $true -or $authority.parent_full_engineering_report_read -ne $true -or $authority.mathematical_accepted -ne $true -or $authority.engineering_accepted -ne $true){throw 'Actual separate full mathematical/engineering reviews and parent read gate required'}
foreach($kind in @('mathematical','engineering')){$pf=$kind+'_report_path';$hf=$kind+'_report_sha256';if(-not[regex]::IsMatch([string]$authority.$hf,'\A[a-f0-9]{64}\z') -or (Get-FileHash -LiteralPath ([string]$authority.$pf)).Hash.ToLowerInvariant() -cne [string]$authority.$hf){throw 'Actual full review report hash differs'}}
$out=Join-Path $evidence 'attempt-a'
if(Test-Path -LiteralPath $out){throw 'Preserve previous281 attempt; no blind rerun'}
New-Item -ItemType Directory -Path $out|Out-Null
$prefix='export GOOGLE_APPLICATION_CREDENTIALS=/mnt/c/Users/lluis/AppData/Roaming/gcloud/application_default_credentials.json; exec /home/lluis/.local/bin/colab --auth adc --config /home/lluis/.config/colab-cli/tep281-diagnostic-sessions.json'
$session='tep281-diagnostic-own-cpu'
$script='/mnt/c/Trabajo/the-eriksson-programme/solenoidal-layers275-20261112/research/full-cost281/launch281.py'
$remote='/content/tep281-diagnostic-envelope.zip'
$local='/mnt/d/Datos/the-eriksson-programme/autonomia/evidencia-281/attempt-a/tep281-diagnostic-envelope.zip'
$localPath=Join-Path $out 'tep281-diagnostic-envelope.zip'
$attempted=$false;$exits=[ordered]@{};$caught=$null;$childVerified=$false;$summary=$null
[IO.File]::WriteAllText((Join-Path $out 'runtime-open-requested.txt'),[DateTime]::UtcNow.ToString('o')+"`n")
try{
 $attempted=$true;$exits.allocation=Invoke-CapturedWsl -Name 'allocation' -ShellCommand ($prefix+' new -s '+$session+' --high-mem') -OutputDirectory $out
 if($exits.allocation -ne 0){throw 'Actual allocation failed; preserve rejection and stop own session if any'}
 $exits.execution=Invoke-CapturedWsl -Name 'execution' -ShellCommand ($prefix+' exec -s '+$session+' -f '+$script+' --timeout 3600') -OutputDirectory $out
 $exits.download=Invoke-CapturedWsl -Name 'download' -ShellCommand ($prefix+' download -s '+$session+' '+$remote+' '+$local) -OutputDirectory $out
 $lines=@(Get-Content -LiteralPath (Join-Path $out 'execution.log')|Where-Object{$_.StartsWith('TEP281_LAUNCH_RESULT ')})
 if($lines.Count -ne 1){throw 'One real281 bootstrap summary required; CLI0 is not Python success'}
 $summary=$lines[0].Substring('TEP281_LAUNCH_RESULT '.Length)|ConvertFrom-Json
 if($summary.schema -cne 'TEP281-LAUNCH-1.0' -or $summary.diagnostic_source_sha256 -cne $diagnosticHash -or $summary.actual_child_started -ne $true -or $summary.child_exit -ne 0 -or $summary.timed_out -ne $false -or $summary.status -cne 'FINITE_DIAGNOSTIC_ARTIFACT_CAPTURED_PENDING_PARENT_REVIEW'){throw 'Actual standalone281 child failed; preserve envelope'}
 if($exits.download -ne 0 -or (Get-Item -LiteralPath $localPath).Length -ne $summary.envelope_bytes -or (Get-FileHash -LiteralPath $localPath).Hash.ToLowerInvariant() -cne $summary.envelope_sha256){throw 'Actual281 downloaded envelope differs'}
 Add-Type -AssemblyName System.IO.Compression.FileSystem
 $z=[IO.Compression.ZipFile]::OpenRead($localPath)
 try{
  $entry=$z.GetEntry('launch/receipt.json');$exitEntry=$z.GetEntry('launch/child.exit')
  if($null -eq $entry -or $null -eq $exitEntry -or $null -eq $z.GetEntry('launch/diagnostic-results.zip')){throw 'Actual receipt/decimal/nativeZIP missing'}
  $s=$entry.Open();$mem=[IO.MemoryStream]::new();try{$s.CopyTo($mem)}finally{$s.Dispose()};$raw=$mem.ToArray();$mem.Dispose();$hash=[Security.Cryptography.SHA256]::Create();try{$rh=[Convert]::ToHexString($hash.ComputeHash($raw)).ToLowerInvariant()}finally{$hash.Dispose()}
  if($rh -cne $summary.receipt_sha256){throw 'Actual receipt raw hash differs'}
  $receipt=[Text.Encoding]::UTF8.GetString($raw)|ConvertFrom-Json;$reader=[IO.StreamReader]::new($exitEntry.Open(),[Text.Encoding]::ASCII);try{$actual=$reader.ReadToEnd()}finally{$reader.Dispose()}
  if($actual -cne "0`n" -or $receipt.child_exit -ne 0 -or $receipt.timed_out -ne $false -or $receipt.diagnostic_source_sha256 -cne $diagnosticHash -or $receipt.diagnostic_actual_source_sha256 -cne $diagnosticHash -or $receipt.diagnostic_construction_base -cne $constructionBase -or $receipt.status -cne $summary.status -or @($receipt.commands).Count -ne 3 -or @($receipt.commands|Where-Object{$_.exit -ne 0 -or $_.timed_out -ne $false}).Count -ne 0){throw 'Actual281 standalone receipt/exit/source differs'}
 }finally{$z.Dispose()}
 $childVerified=$true
}catch{$caught=$_.Exception.ToString();[IO.File]::WriteAllText((Join-Path $out 'outer-failure.txt'),$caught+"`n")}
finally{
 if($attempted){$exits.release=Invoke-CapturedWsl -Name 'release' -ShellCommand ($prefix+' stop -s '+$session) -OutputDirectory $out}
 [IO.File]::WriteAllText((Join-Path $out 'runtime-release-finished.txt'),[DateTime]::UtcNow.ToString('o')+"`n")
 [ordered]@{parent_authorized_source=$SourceSha;construction_base=$constructionBase;actual_diagnostic_source_sha256=$diagnosticHash;runner_manifest_sha256=$ApprovedManifestSha256;actual_cli_exits=$exits;actual_standalone_receipt_verified=$childVerified;failure=$caught;bootstrap_summary=$summary;runtime_type='own CPU high-memory';billing_units=$null;status='Diagnostic artifact transport only; full returned mathematics/source audit and literal inactive backend still required';certificate=$false}|ConvertTo-Json -Depth 16|Set-Content -LiteralPath (Join-Path $out 'outer-report.json') -Encoding utf8NoBOM
}
if($null -ne $caught -or -not $childVerified -or $exits.Count -ne 4 -or @($exits.Values|Where-Object{$_ -ne 0}).Count -ne 0){throw 'Actual281 standalone/CLI failure; preserve all outputs'}
