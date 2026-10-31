param([Parameter(Mandatory)][string]$Zip,[Parameter(Mandatory)][string]$Destination,
 [Parameter(Mandatory)][string]$SourceSha,[Parameter(Mandatory)][int]$Cases)
$ErrorActionPreference='Stop'
$watch=[Diagnostics.Stopwatch]::StartNew()
$z=[IO.Compression.ZipFile]::OpenRead($Zip)
try {
 $data=@{}
 foreach($entry in $z.Entries){
  if($entry.FullName -notmatch '^[a-zA-Z0-9_.-]+$' -or $entry.FullName.Contains('..') -or $data.ContainsKey($entry.FullName)){throw 'Unsafe/duplicate entry'}
  $ms=[IO.MemoryStream]::new();$stream=$entry.Open()
  try{$stream.CopyTo($ms)}finally{$stream.Dispose()}
  $data[$entry.FullName]=$ms.ToArray();$ms.Dispose()
 }
 if($data.Count -ne 9){throw 'Unexpected entry count'}
 $manifest=[Text.Encoding]::UTF8.GetString($data['manifest.json'])|ConvertFrom-Json -AsHashtable
 if($manifest.Count -ne 8){throw 'Incomplete manifest'}
 foreach($name in $manifest.Keys){
  if(!$data.ContainsKey($name) -or [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($data[$name])).ToLowerInvariant() -ne $manifest[$name]){throw "Hash mismatch: $name"}
 }
 $report=[Text.Encoding]::UTF8.GetString($data['report.json'])|ConvertFrom-Json -AsHashtable
 if($report.source_sha -ne $SourceSha -or $report.status -ne 'FINITE_PROBES_AND_MUTATIONS_MATCH_NOT_A_UNIVERSAL_PROOF' -or $report.steps.Count -ne 2 -or @($report.steps|Where-Object exit_code -ne 0).Count -ne 0 -or !$report.normal_optimized_match -or $report.cases -ne $Cases -or $report.formal_verification){throw 'Cloud report mismatch'}
 foreach($name in $report.source_hashes.Keys){if($manifest[$name] -ne $report.source_hashes[$name]){throw 'Source hash/report mismatch'}}
 [IO.Directory]::CreateDirectory($Destination)|Out-Null
 foreach($name in $data.Keys){[IO.File]::WriteAllBytes((Join-Path $Destination $name),$data[$name])}
 $watch.Stop()
 $result=[ordered]@{status='RAW_BUNDLE_INTEGRITY_VALIDATED_NOT_A_UNIVERSAL_PROOF';source_sha=$SourceSha;cases=$Cases;manifest_entries=8;bundle_entries=9;zip_sha256=(Get-FileHash -LiteralPath $Zip -Algorithm SHA256).Hash.ToLowerInvariant();seconds=$watch.Elapsed.TotalSeconds;child_processes_started=0;peak_process_rss_bytes=[Diagnostics.Process]::GetCurrentProcess().PeakWorkingSet64;local_mathematical_execution=$false}
 [IO.File]::WriteAllText((Join-Path $Destination 'integrity.json'),(($result|ConvertTo-Json)+"`n"),[Text.UTF8Encoding]::new($false))
 $result|ConvertTo-Json
} finally {$z.Dispose()}
