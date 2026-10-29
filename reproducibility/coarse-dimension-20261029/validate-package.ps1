param(
 [Parameter(Mandatory=$true)][string]$ZipPath,
 [Parameter(Mandatory=$true)][string]$ExpectedZipHash,
 [Parameter(Mandatory=$true)][string]$ExpectedSourceHashes
)
$ErrorActionPreference='Stop'
$actualZip=(Get-FileHash -LiteralPath $ZipPath -Algorithm SHA256).Hash.ToLower()
if($actualZip -ne $ExpectedZipHash.ToLower()){throw 'ZIP digest mismatch'}
Add-Type -AssemblyName System.IO.Compression.FileSystem
$z=[IO.Compression.ZipFile]::OpenRead($ZipPath)
try {
 function Read-ZipText([string]$name){
  $e=$z.GetEntry($name); if($null -eq $e){throw "Missing $name"}
  $reader=[IO.StreamReader]::new($e.Open())
  try{$reader.ReadToEnd()}finally{$reader.Dispose()}
 }
 $manifest=Read-ZipText 'manifest.json'|ConvertFrom-Json
 if(@($manifest.PSObject.Properties).Count -ne 12){throw 'Wrong manifest count'}
 foreach($p in $manifest.PSObject.Properties){
  $entry=$z.GetEntry($p.Name); if($null -eq $entry){throw 'Missing manifest entry'}
  $stream=$entry.Open()
  try{$got=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($stream)).ToLower()}
  finally{$stream.Dispose()}
  if($got -ne $p.Value){throw "Entry digest mismatch: $($p.Name)"}
 }
 $report=Read-ZipText 'report.json'|ConvertFrom-Json
 if($report.status -ne 'FOCAL_REPRODUCTION_PASS' -or
    $report.source_sha -ne 'b2313402cefb896c899ab4afb3c4d2aed75d95d4'){
  throw 'Wrong source/verdict'
 }
 $steps=@('install-elan','git-init','git-remote','git-fetch','git-checkout',
          'lean-version','cache-get','focal-build','oracle')
 if($report.steps.Count -ne 9){throw 'Wrong step count'}
 for($i=0;$i -lt 9;$i++){
  if($report.steps[$i].name -ne $steps[$i] -or $report.steps[$i].exit_code -ne 0){throw 'Failed step'}
 }
 $expected=Get-Content -LiteralPath $ExpectedSourceHashes -Raw|ConvertFrom-Json
 $sources=Read-ZipText 'source-hashes.json'|ConvertFrom-Json
 if($sources.Count -ne 2){throw 'Wrong source count'}
 foreach($p in $expected.PSObject.Properties){
  $row=@($sources|Where-Object{$_.name -eq $p.Name})
  if($row.Count -ne 1 -or $row[0].sha256_lf -ne $p.Value -or !$row[0].matches){throw 'Source mismatch'}
 }
 $oracle=Read-ZipText 'oracle.log'
 $found=[regex]::Matches($oracle,"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
 $names=@('exists_unseen_of_finrank_lt_measurement_add_repair',
          'factorized_coercivity_false_of_dimension_budget','factorized_coercivity_dimension_budget')
 if($found.Count -ne 3 -or $report.oracle_reports.Count -ne 3){throw 'Wrong oracle count'}
 for($i=0;$i -lt 3;$i++){
  $want='YangMills.RG.'+$names[$i]
  if($found[$i].Groups[1].Value -ne $want -or $report.oracle_reports[$i].name -ne $want){throw 'Wrong oracle name'}
  $axs=@($found[$i].Groups[2].Value.Split(',')|ForEach-Object{$_.Trim()})
  if($axs.Count -ne 3 -or @(Compare-Object $axs @('propext','Classical.choice','Quot.sound')).Count -ne 0){throw 'Unexpected axioms'}
 }
 [ordered]@{
  status='ABSTRACT_DIMENSION_MODULE_VALIDATED';zip_sha256=$actualZip
  source_sha=$report.source_sha;manifest_entries=12;source_files=2;exit_zero_steps=9;oracle_reports=3
  target_olean_sha256=$report.target_olean_sha256
  oracle_log_sha256=$manifest.'oracle.log';source_manifest_sha256=$manifest.'source-hashes.json'
  started_utc=$report.started_utc;finished_utc=$report.finished_utc
  scope='Abstract dimension obstruction only; concrete Fourier band not yet formalized'
 }|ConvertTo-Json
}finally{$z.Dispose()}
