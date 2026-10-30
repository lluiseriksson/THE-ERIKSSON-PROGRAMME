param([Parameter(Mandatory=$true)][string]$ZipPath,[Parameter(Mandatory=$true)][string]$ExpectedZipHash,[Parameter(Mandatory=$true)][string]$ExtractTo)
$ErrorActionPreference='Stop'
if((Get-Item -LiteralPath $ZipPath).Length -gt 6MB){throw 'Bundle exceeds bounded local-light input limit'}
$actual=(Get-FileHash -LiteralPath $ZipPath -Algorithm SHA256).Hash.ToLower()
if($actual -ne $ExpectedZipHash){throw 'Bundle digest mismatch'}
Add-Type -AssemblyName System.IO.Compression.FileSystem
$z=[IO.Compression.ZipFile]::OpenRead($ZipPath)
try{
 function Read-Entry([string]$name){$e=$z.GetEntry($name);if(!$e){throw 'Missing entry'};$r=[IO.StreamReader]::new($e.Open());try{$r.ReadToEnd()}finally{$r.Dispose()}}
 $m=Read-Entry 'manifest.json'|ConvertFrom-Json
 foreach($v in $m.PSObject.Properties){
  if($v.Name -match '[/\\]' -or $v.Name -eq '..'){throw 'Unexpected entry path'}
  $e=$z.GetEntry($v.Name);if(!$e){throw 'Missing manifest entry'};$s=$e.Open()
  try{$hash=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($s)).ToLower()}finally{$s.Dispose()}
  if($hash -ne $v.Value){throw 'Manifest digest mismatch'}
 }
 $r=Read-Entry 'report.json'|ConvertFrom-Json
 if($r.source_sha -ne 'd803cd3b920a7547420352ed28abc204593d1685' -or $r.source_sha256 -ne 'ec1f4090f71d9bf0260bba62ebdb507286d121a72c93ad6e5d4c06d484a9c5dd'){throw 'Source mismatch'}
 if($r.status -ne 'PDF_COMPILED_ALL_PAGES_RENDERED_AWAITING_VISUAL_QA'){throw 'Wrong render status'}
 if($r.pages -ne 8 -or $r.steps.Count -ne 9){throw 'Unexpected page/step count'}
 foreach($step in $r.steps){if($step.exit_code -ne 0){throw 'Failed step'}}
 if($r.layout_warnings.Count -ne 0){throw 'Unresolved layout warning'}
 if($m.'flat_coarse_rank.tex' -ne $r.source_sha256 -or $m.'flat_coarse_rank.pdf' -ne $r.pdf_sha256){throw 'Report/manifest mismatch'}
 if(@($z.Entries|Where-Object{$_.Name -match '^page-\d+\.jpg$'}).Count -ne 8){throw 'Missing rendered page'}
 if(Test-Path -LiteralPath $ExtractTo){throw 'Extraction target already exists'}
 [IO.Compression.ZipFileExtensions]::ExtractToDirectory($z,$ExtractTo,$false)
 [ordered]@{status='PDF_RENDER_BUNDLE_HASH_VALIDATED';zip_sha256=$actual;source_sha=$r.source_sha;source_sha256=$r.source_sha256;pdf_sha256=$r.pdf_sha256;pages=8;manifest_entries=@($m.PSObject.Properties).Count;exit_zero_steps=9;layout_warnings=0;started_utc=([datetime]$r.started_utc).ToUniversalTime().ToString('o');finished_utc=([datetime]$r.finished_utc).ToUniversalTime().ToString('o');visual_inspection='separate report required';independent_review=$false}|ConvertTo-Json
}finally{$z.Dispose()}
