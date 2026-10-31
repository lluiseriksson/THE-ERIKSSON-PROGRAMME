param([Parameter(Mandatory=$true)][string]$Zip,[Parameter(Mandatory=$true)][string]$Destination)
$ErrorActionPreference='Stop'
$started=[Diagnostics.Stopwatch]::StartNew()
$expectedSource='dbd8be9909204daea99ca442918e4fae238b8bbc'
$expectedTex='9757b9450a4f8e06101b4a74ae316a8da0c6f4fbfd685be2df24102b5d01a588'
$z=[IO.Compression.ZipFile]::OpenRead($Zip)
function ReadEntry($name){$en=$z.GetEntry($name);if($null -eq $en){throw "Missing $name"};$rd=[IO.StreamReader]::new($en.Open());try{$rd.ReadToEnd()}finally{$rd.Dispose()}}
try{
 $m=ReadEntry 'manifest.json'|ConvertFrom-Json -AsHashtable -DateKind String
 foreach($name in $m.Keys){
  if([IO.Path]::GetFileName($name) -ne $name -or $name.Contains('..')){throw 'Unsafe entry'}
  $en=$z.GetEntry($name);if($null -eq $en){throw "Missing $name"}
  $st=$en.Open();try{$hash=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($st)).ToLowerInvariant()}finally{$st.Dispose()}
  if($hash -ne $m[$name]){throw "Manifest mismatch $name"}
 }
 $r=ReadEntry 'report.json'|ConvertFrom-Json -AsHashtable -DateKind String
 if($r.status -ne 'PDF_COMPILED_ALL_PAGES_RENDERED_AWAITING_VISUAL_QA' -or $r.source_sha -ne $expectedSource -or $r.source_sha256 -ne $expectedTex -or $m['flat_coarse_rank.tex'] -ne $expectedTex -or $m['flat_coarse_rank.pdf'] -ne $r.pdf_sha256){throw 'Wrong render source/verdict/hash'}
 if(@($r.steps|Where-Object exit_code -ne 0).Count -or @($r.steps).Count -ne 8){throw 'Render stage failure/count'}
 if($r.pages -lt 14 -or $r.pages -gt 25){throw 'Unexpected page count'}
 if(@($m.Keys|Where-Object {$_ -match '^page-\d+\.jpg$'}).Count -ne $r.pages){throw 'Missing page images'}
 [IO.Directory]::CreateDirectory($Destination)|Out-Null
 foreach($name in $m.Keys){$en=$z.GetEntry($name);$inputStream=$en.Open();$outputStream=[IO.File]::Create((Join-Path $Destination $name));try{$inputStream.CopyTo($outputStream)}finally{$inputStream.Dispose();$outputStream.Dispose()}}
 [IO.File]::WriteAllText((Join-Path $Destination 'manifest.json'),(ReadEntry 'manifest.json'))
 $started.Stop()
 $v=@{status='EXACT_SOURCE_RENDER_INTEGRITY_VALIDATED_VISUAL_QA_PENDING';source_sha=$r.source_sha;source_lf_sha256=$r.source_sha256;pdf_sha256=$r.pdf_sha256;pages=$r.pages;manifest_entries=$m.Count;rendered_pages=$r.pages;layout_warnings=$r.layout_warnings;zip_sha256=(Get-FileHash -LiteralPath $Zip).Hash.ToLowerInvariant();validation_seconds=$started.Elapsed.TotalSeconds;peak_current_process_rss_bytes=[Diagnostics.Process]::GetCurrentProcess().PeakWorkingSet64;validation_processes_started=0;independent_review=$false}
 [IO.File]::WriteAllText((Join-Path $Destination 'render055-validation.json'),($v|ConvertTo-Json -Depth 20))
 $v|ConvertTo-Json -Depth 20
}finally{$z.Dispose()}
