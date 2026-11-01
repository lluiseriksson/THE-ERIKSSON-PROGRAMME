param([Parameter(Mandatory=$true)][string]$Zip,[Parameter(Mandatory=$true)][string]$Prefix)
$ErrorActionPreference='Stop'
Add-Type -AssemblyName System.IO.Compression.FileSystem
$z=[IO.Compression.ZipFile]::OpenRead($Zip)
function ReadEntry([string]$name){$ent=$z.GetEntry($name);if($null -eq $ent){throw "Missing $name"};$rd=[IO.StreamReader]::new($ent.Open());try{$rd.ReadToEnd()}finally{$rd.Dispose()}}
try{
 $m=ReadEntry 'manifest.json'|ConvertFrom-Json -AsHashtable -DateKind String
 foreach($name in $m.Keys){$ent=$z.GetEntry($name);if($null -eq $ent){throw "Missing $name"};$st=$ent.Open();try{$h=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($st)).ToLowerInvariant()}finally{$st.Dispose()};if($h -ne $m[$name]){throw "Manifest mismatch: $name"}}
 $report=ReadEntry 'report.json'|ConvertFrom-Json -AsHashtable -DateKind String
 foreach($name in @('report.json','focal-build.log','oracle.log','source-hashes.json','exception.txt')){if($z.GetEntry($name)){[IO.File]::WriteAllText($Prefix+'-'+$name,(ReadEntry $name),[Text.UTF8Encoding]::new($false))}}
 $validation=[ordered]@{bundle_integrity='MANIFEST_VALIDATED_ONLY';mathematical_pass=($report.status -eq 'FOCAL_REPRODUCTION_PASS');source_sha=$report.source_sha;status=$report.status;zip_sha256=(Get-FileHash -LiteralPath $Zip).Hash.ToLowerInvariant();manifest_entries=$m.Count;error=$report.error;steps=$report.steps;started_utc=$report.started_utc;finished_utc=$report.finished_utc}
 $validation|ConvertTo-Json -Depth 12|Set-Content -LiteralPath ($Prefix+'-integrity.json') -Encoding utf8
 $validation|ConvertTo-Json -Depth 12
}finally{$z.Dispose()}
