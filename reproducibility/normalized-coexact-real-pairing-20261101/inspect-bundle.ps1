param([Parameter(Mandatory)][string]$Zip,[Parameter(Mandatory)][string]$Destination)
$ErrorActionPreference='Stop'
$z=[IO.Compression.ZipFile]::OpenRead($Zip)
try {
 $seen=@{}
 foreach($e in $z.Entries){
  if($e.FullName -notmatch '^[a-zA-Z0-9_.-]+$' -or $e.FullName.Contains('..') -or $seen.ContainsKey($e.FullName)){throw 'Unsafe/duplicate entry'}
  $seen[$e.FullName]=$true
 }
 $entry=$z.GetEntry('manifest.json');if(!$entry){throw 'Missing manifest'}
 $reader=[IO.StreamReader]::new($entry.Open());try{$manifest=$reader.ReadToEnd()|ConvertFrom-Json -AsHashtable -DateKind String}finally{$reader.Dispose()}
 foreach($name in $manifest.Keys){
  $entry=$z.GetEntry($name);if(!$entry){throw "Missing $name"}
  $stream=$entry.Open();try{$hash=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($stream)).ToLowerInvariant()}finally{$stream.Dispose()}
  if($hash -ne $manifest[$name]){throw "Hash mismatch $name"}
 }
 [IO.Directory]::CreateDirectory($Destination)|Out-Null
 foreach($entry in $z.Entries){
  $stream=$entry.Open();$output=[IO.File]::Create((Join-Path $Destination $entry.FullName))
  try{$stream.CopyTo($output)}finally{$output.Dispose();$stream.Dispose()}
 }
 $r=[IO.File]::ReadAllText((Join-Path $Destination 'report.json'))|ConvertFrom-Json -AsHashtable -DateKind String
 $record=[ordered]@{status='RAW_MANIFEST_VALIDATED_ONLY';source_sha=$r.source_sha;reported_focal_status=$r.status;error=$r.error;manifest_entries=$manifest.Count;zip_sha256=(Get-FileHash -LiteralPath $Zip).Hash.ToLowerInvariant();local_Lean=$false}
 [IO.File]::WriteAllText((Join-Path $Destination 'integrity.json'),(($record|ConvertTo-Json -Depth 5)+"`n"),[Text.UTF8Encoding]::new($false))
 $record|ConvertTo-Json -Depth 5
} finally {$z.Dispose()}
