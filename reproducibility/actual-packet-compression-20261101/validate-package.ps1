param([Parameter(Mandatory=$true)][string]$Zip,[Parameter(Mandatory=$true)][string]$Output,[string]$Source='9a8946b7f96a8528078c59650d94e636acc68887')
$ErrorActionPreference='Stop'
Add-Type -AssemblyName System.IO.Compression.FileSystem
$z=[IO.Compression.ZipFile]::OpenRead($Zip)
function ReadEntry([string]$name){$entry=$z.GetEntry($name);if($null -eq $entry){throw "Missing $name"};$reader=[IO.StreamReader]::new($entry.Open());try{$reader.ReadToEnd()}finally{$reader.Dispose()}}
try {
 $m=ReadEntry 'manifest.json'|ConvertFrom-Json -AsHashtable -DateKind String
 foreach($name in $m.Keys){$entry=$z.GetEntry($name);if($null -eq $entry){throw "Missing $name"};$stream=$entry.Open();try{$hash=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($stream)).ToLowerInvariant()}finally{$stream.Dispose()};if($hash -ne $m[$name]){throw "Manifest mismatch $name"}}
 $r=ReadEntry 'report.json'|ConvertFrom-Json
 if($r.status -ne 'FOCAL_REPRODUCTION_PASS' -or $r.source_sha -ne $Source){throw 'Wrong source or verdict'}
 if(@($r.steps|Where-Object exit_code -ne 0).Count -ne 0){throw 'Nonzero step'}
 foreach($name in @('git-init','git-remote','git-fetch','git-checkout','lean-version','cache-get','focal-build','oracle')){if(@($r.steps|Where-Object name -eq $name).Count -ne 1){throw "Wrong step count $name"}}
 $rawOracle=ReadEntry 'oracle.log'
 $pattern="'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
 $rawMatches=[regex]::Matches($rawOracle,$pattern)
 if($rawMatches.Count -ne 4){throw 'Raw oracle count mismatch'}
 $names=@('actualPacketSubspace_eq_range','actualPacketBasis_coe','actualPacket_compression_trace','actualPacket_weightedRepair_trace')
 if(@($r.oracle_reports).Count -ne 4){throw 'Wrong oracle count'}
 for($i=0;$i -lt 4;$i++){if($r.oracle_reports[$i].name -ne ('YangMills.RG.'+$names[$i])){throw 'Wrong exact oracle name'};if($rawMatches[$i].Groups[1].Value -ne ('YangMills.RG.'+$names[$i])){throw 'Wrong raw oracle name'};foreach($axraw in ($rawMatches[$i].Groups[2].Value -split ',')){if($axraw.Trim() -and $axraw.Trim() -notin @('propext','Classical.choice','Quot.sound')){throw 'Raw unapproved axiom'}};foreach($ax in $r.oracle_reports[$i].axioms){if($ax -notin @('propext','Classical.choice','Quot.sound')){throw "Unapproved axiom $ax"}}}
 if(@($r.oracle_validator_selftests).Count -ne 2){throw 'Missing validator modes'}
 foreach($mode in @('normal','optimized')){$t=@($r.oracle_validator_selftests|Where-Object mode -eq $mode);if($t.Count -ne 1 -or $t[0].real_mutations_rejected -ne 3 -or $t[0].positive_accepted -ne 1){throw "Mutation checks missing $mode"}}
 if($r.target_olean_sha256 -notmatch '^[a-f0-9]{64}$'){throw 'Missing compiled object hash'}
 [ordered]@{status='ACTUAL_PACKET_COMPRESSION_VALIDATED';source_sha=$r.source_sha;zip_sha256=(Get-FileHash -LiteralPath $Zip).Hash.ToLowerInvariant();manifest_entries=$m.Count;exit_zero_steps=@($r.steps).Count;oracle_reports=4;target_olean_sha256=$r.target_olean_sha256;oracle_log_sha256=$m['oracle.log'];source_manifest_sha256=$m['source-hashes.json'];started_utc=([datetimeoffset]$r.started_utc).ToUniversalTime().ToString("o");finished_utc=([datetimeoffset]$r.finished_utc).ToUniversalTime().ToString("o");independent_review=$false;scope='Actual packet image orthonormal basis, true compression trace, and weighted repair trace; Hodge/local-kernel/support-positivity composition still open';windows_lean_executed=$false}|ConvertTo-Json -Depth 8|Set-Content -LiteralPath $Output -Encoding utf8
} finally {$z.Dispose()}
