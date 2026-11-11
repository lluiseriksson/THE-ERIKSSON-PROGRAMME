$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$base='D:\Datos\the-eriksson-programme\autonomia'
$out=Join-Path $base 'evidencia-252\source-audit'
$capture=Join-Path $out 'capture'
if(Test-Path -LiteralPath $capture){throw 'Preserve earlier audit capture'}
New-Item -ItemType Directory -Path $capture|Out-Null
$specs=@(
 @('source252A.txt','evidencia-252\coexact-layer-band252A.txt','d55daa2a3af56039a4e29ada2f7200acf7127d733d640df13c1941ad7c56a677'),
 @('source246.txt','evidencia-250\source-preparation\raw-tree\inputs\accepted\source246.txt','ab9ab2195affe3482674538f4553c8c25e6655cfbcc74db68da7ef6d275c8842'),
 @('source249A.txt','evidencia-249\fixed-angle-point249A-candidate.txt','207964b440b7c91bc535739cc323f1fc135be4aac697ad665efb0ea4b7fb5a24'),
 @('report251.txt','evidencia-251\source-audit\fullreport.txt',''),
 @('verdict249.json','evidencia-249\source-audit\verdict.json',''),
 @('verdict251.json','evidencia-251\source-audit\verdict.json',''),
 @('setup250-prior.tex','evidencia-250\source-preparation\raw-tree\setup250.tex','44a04cb5ff4b2a212995a0801b358f05c78cd28136420a067267769362c6b703'),
 @('finite250-prior.tex','evidencia-250\source-preparation\raw-tree\finite250.tex','6ef355ed73177a2845fe468e68eec85184c4d39047448de18d0e268020c6a33f')
)
$records=@()
foreach($spec in $specs){
 $origin=Join-Path $base $spec[1];$target=Join-Path $capture $spec[0]
 $before=(Get-FileHash -LiteralPath $origin).Hash.ToLowerInvariant()
 if($spec[2] -ne '' -and $before -cne $spec[2]){throw ('Frozen input differs '+$origin)}
 Copy-Item -LiteralPath $origin -Destination $target
 $after=(Get-FileHash -LiteralPath $target).Hash.ToLowerInvariant()
 if($after -cne $before -or (Get-Item -LiteralPath $origin).Length -ne (Get-Item -LiteralPath $target).Length){throw 'Raw copy differs'}
 $records+=@{path=('capture/'+$spec[0]);origin=$origin;bytes=(Get-Item -LiteralPath $target).Length;sha256_raw=$after;representation='Original bytes, no normalization'}
}
@{candidate_sha256_raw='d55daa2a3af56039a4e29ada2f7200acf7127d733d640df13c1941ad7c56a677';files=$records;count=$records.Count;method='Read-only local raw copies and SHA256/size comparisons; no Git/UI/network/WSL/scientific execution'}|ConvertTo-Json -Depth 7|Set-Content -LiteralPath (Join-Path $out 'capture-manifest.json') -Encoding utf8NoBOM
Write-Output '8 exact raw input captures copied and hashed; candidate252A matches supplied frozen SHA. Data operations only.'
