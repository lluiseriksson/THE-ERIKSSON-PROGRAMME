$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo='C:\Trabajo\the-eriksson-programme\perron-spec-210-20261108'
$sha='1659b5397ffa30e5315b2b3963d9ed661ee5f611'
$prefix='papers/flat-coarse-rank/research-consolidation/revision250-preparation'
$out='D:\Datos\the-eriksson-programme\autonomia\evidencia-250\source-audit'
$zip=Join-Path $out 'source250-raw-git.zip'
if(Test-Path -LiteralPath $zip){throw 'Preserve existing raw capture'}
git -C $repo -c gc.auto=0 archive --format=zip --output=$zip $sha -- $prefix
if($LASTEXITCODE -ne 0){throw 'Actual git archive failed'}
$capture=Join-Path $out 'capture'
[IO.Compression.ZipFile]::ExtractToDirectory($zip,$capture)
$root=Join-Path $capture $prefix
$inventory=@(git -C $repo -c gc.auto=0 ls-tree -r --name-only $sha -- $prefix)
if($LASTEXITCODE -ne 0 -or $inventory.Count -ne 150){throw 'Expected exact150-file frozen source prefix'}
$files=@(Get-ChildItem -LiteralPath $root -File -Recurse)
if($files.Count -ne 150){throw 'Captured prefix not closed150'}
$manifest=@()
foreach($file in $files){
 $rel=[IO.Path]::GetRelativePath($root,$file.FullName).Replace('\','/')
 if($inventory -cnotcontains ($prefix+'/'+$rel)){throw 'Unlisted captured file'}
 $local=Join-Path (Join-Path $repo $prefix) $rel
 $hash=(Get-FileHash -Algorithm SHA256 -LiteralPath $file.FullName).Hash.ToLowerInvariant()
 if((Get-Item -LiteralPath $local).Length -ne $file.Length -or (Get-FileHash -Algorithm SHA256 -LiteralPath $local).Hash.ToLowerInvariant() -cne $hash){throw ('Working bytes differ from frozen raw Git '+$rel)}
 $manifest+=@{path=$rel;bytes=$file.Length;sha256_raw_git_LF_or_original_binary=$hash}
}
$inputs=Get-Content -LiteralPath (Join-Path $root 'SOURCE-INPUTS.json') -Raw|ConvertFrom-Json
if($inputs.inputs.Count -ne 137){throw 'Unexpected binder input count'}
foreach($input in $inputs.inputs){
 $p=Join-Path $root $input.path
 if((Get-Item -LiteralPath $p).Length -ne $input.bytes -or (Get-FileHash -Algorithm SHA256 -LiteralPath $p).Hash.ToLowerInvariant() -cne $input.sha256){throw ('Raw binder input differs '+$input.path)}
}
$record=@{source_commit=$sha;prefix=$prefix;capture_method='git archive exact commit, ZIP binary extraction, each150 raw captured file compared to checkout without normalization;137binder payload hashes checked';tracked_file_count=150;binder_input_count=137;files=$manifest;scientific_execution=$false;compile=$false}
$record|ConvertTo-Json -Depth 8|Set-Content -LiteralPath (Join-Path $out 'capture-manifest.json') -Encoding utf8NoBOM
Write-Output '150 frozen raw Git files captured and compared;137declared binder payloads match. Hash/data operations only.'
