$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo='C:\Trabajo\the-eriksson-programme\perron-spec-210-20261108'
$old='1659b5397ffa30e5315b2b3963d9ed661ee5f611';$sha='4ec599da41521ecfdadd7d2aee69faab8b3819f1'
$prefix='papers/flat-coarse-rank/research-consolidation/revision250-preparation'
$base='D:\Datos\the-eriksson-programme\autonomia\evidencia-250'
$out=Join-Path $base 'source-audit-B';$zip=Join-Path $out 'source250B-raw-git.zip'
if(Test-Path -LiteralPath $zip){throw 'Preserve prior audit capture'}
git -C $repo -c gc.auto=0 archive --format=zip --output=$zip $sha -- $prefix
if($LASTEXITCODE -ne 0){throw 'Actual git archive failed'}
git -C $repo -c gc.auto=0 diff --output=(Join-Path $out 'A-to-B.diff') $old $sha -- $prefix
if($LASTEXITCODE -ne 0){throw 'Actual git diff failed'}
$capture=Join-Path $out 'capture';[IO.Compression.ZipFile]::ExtractToDirectory($zip,$capture)
$root=Join-Path $capture $prefix
$inventory=@(git -C $repo -c gc.auto=0 ls-tree -r --name-only $sha -- $prefix)
if($LASTEXITCODE -ne 0 -or $inventory.Count -ne 151){throw 'Expected151 frozen B files'}
$files=@(Get-ChildItem -LiteralPath $root -File -Recurse)
if($files.Count -ne 151){throw 'Captured B prefix not closed151'}
$manifest=@();$unchanged=0
$oldManifest=Get-Content -LiteralPath (Join-Path $base 'source-audit\capture-manifest.json') -Raw|ConvertFrom-Json
foreach($file in $files){
 $rel=[IO.Path]::GetRelativePath($root,$file.FullName).Replace('\','/')
 if($inventory -cnotcontains ($prefix+'/'+$rel)){throw 'Unlisted B file'}
 $local=Join-Path (Join-Path $repo $prefix) $rel
 $hash=(Get-FileHash -LiteralPath $file.FullName).Hash.ToLowerInvariant()
 if((Get-Item -LiteralPath $local).Length -ne $file.Length -or (Get-FileHash -LiteralPath $local).Hash.ToLowerInvariant() -cne $hash){throw ('Checkout differs '+$rel)}
 $prior=@($oldManifest.files|Where-Object{$_.path -ceq $rel})
 if($prior.Count -eq 1 -and $prior[0].sha256_raw_git_LF_or_original_binary -ceq $hash -and $prior[0].bytes -eq $file.Length){$unchanged++}
 $manifest+=@{path=$rel;bytes=$file.Length;sha256_raw=$hash}
}
if($unchanged -ne 148){throw 'Expected exactly148 byte-unchanged old files'}
$inputs=Get-Content -LiteralPath (Join-Path $root 'SOURCE-INPUTS.json') -Raw|ConvertFrom-Json
if($inputs.inputs.Count -ne 137){throw 'Unexpected binder count'}
foreach($input in $inputs.inputs){$p=Join-Path $root $input.path;if((Get-Item -LiteralPath $p).Length -ne $input.bytes -or (Get-FileHash -LiteralPath $p).Hash.ToLowerInvariant() -cne $input.sha256){throw ('Binder differs '+$input.path)}}
$attempt=Join-Path $base 'production-preparation\attempt-a'
$archive=Join-Path $attempt 'tep250A-production-results.zip'
if((Get-FileHash -LiteralPath $archive).Hash.ToLowerInvariant() -cne '48fcb78a9c865f55ac81d10c7ba9d8abf78797a463134cf67105d6c46790e3ac'){throw 'Actual A failure archive differs'}
$failure=Join-Path $out 'actual-A-failure';New-Item -ItemType Directory -Path $failure|Out-Null
$z=[IO.Compression.ZipFile]::OpenRead($archive)
try{
 foreach($entryName in @('evidence/report.json','evidence/failure.txt','build-state/first/finalpass/canonical_rectangles250.log','evidence/latex-first-firstpass.exit','evidence/latex-first-secondpass.exit','evidence/latex-first-finalpass.exit')){
  $entry=$z.GetEntry($entryName);if($null -eq $entry){throw ('Actual failure entry missing '+$entryName)}
  $target=Join-Path $failure $entryName;[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($target))|Out-Null
  [IO.Compression.ZipFileExtensions]::ExtractToFile($entry,$target,$false)
  if((Get-FileHash -LiteralPath $target).Hash -cne (Get-FileHash -LiteralPath (Join-Path (Join-Path $attempt 'returned') $entryName)).Hash){throw 'Returned failure bytes differ from ZIP'}
 }
}finally{$z.Dispose()}
foreach($name in @('backend-readback.log','backend-readback.stderr.log','backend-readback.exit','execution.exit')){Copy-Item -LiteralPath (Join-Path $attempt $name) -Destination (Join-Path $failure $name)}
@{source_A=$old;source_B=$sha;tracked_B_files=151;old_byte_unchanged_files=148;old_changed_files=@('context250.tex','fixed250.tex');added_file='PRODUCTION-CORRECTION250B.txt';binder_payloads_checked=137;files=$manifest;A_failure_archive_sha256='48fcb78a9c865f55ac81d10c7ba9d8abf78797a463134cf67105d6c46790e3ac';method='Read-only exact Git archive/diff; raw size/hash comparison; selected native failure entries extracted directly from the bound original ZIP; no normalization'}|ConvertTo-Json -Depth 8|Set-Content -LiteralPath (Join-Path $out 'capture-manifest.json') -Encoding utf8NoBOM
Write-Output 'B151files captured;148unchanged,2editorialchanges,1newcorrectionnote;137binder hashes unchanged; selected actual failure records bound.'
