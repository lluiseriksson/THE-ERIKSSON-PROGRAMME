# Operational capture only. No Python/tests, credentials read, or allocation here.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
function Write-AtomicExit {
 param([string]$Path,[int]$ActualCode)
 if((Test-Path -LiteralPath $Path) -or (Test-Path -LiteralPath ($Path+'.tmp'))){throw 'Preserve existing sentinel evidence'}
 $temporary=$Path+'.tmp'
 $bytes=[Text.Encoding]::ASCII.GetBytes(([string]$ActualCode)+"`n")
 $stream=[IO.FileStream]::new($temporary,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None)
 try{$stream.Write($bytes,0,$bytes.Length);$stream.Flush($true)}finally{$stream.Dispose()}
 # Flush(true) requests durable OS flushing; stream CLOSED before parse/rename.
 $raw=[IO.File]::ReadAllText($temporary,[Text.Encoding]::ASCII)
 if(-not[regex]::IsMatch($raw,'\A-?[0-9]+\n\z')){throw 'Nonempty exact decimal line required'}
 $parsed=[int]::Parse($raw.Trim(),[Globalization.CultureInfo]::InvariantCulture)
 if($parsed -ne $ActualCode){throw 'Sentinel differs from actual child exit'}
 [IO.File]::Move($temporary,$Path) # Same-directory atomic rename; no overwrite.
 if([IO.File]::ReadAllText($Path,[Text.Encoding]::ASCII) -cne $raw){throw 'Exit sentinel readback differs'}
 return $parsed
}
function Invoke-CapturedWsl {
 param([string]$Name,[string]$ShellCommand,[string]$OutputDirectory)
 if(-not[regex]::IsMatch($Name,'\A[a-z0-9-]+\z')){throw 'Semantic child mode name required'}
 $info=[Diagnostics.ProcessStartInfo]::new('wsl.exe')
 $info.UseShellExecute=$false;$info.CreateNoWindow=$true
 $info.RedirectStandardOutput=$true;$info.RedirectStandardError=$true
 foreach($argument in @('bash','-lc',$ShellCommand)){$info.ArgumentList.Add($argument)}
 $stdout=[IO.FileStream]::new((Join-Path $OutputDirectory ($Name+'.log')),[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::Read)
 $stderr=[IO.FileStream]::new((Join-Path $OutputDirectory ($Name+'.stderr.log')),[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::Read)
 $child=[Diagnostics.Process]::new();$child.StartInfo=$info
 try{
  if(-not$child.Start()){throw 'Could not start exact own operational child'}
  $copyOut=$child.StandardOutput.BaseStream.CopyToAsync($stdout)
  $copyErr=$child.StandardError.BaseStream.CopyToAsync($stderr)
  $child.WaitForExit()
  [Threading.Tasks.Task]::WaitAll([Threading.Tasks.Task[]]@($copyOut,$copyErr))
  $actual=[int]$child.ExitCode
  $stdout.Flush($true);$stderr.Flush($true)
 }finally{$stdout.Dispose();$stderr.Dispose();$child.Dispose()}
 return (Write-AtomicExit -Path (Join-Path $OutputDirectory ($Name+'.exit')) -ActualCode $actual)
}
