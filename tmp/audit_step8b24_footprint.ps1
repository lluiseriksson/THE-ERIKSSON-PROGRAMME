param(
  [string]$Repo = (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Pair([string]$name) {
  @(
    "tmp/$name.draft.lean"
    "tmp/${name}Audit.draft.lean"
  )
}

$preUnitE = @(
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary'
  'BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand'
  'BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction'
  'BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint'
) | ForEach-Object { Pair $_ }

$step8b23 = Get-Content -LiteralPath (Join-Path $Repo 'tmp/STEP8B23-ALL-PATHS.txt') |
  Where-Object { $_.Trim() -ne '' }
$independent = @(
  'tmp/BalabanCMP89CenteredBrillouinAffineSlice.draft.lean'
  'tmp/BalabanCMP89CenteredBrillouinAffineSliceAudit.draft.lean'
)
$sharedPrefix = $step8b23 | Where-Object { $_ -notin $independent }

$tailLists = @(
  'STEP8B24-C2-PATHS.txt'
  'STEP8B24-C3-PATHS.txt'
  'STEP8B24-C4A-PATHS.txt'
  'STEP8B24-C4B-PATHS.txt'
  'STEP8B24-C5-PATHS.txt'
  'STEP8B24-C6A-PATHS.txt'
  'STEP8B24-C6B-PATHS.txt'
)
$tail = $tailLists | ForEach-Object {
  Get-Content -LiteralPath (Join-Path $Repo "tmp/$_")
} | Where-Object { $_.Trim() -ne '' }

$dependency = @($preUnitE) + @($sharedPrefix) + @($tail)
$full = @($dependency) + @($independent)

if ($preUnitE.Count -ne 20) { throw "pre-Unit-E count $($preUnitE.Count), expected 20" }
if ($sharedPrefix.Count -ne 42) { throw "shared prefix count $($sharedPrefix.Count), expected 42" }
if ($tail.Count -ne 14) { throw "C2-C6b tail count $($tail.Count), expected 14" }
if ($dependency.Count -ne 76) { throw "dependency count $($dependency.Count), expected 76" }
if (($dependency | Sort-Object -Unique).Count -ne 76) { throw 'duplicate dependency path' }
if ($full.Count -ne 78) { throw "full schedule count $($full.Count), expected 78" }
if (($full | Sort-Object -Unique).Count -ne 78) { throw 'duplicate full-schedule path' }

$missing = @($full | Where-Object { -not (Test-Path -LiteralPath (Join-Path $Repo $_)) })
if ($missing.Count -ne 0) { throw "missing paths:`n$($missing -join "`n")" }

"STEP8B24_FOOTPRINT_STATIC_OK pre_unit_e=20 shared_prefix=42 tail=14 dependency=76 full=78 unique=78 missing=0"
