param([string[]]$Targets = @('KhanSL2', 'SourceAudit', 'TargetAudit',
  'CanonicalAudit', 'InjectivityAudit', 'DictionaryAudit', 'Audit', 'BGG', 'BGGAudit',
  'BGGBridge', 'BGGBridgeAudit', 'ModuleAudit', 'Depth', 'DepthAudit', 'Conditional', 'ConditionalAudit', 'Deformation', 'DeformationAudit', 'MergeCheck',
  'KhanSL2All', 'IntegrationAudit', 'ReviewChecks', 'Macdonald', 'MacdonaldAudit', 'StrongMacdonald', 'StrongMacdonaldAudit', 'Collision', 'CollisionAudit', 'MainProof', 'MainProofAudit', 'Final', 'FinalAudit'))

# Build project and selected Tau Ceti modules in import order. Fetch the
# pinned mathlib cache first; this script uses ordinary Lake builds and
# never manufactures or modifies build traces.
$ErrorActionPreference = 'Stop'
$taskProject = $PSScriptRoot
$taskSeen = [Collections.Generic.HashSet[string]]::new()
$taskOrder = [Collections.Generic.List[string]]::new()

function Add-TaskBuildModule([string]$TaskModule) {
  if (-not $taskSeen.Add($TaskModule)) { return }
  $taskModuleRoot = if ($TaskModule.StartsWith('TauCeti.')) {
    Join-Path $taskProject '.lake/packages/TauCeti'
  } else { $taskProject }
  $taskSource = Join-Path $taskModuleRoot ($TaskModule.Replace('.', '/') + '.lean')
  if (-not (Test-Path -LiteralPath $taskSource)) {
    throw "Missing module $TaskModule. Run lake update and fetch the dependency cache first."
  }
  foreach ($taskMatch in [regex]::Matches([IO.File]::ReadAllText($taskSource),
      '(?m)^(?:public )?import (?:all )?([\w.]+)')) {
    $taskImport = $taskMatch.Groups[1].Value
    if ($taskImport -in @('KhanSL2', 'BGG', 'BGGBridge', 'Depth', 'DepthAudit', 'Conditional', 'ConditionalAudit', 'ModuleAudit', 'MergeCheck', 'KhanSL2All', 'ReviewChecks', 'Macdonald', 'StrongMacdonald', 'Collision', 'MainProof', 'MainProofAudit', 'Final', 'FinalAudit') -or $taskImport.StartsWith('KhanSL2.') -or
        $taskImport.StartsWith('TauCeti.')) {
      Add-TaskBuildModule $taskImport
    }
  }
  $taskOrder.Add($TaskModule)
}

foreach ($taskTarget in $Targets) { Add-TaskBuildModule $taskTarget }
$taskPreviousThreads = $env:LEAN_NUM_THREADS
Push-Location -LiteralPath $taskProject
try {
  $env:LEAN_NUM_THREADS = '2'
  $taskSpecs = @($taskOrder | ForEach-Object { "+$_" })
  # Lake has builtin initializers and native symbols that plain `lean --run`
  # does not initialize. Load the matching toolchain's Lake shared plugin.
  $taskLeanPrefix = (& lean --print-prefix | Out-String).Trim()
  if ($LASTEXITCODE -ne 0) { throw 'Cannot locate the pinned Lean toolchain.' }
  $taskLakePlugin = @('bin/libLake_shared.dll',
    'lib/lean/libLake_shared.so', 'lib/lean/libLake_shared.dylib') |
    ForEach-Object { Join-Path $taskLeanPrefix $_ } |
    Where-Object { Test-Path -LiteralPath $_ } |
    Select-Object -First 1
  if (-not $taskLakePlugin) { throw 'Cannot locate the Lake shared library.' }
  # The complete proof closure exceeds Windows' command-line length limit.
  # Pass target names through a UTF-8 data file, retaining normal Lake jobs.
  $taskSpecsPath = Join-Path $taskProject '.lake/serial-build-targets.txt'
  [IO.File]::WriteAllLines($taskSpecsPath, $taskSpecs, [Text.UTF8Encoding]::new($false))
  & lake env lean "--plugin=$taskLakePlugin" --run BuildSerial.lean --targets-file $taskSpecsPath
  if ($LASTEXITCODE -ne 0) { throw 'Sequential Lake build failed.' }
  & lake --no-cache build
  if ($LASTEXITCODE -ne 0) { throw 'Final Lake build failed.' }
} finally {
  $env:LEAN_NUM_THREADS = $taskPreviousThreads
  Pop-Location
}
