param([switch]$FetchCache, [switch]$TrustZero, [switch]$Serial)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
  if ($FetchCache) {
    & lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Dependency cache download failed.' }
  }
  if ($Serial) {
    & (Join-Path $PSScriptRoot 'build-serial.ps1')
  } else {
    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'Build failed.' }
  }
  $taskLeanArgs = @('-DwarningAsError=true', '-Dlinter.unusedSimpArgs=false', '-Dlinter.deprecated=false')
  if ($TrustZero) { $taskLeanArgs += '-t0' }
  foreach ($taskAudit in @('SourceAudit.lean', 'TargetAudit.lean', 'CanonicalAudit.lean',
      'InjectivityAudit.lean', 'DictionaryAudit.lean', 'Audit.lean', 'BGGAudit.lean',
      'BGGBridgeAudit.lean', 'DepthAudit.lean', 'ConditionalAudit.lean', 'DeformationAudit.lean', 'ModuleAudit.lean', 'IntegrationAudit.lean', 'ReviewChecks.lean',
      'MergeCheck.lean', 'MacdonaldAudit.lean', 'StrongMacdonaldAudit.lean', 'CollisionAudit.lean', 'MainProofAudit.lean', 'FinalAudit.lean')) {
    & lake env lean @taskLeanArgs $taskAudit
    if ($LASTEXITCODE -ne 0) { throw "Audit failed: $taskAudit" }
  }
  Write-Output 'PASS: all default library targets and standalone audits compiled. MainStatement is proved for the original specified phi, with no remaining mathematical hypotheses, no sorryAx, and no additional axioms.'
} finally {
  Pop-Location
}
