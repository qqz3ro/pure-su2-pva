$ErrorActionPreference = 'Stop'
$taskRelease = Split-Path -Parent $PSScriptRoot
$taskUtf8 = [Text.UTF8Encoding]::new($false)
$taskManifest = Get-Content -LiteralPath (Join-Path $taskRelease 'verification/original-lean-sha256.json') -Raw -Encoding utf8 | ConvertFrom-Json
$taskCertificatePath = Join-Path $taskRelease 'verification/comment-only-edits.json'
$taskEdits = $null
if (Test-Path -LiteralPath $taskCertificatePath) {
  $taskEdits = (Get-Content -LiteralPath $taskCertificatePath -Raw -Encoding utf8 | ConvertFrom-Json).edits
}
function Test-TaskBlockComment([string]$Text) {
  if (-not $Text.StartsWith('/-') -or -not $Text.EndsWith('-/')) { return $false }
  $taskDepth = 0
  $taskI = 0
  while ($taskI -lt $Text.Length) {
    $taskPair = if ($taskI + 1 -lt $Text.Length) { $Text.Substring($taskI,2) } else { '' }
    if ($taskPair -eq '/-') { $taskDepth++; $taskI += 2 }
    elseif ($taskPair -eq '-/') {
      $taskDepth--; $taskI += 2
      if ($taskDepth -lt 0 -or ($taskDepth -eq 0 -and $taskI -ne $Text.Length)) { return $false }
    } else { $taskI++ }
  }
  return ($taskDepth -eq 0)
}
foreach ($taskEntry in $taskManifest.PSObject.Properties) {
  $taskPath = Join-Path (Join-Path $taskRelease 'lean') $taskEntry.Name
  $taskHash = (Get-FileHash -LiteralPath $taskPath -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($taskHash -eq $taskEntry.Value) { continue }
  $taskProperty = if ($null -ne $taskEdits) { $taskEdits.PSObject.Properties[$taskEntry.Name] } else { $null }
  if ($null -eq $taskProperty) { throw "Original Lean source changed: $($taskEntry.Name)" }
  $taskEdit = $taskProperty.Value
  if ($taskEdit.original_sha256 -ne $taskEntry.Value -or $taskEdit.current_sha256 -ne $taskHash) { throw 'Comment-edit file hashes do not match.' }
  if (-not (Test-TaskBlockComment $taskEdit.before) -or -not (Test-TaskBlockComment $taskEdit.after)) { throw 'Edit is not confined to one block comment.' }
  $taskText = [IO.File]::ReadAllText($taskPath, $taskUtf8)
  $taskIndex = $taskText.IndexOf($taskEdit.after, [StringComparison]::Ordinal)
  if ($taskIndex -lt 0 -or $taskIndex -ne $taskText.LastIndexOf($taskEdit.after, [StringComparison]::Ordinal)) { throw 'Comment location is ambiguous.' }
  $taskOriginal = $taskText.Replace($taskEdit.after, $taskEdit.before)
  $taskSha = [Security.Cryptography.SHA256]::Create()
  try { $taskRestoredHash = ([BitConverter]::ToString($taskSha.ComputeHash($taskUtf8.GetBytes($taskOriginal)))).Replace('-','').ToLowerInvariant() }
  finally { $taskSha.Dispose() }
  if ($taskRestoredHash -ne $taskEntry.Value) { throw 'Code outside the documented comment changed.' }
}
$taskBaseline = Join-Path $taskRelease 'verification/reference.zip'
if ((Get-FileHash -LiteralPath $taskBaseline -Algorithm SHA256).Hash.ToLowerInvariant() -ne '3dfcdee24cbebfdbb9e5496295a797a52d7c4718e020808b8e0f36389b5a1fc1') {
  throw 'Frozen reference archive differs from the trusted specification.'
}
Write-Output 'PASS: original Lean sources preserved, allowing only documented comment corrections; frozen specification matches.'
