param([switch]$FetchCache, [switch]$TrustZero, [switch]$Serial)
$ErrorActionPreference = 'Stop'
& (Join-Path $PSScriptRoot 'scripts/check-integrity.ps1')
& (Join-Path $PSScriptRoot 'lean/verify.ps1') -FetchCache:$FetchCache -TrustZero:$TrustZero -Serial:$Serial
