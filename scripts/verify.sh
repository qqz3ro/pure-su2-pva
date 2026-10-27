#!/usr/bin/env bash
set -euo pipefail
release_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
python3 "$release_dir/scripts/check-integrity.py"
cd "$release_dir/lean"
lake build
for audit in SourceAudit TargetAudit CanonicalAudit InjectivityAudit DictionaryAudit Audit BGGAudit BGGBridgeAudit DepthAudit ConditionalAudit DeformationAudit ModuleAudit IntegrationAudit ReviewChecks MergeCheck MacdonaldAudit StrongMacdonaldAudit CollisionAudit MainProofAudit FinalAudit; do
  lake env lean -DwarningAsError=true -Dlinter.unusedSimpArgs=false -Dlinter.deprecated=false "$audit.lean"
done
printf '%s\n' 'PASS: native build and all 20 standalone audits.'
