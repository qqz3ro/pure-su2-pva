# Lean project for sl2-vfinal

Open this folder in VS Code, or open `../sl2-vfinal.code-workspace`.

Start at [Final.lean](Final.lean). The main theorem is
`KhanSL2.mainStatement : KhanSL2.MainStatement` in [MainProof.lean](MainProof.lean).

Current documentation is in [the release guide](../README.md) and
[the mathematical scope](../docs/SCOPE.md).

From this directory, `lake build FinalAudit` builds the proof and final audits.
From the release root, `./verify.ps1 -Serial` runs the full Windows verification.
