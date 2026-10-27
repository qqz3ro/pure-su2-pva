# Frozen specification

`reference.zip` contains the Lean sources and pinned build configuration used
as the trusted formal specification. Source bytes are unchanged from the
verified proof; the archive contains no historical documents, plans or logs.
Its SHA256 and provenance are recorded in `reference.json`.

The challenge contains an actual proof of `KhanSL2.mainStatement`. It introduces
no unfinished proofs or additional axioms. Comparator checks the current
unconditional theorem against that separately exported environment, including
the definitions on which its statement depends. No definition holes are allowed.
The permitted axioms are `propext`, `Quot.sound` and `Classical.choice`.

From the release root, validate the archive and configuration with Python 3.9+:

```text
python scripts/compare_reference.py --validate-only
```

For sandboxed comparison, use Linux or WSL with the pinned Lean toolchain and
`bubblewrap`:

```text
python scripts/compare_reference.py
```

Add `--paranoid` to require every bundled external checker. The harness builds
the separate reference project, exports its theorem, and invokes `lake comparator`
on `lean/`. It writes logs and exports to `.verification/`; the focused export
is approximately 1 GB. `--baseline-project PATH` reuses an existing source
baseline only after verifying every archived file. On Windows, `--prepare-only`
exports the reference but does not perform or claim a comparison.

`FrozenSpecification` is deliberately not a local Lean module. The harness
supplies it through `--challenge-from-export`; using the JSON alone fails
instead of comparing the current project with itself.

This verifies preservation of the **formal statement**. Its correspondence to
the paper's intended mathematics still depends on reviewing the definitions
and scope. The release verification report distinguishes checks actually run
from the additional verification commands supplied here.


## Native build and audit

The normal release check is `./verify.ps1 -Serial` from the release root on
PowerShell, or `bash scripts/verify.sh` on Linux/macOS. It verifies preservation
of the original sources, builds all default library targets, and runs 20
standalone audits. In `lean/`, `lake build FinalAudit` is the shorter final
entry-point check. See [STATUS.md](STATUS.md) for the recorded outcome.

## Optional export and kernel checks

From `lean/` on Linux with the pinned toolchain and `bubblewrap`, `lake check`
checks the default targets by export and replay; `lake check --paranoid` also
requires all bundled external checkers. This is separate from the frozen
statement comparison above. These commands are substantially heavier than
opening the theorem in VS Code.

The [verification report](STATUS.md) distinguishes completed checks from optional
ones. An optional native Windows replay trial reached its time limit without a
verdict. It does not count as a completed independent check.

Tool references: [Lean 4.35 verification tools](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
and [Comparator design](https://github.com/leanprover/comparator). The old
standalone Comparator package is superseded by the pinned toolchain's built-in
command. The additional independent checks have not been represented as passed
merely because their configuration is present.

## Source preservation

`original-lean-sha256.json` identifies the reference source bytes.
`comment-only-edits.json` records three documentation corrections, each confined
to one balanced Lean block comment. The integrity scripts reverse those exact
comment edits and check the reference hashes, so all bytes outside the comments
remain unchanged. `final-source-sha256.json` records the actual delivered sources
and build configuration after their final native check.
