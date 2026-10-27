# Verification report

**The native build and all 20 standalone audits passed.** The final delivered
sources were rebuilt and the explicit theorem audit passed on 2026-10-27T13:46:20.3346214Z.

The checked theorem is:

```lean
KhanSL2.mainStatement : KhanSL2.MainStatement
```

Its exact type has no remaining mathematical premise. The axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or
additional mathematical axiom. The complete main audit traverses 20,655 safe
project declarations with the selected private proof bodies available. The
additional release audit checks `KhanSL2.mainStatement_explicit`.

| Check | Result | Evidence |
|---|---|---|
| Full native build and 20 standalone audits | Passed | [Native verification log](native-build.log) |
| Final sources after documentation cleanup, all default targets | Passed | [Final source build](final-source-build.log) |
| Explicit theorem interface and permitted axioms | Passed | [FinalAudit.lean](../lean/FinalAudit.lean) and final source log |
| Original mathematical definitions and proofs preserved | Passed | [Comment-only correction certificate](comment-only-edits.json), original source hashes and integrity scripts |
| Frozen specification ZIP and Comparator configuration | Validated | [Reference metadata](reference.json) |
| Export of the frozen main theorem and its dependencies | Passed | [Machine-readable results](results.json) |
| Optional native export replay | Inconclusive; no verdict within the 300-second trial | [Machine-readable results](results.json) |
| Sandboxed Comparator | Not run in this environment | Linux/WSL instructions in [README.md](README.md) |
| All bundled external kernels | Not run | Optional `--paranoid` workflow |

The proof library preserves all 1,046 reference Lean files' mathematical code.
Of those files, 1,043 are byte-identical and three have only a documented block
comment correction. Two new Lean files provide the explicit theorem interface
and its audit. The integrity scripts reverse only those certified comment edits
and recover the reference hashes exactly.

Native verification used ordinary Lake cache reuse. The source archive excludes
build caches and contains the pinned dependency configuration. The byte hashes
of the delivered checked sources are in [final-source-sha256.json](final-source-sha256.json).
The full standalone audit run completed at 2026-10-27T13:39:13.6463127Z; the comment corrections
were followed by the final default-target rebuild and explicit theorem audit.

Some audit output lists intermediate lemmas with premises. The final theorem
check above supplies those premises with proved results and has no remaining
mathematical hypotheses.

Successful compilation and axiom checking certify the precise Lean proposition.
The frozen comparison workflow checks agreement with the formal specification;
mathematical interpretation is documented in [the scope guide](../docs/SCOPE.md).
The optional independent checks are not represented as passed merely because
their scripts are provided.
