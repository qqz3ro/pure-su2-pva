#!/usr/bin/env python3
"""Compare the current theorem with the frozen formal specification.

The trusted challenge contains an actual proof, not a placeholder. The
baseline is exported in its own project. Use Linux for sandboxed comparison;
--prepare-only also works on Windows and does not claim a comparison.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import zipfile

# Exact primitive roots from the pinned Lean 4.36.0-rc1 Lake/CLI/Check.lean.
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
    "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List",
    "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam",
    "autoParam", "semiOutParam", "outParam",
]
QUOTIENT_ROOTS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run(args: list[str], cwd: Path, log: Path) -> None:
    print(f"Running in {cwd}: {' '.join(args)}", flush=True)
    with log.open("ab") as record:
        record.write(("\nCOMMAND " + repr(args) + "\n").encode("utf-8"))
        record.flush()
        completed = subprocess.run(args, cwd=cwd, stdout=record, stderr=record)
    if completed.returncode:
        raise RuntimeError(f"Command exited {completed.returncode}; see {log}")


def archive_files(archive: Path, expected_root: str) -> dict[str, bytes]:
    """Read the frozen source archive, rejecting ambiguous paths."""
    files: dict[str, bytes] = {}
    with zipfile.ZipFile(archive) as bundle:
        for entry in bundle.infolist():
            if entry.is_dir():
                continue
            name = PurePosixPath(entry.filename)
            if (
                name.is_absolute()
                or ".." in name.parts
                or "\\" in entry.filename
                or len(name.parts) < 2
                or name.parts[0] != expected_root
                or ((entry.external_attr >> 16) & 0o170000) == 0o120000
            ):
                raise RuntimeError(f"Unexpected archive path: {entry.filename}")
            relative = PurePosixPath(*name.parts[1:]).as_posix()
            if relative in files:
                raise RuntimeError(f"Duplicate archive path: {relative}")
            files[relative] = bundle.read(entry)
    return files


def prepare_reference(files: dict[str, bytes], destination: Path, *, existing: bool) -> None:
    """Create a reference checkout, or validate one without overwriting it."""
    destination = destination.resolve()
    if not existing:
        destination.mkdir(parents=True, exist_ok=True)
    for relative, content in files.items():
        target = destination.joinpath(*PurePosixPath(relative).parts)
        if not target.resolve().is_relative_to(destination):
            raise RuntimeError(f"Reference path escapes destination: {relative}")
        if target.exists():
            if target.read_bytes() != content:
                raise RuntimeError(f"Reference file differs from frozen release: {target}")
        elif existing:
            raise RuntimeError(f"Frozen reference file is missing: {target}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release-root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="vfinal folder containing lean/ and verification/")
    parser.add_argument("--baseline-project", type=Path,
                        help="Reuse a source baseline after checking every archived file")
    parser.add_argument("--prepare-only", action="store_true",
                        help="Build/export the frozen challenge only; do not run Comparator")
    parser.add_argument("--validate-only", action="store_true",
                        help="Check archive, configuration and toolchain without building or extracting")
    parser.add_argument("--paranoid", action="store_true",
                        help="Require all bundled external checkers during Linux comparison")
    args = parser.parse_args()
    root = args.release_root.resolve()
    project = root / "lean"
    spec = root / "verification"
    reference = json.loads((spec / "reference.json").read_text(encoding="utf-8-sig"))
    config_path = spec / "comparator.json"
    config = json.loads(config_path.read_text(encoding="utf-8-sig"))
    archive = spec / reference["archive"]
    if sha256(archive) != reference["archive_sha256"]:
        raise RuntimeError("The frozen reference archive's SHA256 does not match")
    if config["theorem_names"] != [reference["theorem"]]:
        raise RuntimeError("Comparator targets do not match the frozen theorem")
    if config.get("definition_names", []) != []:
        raise RuntimeError("The frozen specification permits no definition holes")
    if set(config["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
        raise RuntimeError("Unexpected permitted axiom list")
    if config["challenge_module"] != "FrozenSpecification":
        raise RuntimeError("Unexpected frozen challenge module")
    if config["solution_module"] != "MainProofAudit":
        raise RuntimeError("Unexpected solution module")
    toolchain = (project / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if toolchain != reference["lean_toolchain"]:
        raise RuntimeError("Comparator primitive roots require the pinned Lean toolchain")
    files = archive_files(archive, reference["archive_root"])
    if files["lean-toolchain"].decode("utf-8-sig").strip() != toolchain:
        raise RuntimeError("Reference and current Lean toolchains differ")
    print(f"PASS: frozen reference SHA256, {len(files)} files and configuration validated.")
    if args.validate_only:
        return
    if not args.prepare_only and not sys.platform.startswith("linux"):
        raise RuntimeError("Sandboxed Comparator requires Linux (for example WSL). "
                           "Use --prepare-only on Windows to export without claiming comparison.")
    work = root / ".verification"
    work.mkdir(exist_ok=True)
    baseline = (args.baseline_project.resolve() if args.baseline_project else
                work / "frozen-specification" / reference["archive_root"])
    if baseline == project.resolve():
        raise RuntimeError("The trusted baseline and current project must be separate")
    prepare_reference(files, baseline, existing=args.baseline_project is not None)
    log = work / "comparator.log"
    log.write_text("Frozen-reference verification started.\n", encoding="utf-8")
    run(["lake", "build", reference["module"]], baseline, log)
    challenge = work / "frozen-specification.ndjson"
    temporary = work / "frozen-specification.ndjson.tmp"
    export_roots = [reference["theorem"]] + config["permitted_axioms"] + QUOTIENT_ROOTS + PRIMITIVES
    export_args = ["lake", "env", "leanexport", reference["module"], "--"] + export_roots
    print("Exporting the frozen reference theorem and its dependencies...", flush=True)
    with temporary.open("wb") as output, log.open("ab") as record:
        completed = subprocess.run(export_args, cwd=baseline, stdout=output, stderr=record)
    if completed.returncode:
        raise RuntimeError(f"Baseline export failed; see {log}")
    if temporary.stat().st_size == 0:
        raise RuntimeError("Baseline export is empty")
    os.replace(temporary, challenge)
    export_record = {"baseline_archive_sha256": reference["archive_sha256"],
                     "export_sha256": sha256(challenge), "export_bytes": challenge.stat().st_size,
                     "export_roots": export_roots, "comparison_run": False}
    report = work / "comparator-result.json"
    report.write_text(json.dumps(export_record, indent=2) + "\n", encoding="utf-8")
    if args.prepare_only:
        print(f"PREPARED ONLY: {challenge}\nComparator has NOT been run.")
        return
    command = ["lake", "comparator", "--config", str(config_path),
               "--challenge-from-export", str(challenge)]
    if args.paranoid:
        command.append("--paranoid")
    run(command, project, log)
    export_record.update(comparison_run=True, comparison_passed=True, paranoid=args.paranoid)
    report.write_text(json.dumps(export_record, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: theorem matches the frozen specification and passed Comparator; see {log}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, KeyError, ValueError, zipfile.BadZipFile) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
