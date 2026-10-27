#!/usr/bin/env python3
"""Check production root generation, export association and fixed-request preservation.

Uses a private Lean overlay, the existing export readers, and kernel equations.
No Lake build or protocol evaluation is performed. --exports contains one
catalogue-named directory per root with source.json, producer.json, validator.json,
producer.identity, validator.identity, original.mlir, interface.json,
source-claims.json and deployment.json. Participants use the current strict
schema. Identity files are hashed without interpreting them; reissuing a source
request additionally requires validator.identity to be the current participant
bytes. The common request renderer transfers data and Lean resolves its meaning.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path
import sys

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
sys.path.insert(0, str(LEAN))
from bridges.construction import pair  # noqa: E402
from bridges.pipeline import evidence, source_claims  # noqa: E402
from bridges.structured import snapshot  # noqa: E402
from bridges.structured.generate_component_roots import Generation  # noqa: E402
from support.lean_headers import HeaderParser  # noqa: E402


def export_metadata(rows: list[tuple[str, str, str, str]]) -> str:
    entries = ",\n".join("  (" + ", ".join(map(json.dumps, row)) + ")" for row in rows)
    return '''module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
''' + entries + ''']

end ZkcSecurity.Generation.Roots
'''


def freeze_dependencies(generation: Generation) -> None:
    """Copy this check's local import closure so concurrent cache writers cannot
    unlink a dependency between two commands. External package caches are reused.
    Only symlinked artifacts in our private overlay are replaced.
    """
    pending = ["ZkcSecurity.Generation.Roots.Stages", "ZkcSecurity.Generation.Roots.Subjects",
               "TestsSecurity.GenerateRootControls", "ZkcSecurity.Claims.CanonicalAuthorityPair"]
    seen = set()
    # Lean owns the grammar, including `public meta import` and `import all`.
    # Missing one of those dependencies could leave a supposedly frozen closure
    # pointing at another process's mutable cache.
    with HeaderParser(lean=generation.lean, root=LEAN) as headers:
        for module in pending:
            if module in seen:
                continue
            source = generation.module_path(module)
            if not source.is_file():
                continue
            seen.add(module)
            pending.extend(headers.imports(source.read_text(), source))
            for suffix in [".olean", ".olean.private", ".olean.server", ".ir"]:
                cached = generation.output.joinpath(*module.split(".")).with_suffix(suffix)
                if cached.is_symlink():
                    temporary = cached.with_name(cached.name + ".snapshot")
                    shutil.copyfile(cached, temporary)
                    os.replace(temporary, cached)


def source_request_module(subject_module: str, directory: Path) -> tuple[str, str]:
    """Print the actual compiled-stage source requests through the common renderer.

    Stage selection chooses this root's interface, not a property or theorem.
    Lean still resolves each request and checks its exact meaning and method.
    """
    interface_text = (directory / "interface.json").read_text()
    interface = json.loads(interface_text)
    report = source_claims.decode((directory / "source-claims.json").read_text())
    deployment = json.loads((directory / "deployment.json").read_text())
    participant = (directory / "validator.json").read_text()
    if participant.encode() != (directory / "validator.identity").read_bytes():
        raise ValueError("source request reissue requires the actual participant identity bytes")
    bound = source_claims.bind_export(report["source_claims"], entry=interface["entry"],
        source=(directory / "original.mlir").read_bytes(), interface_text=interface_text,
        original_text=(directory / "source.json").read_text(),
        participant_text=participant, program=deployment[4].encode())
    bound["claims"] = [claim for claim in bound["claims"]
                       if claim["request"]["subject"]["stage"] == "compiled-ideal"]
    if not bound["claims"]:
        raise ValueError("no compiled-stage source requests for the selected root")
    module = subject_module + "SoundnessClaims"
    registration = subject_module + "SoundnessRegistration"
    header = evidence.HEADER.format(
        imports=f"public import {registration}\npublic meta import {registration}",
        doc="Generated exact source requests. Regenerate with "
            "`lean/checks/check_subject_roots.py --exports DIRECTORY --write`. "
            "The common data renderer emits no property or proof wrapper.")
    return module, header + evidence.request_commands(module, bound, registration + ".library")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exports", type=Path, required=True)
    parser.add_argument("--records", type=Path, default=ROOT / "build/lean/subject-roots")
    parser.add_argument("--dependency-path", type=Path, action="append", default=[])
    parser.add_argument("--write", action="store_true", help="retain the regenerated subjects and aliases")
    options = parser.parse_args()
    if not options.exports.is_dir():
        raise ValueError(f"missing root exports directory: {options.exports}")
    # Reuse the maintained overlay/compiler driver, with no shared-output writes.
    options.output, options.check = options.records, not options.write
    generation = Generation(options)
    freeze_dependencies(generation)
    for module in ["ZkcTools.StructuredSource.Root", "ZkcSecurity.Generation.Roots.Catalogue",
                   "ZkcSecurity.Generation.Roots.ExportMetadata"]:
        generation.compile(module)
    manifest = json.loads(generation.printer("RootManifest", '''import ZkcSecurity.Generation.Roots.Catalogue

def main : IO Unit := IO.println ZkcSecurity.Generation.Roots.catalogueManifest
'''))
    retained_rows = json.loads(generation.printer("RetainedRootExports", '''import Lean
import ZkcSecurity.Generation.Roots.ExportMetadata

def main : IO Unit := IO.println (Lean.Json.arr
  (ZkcSecurity.Generation.Roots.exportDigests.map fun (name, original, producer, validator) =>
    Lean.toJson [name, original, producer, validator]).toArray).compress
'''))
    retained = {row[0]: row[1:] for row in retained_rows}
    (generation.directory / "catalogue.json").write_text(json.dumps(manifest, indent=2) + "\n")
    metadata = []
    for row in manifest:
        name = row["name"]
        directory = options.exports / name
        for filename in ["source.json", "producer.json", "validator.json", "producer.identity", "validator.identity"]:
            if not (directory / filename).is_file():
                raise ValueError(f"missing root export: {directory / filename}")
        source_bytes = (directory / "source.json").read_bytes()
        source = json.loads(source_bytes)
        # These are the production strict readers; their existing refusals stand.
        source_module = "RootSourceExport" + name
        source_text = snapshot.render(source, source_module)
        participants = [json.loads((directory / (role + ".json")).read_bytes())
                        for role in ["producer", "validator"]]
        pair_module = "RootPairExport" + name
        pair_text = pair.render([pair.FORMAT, *participants], pair_module)
        digest = "sha256:" + hashlib.sha256(source_bytes).hexdigest()
        identities = ["sha256:" + hashlib.sha256((directory / (role + ".identity")).read_bytes()).hexdigest()
                      for role in ["producer", "validator"]]
        if name in retained and [digest, *identities] != retained[name]:
            raise ValueError(f"fixed export identity differs: {name}; checked request migration required")
        metadata.append((name, digest, *identities))
        for module, text, imports, equation in [
            (source_module, source_text, row["sourceModule"],
             f"{source_module}.snapshot = {row['sourceModule']}.program.snapshot"),
            (pair_module, pair_text, row["pairModule"],
             f"{pair_module}.artifacts = {row['pairModule']}.artifacts"),
        ]:
            text = text.replace("module\n", f"module\n\npublic import {imports}\n", 1)
            text += f"\nexample : {equation} := by rfl\n"
            path = generation.directory / (module + ".lean")
            path.write_text(text)
            generation.compile(module, path)
    metadata_path = generation.module_path("ZkcSecurity.Generation.Roots.ExportMetadata")
    if options.write:
        metadata_path.write_text(export_metadata(metadata))
    elif metadata_path.read_text() != export_metadata(metadata):
        raise AssertionError("stale generated export metadata")
    for module in ["ZkcSecurity.Generation.Roots.ExportMetadata", "ZkcSecurity.Generation.Roots.Subjects",
                   "TestsSecurity.GenerateSubjects"]:
        generation.compile(module)

    run_directory = generation.directory / "runs" / generation.run_id
    regenerated = run_directory / "regenerated"
    generation.printer("GenerateRootSubjects", f'''import TestsSecurity.GenerateSubjects

def main : IO Unit := TestsSecurity.GenerateSubjects.main [{json.dumps(str(regenerated))}]
''')
    baseline = generation.directory / "baseline"
    baseline.mkdir(exist_ok=True)
    for row in manifest:
        path = generation.module_path(row["subjectModule"])
        saved = baseline / (row["name"] + ".lean")
        if not saved.exists():
            saved.write_text(path.read_text())
    subject_paths = sorted(regenerated.rglob("*.lean"))
    expected_subjects = {row["subjectModule"] for row in manifest}
    expected_subjects.update(row["aliasesModule"] for row in manifest)
    expected_subjects.add("ZkcSecurity.Generation.Roots.SubjectImports")
    actual_subjects = {".".join(path.relative_to(regenerated).with_suffix("").parts) for path in subject_paths}
    if actual_subjects != expected_subjects:
        raise AssertionError("production subject output inventory differs from catalogue")
    generated = ["ZkcSecurity.Generation.Roots.ExportMetadata"]
    for path in subject_paths:
        module = ".".join(path.relative_to(regenerated).with_suffix("").parts)
        generation.retain(module, path.read_text())
        generated.append(module)
    generation.compile("ZkcSecurity.Generation.Roots.Stages")
    generation.printer("GenerateRootStages", f'''import ZkcSecurity.Generation.Roots.Stages

def main : IO Unit := ZkcSecurity.Generation.Roots.writeSources {json.dumps(str(regenerated))}
  (ZkcSecurity.Generation.Roots.stageSources.map fun (_, name, source) => (name, source))
''')
    for path in sorted(regenerated.rglob("*.lean")):
        module = ".".join(path.relative_to(regenerated).with_suffix("").parts)
        if module in generated:
            continue
        if generation.module_path(module).read_bytes() != path.read_bytes():
            raise AssertionError(f"downstream output changed: {module}")
        generated.append(module)
        if module.endswith("ABI"):
            generation.compile(module)

    # The actual default entry point must exercise the production catalogue.
    drivers = ["ClaimLibraries", "CompletenessClaims", "SubjectABI",
               "SumcheckCompleteness", "SumcheckSoundness"]
    for name in drivers:
        generation.compile("TestsSecurity.Generate" + name)
    default_output = run_directory / "default-regenerated"
    generation.execute([generation.lean, "--run", "checks/RunGenerators.lean", "subjects", default_output], generation.package)
    default_paths = sorted(default_output.rglob("*.lean"))
    if {path.relative_to(default_output) for path in default_paths} != {path.relative_to(regenerated) for path in subject_paths}:
        raise AssertionError("default subject output inventory differs")
    for path in default_paths:
        if path.read_bytes() != (regenerated / path.relative_to(default_output)).read_bytes():
            raise AssertionError(f"default generation differs: {path}")
    imports = "\n".join("import TestsSecurity.Generate" + name for name in drivers)
    calls = "\n".join("  TestsSecurity.Generate" + name + ".main [" + json.dumps(str(default_output)) + "]"
                      for name in drivers)
    generation.printer("GenerateRootDrivers", imports + "\n\ndef main : IO Unit := do\n" + calls + "\n")
    generation.execute([generation.lean, "--run", "checks/RunGenerators.lean", "bindings", default_output], generation.package)
    default_paths = sorted(default_output.rglob("*.lean"))
    if {path.relative_to(default_output) for path in default_paths} != {path.relative_to(regenerated) for path in regenerated.rglob("*.lean")}:
        raise AssertionError("default downstream output inventory differs")
    for path in default_paths:
        if path.read_bytes() != (regenerated / path.relative_to(default_output)).read_bytes():
            raise AssertionError(f"default downstream generation differs: {path}")
    generation.compile("TestsSecurity.GenerateRootControls")

    for row in manifest:
        module, source = source_request_module(row["subjectModule"], options.exports / row["name"])
        generation.retain(module, source)
        generated.append(module)

    preservation = ["import ZkcSecurity.Claims.CanonicalAuthorityPair"]
    for row in manifest:
        module = "RootBaseline" + row["name"]
        text = (baseline / (row["name"] + ".lean")).read_text().replace(row["subjectModule"], module)
        path = generation.directory / (module + ".lean")
        path.write_text(text)
        generation.compile(module, path)
        selected = row["subjectModule"]
        preservation += [f"import {selected}", f"import {module}", ""]
        for field in ["subject.reference", "subject.targetReference", "subject.acceptance",
                      "validatorSubject.reference",
                      "validatorSubject.targetReference", "validatorSubject.acceptance"]:
            preservation.append(f"example : {selected}.{field} = {module}.{field} := by rfl")
        preservation.append(f"example (inputs : {selected}.subject.Inputs) :\n"
                            f"    {selected}.subject.HonestInput inputs ↔ {module}.subject.HonestInput inputs := Iff.rfl")
        preservation.append(f"example (inputs : {selected}.subject.Inputs) :\n"
                            f"    {selected}.subject.Relation inputs ↔ {module}.subject.Relation inputs := Iff.rfl")
        preservation.append(f"example (inputs : {selected}.subject.Inputs) :\n"
                            f"    {selected}.subject.runtimeInputs inputs = {module}.subject.runtimeInputs inputs := by rfl")
        preservation.append(f"example : {selected}.validatorSites.map (fun site => (site.label, site.native, site.occurrence)) =\n"
                            f"    {module}.validatorSites.map (fun site => (site.label, site.native, site.occurrence)) := by rfl")
    # Imports precede all declarations in the kernel preservation client.
    imports = [line for line in preservation if line.startswith("import ")]
    equations = [line for line in preservation if not line.startswith("import ")]
    path = generation.directory / "RootPreservation.lean"
    path.write_text("\n".join(imports + ["set_option maxRecDepth 50000", "set_option maxHeartbeats 16000000"] + equations) + "\n")
    generation.compile("RootPreservation", path)
    outputs = [{"module": module, "bytes": generation.module_path(module).stat().st_size,
                "sha256": hashlib.sha256(generation.module_path(module).read_bytes()).hexdigest()}
               for module in generated]
    report = {"roots": [row["name"] for row in manifest], "outputs": outputs,
              "exact_downstream_regeneration": True, "fixed_request_preservation": True,
              "exact_default_regeneration": True,
              "exact_source_request_regeneration": True,
              "current_export_equations": True, "origin_refusals": True,
              "shared_lake_builds": 0, "commands": len(generation.commands)}
    (generation.directory / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS {len(outputs)} exact outputs; export equations, request preservation and origin refusals")


if __name__ == "__main__":
    main()
