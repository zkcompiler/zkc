#!/usr/bin/env python3
"""Export the actual mixed root and invoke the generic structured printers.

Run from any directory with --compiler pointing at an existing zkc-compile.
No compiler/dependency build, manifest update, or inventory edit is performed.
Use --output-root for isolated candidate generation and --negative-controls to
check that changed source cannot reuse the installed component laws.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import sys
import os
from pathlib import Path
import subprocess
import time

REPOSITORY = Path(__file__).resolve().parents[3]
SECURITY = REPOSITORY / "lean/security"
NAMESPACE = "ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated"
MODULE = NAMESPACE.replace(".", "/")
PRINTER_CACHE: Path | None = None

MODULES = [MODULE + "/" + name + ".lean" for name in
           ["Data", "Inputs", "RoundProducer", "RoundVerifier", "RootProducer", "RootVerifier"]]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], cwd: Path, report: Path, *, env=None, expected=0) -> subprocess.CompletedProcess:
    started = time.monotonic()
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = f"command-{time.time_ns()}.log"
    (report / log).write_text(result.stdout)
    row = dict(command=command, cwd=str(cwd), exit=result.returncode, log=log,
               elapsed=round(time.monotonic() - started, 3))
    with (report / "commands.jsonl").open("a") as output:
        output.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)
    if expected == 0 and result.returncode != 0:
        raise RuntimeError(f"command failed; see {report / log}")
    if expected is not None and expected != 0 and result.returncode == 0:
        raise RuntimeError(f"negative control unexpectedly passed; see {report / log}")
    return result


def generate(compiler: Path, fixture: Path, output: Path, report: Path) -> bool:
    report.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    emitted = run([str(compiler), "language-emit", "--source-format=zkc", "--subject=Root",
                   "--module=mixed_sumcheck=" + str(fixture),
                   "--module=zkc::primitives::vector=" + str(REPOSITORY / "libraries/core/primitives/collections/vector.zkc")], REPOSITORY, report, expected=None)
    if emitted.returncode != 0:
        return False
    mlir = report / "source.mlir"
    mlir.write_text(emitted.stdout)
    exported = run([str(compiler), "protocol-structured", str(mlir),
                    "--symbol=s14h6d697865645f73756d636865636b4h526f6f74"], REPOSITORY, report, expected=None)
    if exported.returncode != 0:
        return False
    snapshot = report / "snapshot.json"
    snapshot.write_text(exported.stdout)
    identity = dict(binary=str(compiler), binary_sha256=digest(compiler),
                    fixture_sha256=digest(fixture), mlir_sha256=digest(mlir),
                    snapshot_source=json.loads(exported.stdout)[2],
                    snapshot_sha256=digest(snapshot))
    (report / "identity.json").write_text(json.dumps(identity, indent=2) + "\n")
    return render_snapshot(snapshot, output, report)


def lean_json(value) -> str:
    """Render retained JSON structurally, without interpreting component routes."""
    if value is None:
        return ".null"
    if isinstance(value, bool):
        return ".bool " + str(value).lower()
    if isinstance(value, int) and value >= 0:
        return ".num ⟨.ofNat " + str(value) + ", 0⟩"
    if isinstance(value, str):
        return ".str " + json.dumps(value, ensure_ascii=False)
    if isinstance(value, list):
        return ".arr #[" + ", ".join("(" + lean_json(item) + ")" for item in value) + "]"
    raise ValueError("unsupported component wire value")


def export_components(compiler: Path, fixture: Path, output: Path, report: Path) -> bool:
    result = run([str(compiler), "language-check", "--source-format=zkc", "--subject=Root",
                  "--source-claims", "--module=mixed_sumcheck=" + str(fixture),
                  "--module=zkc::primitives::vector=" + str(REPOSITORY / "libraries/core/primitives/collections/vector.zkc")],
                 REPOSITORY, report, expected=None)
    if result.returncode:
        return False
    (report / "source-claims.json").write_text(result.stdout)
    identity_path = report / "identity.json"
    identity = json.loads(identity_path.read_text())
    identity["source_claims_sha256"] = digest(report / "source-claims.json")
    identity_path.write_text(json.dumps(identity, indent=2) + "\n")
    sys.path.insert(0, str(REPOSITORY / "lean"))
    from bridges.pipeline.source_claims import decode
    wire = decode(result.stdout)["source_claims"]
    source = """module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Data
public import Zkc.Source.Structured.ComponentExport
public import Init.Data.List.Sort.Lemmas
-- Kernel association needs the bodies of the JSON accessors.
import all Lean.Data.Json.Basic
public import Zkc.Source.KernelRfl

@[expose] public section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Association
open Lean Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
"""
    source += "def proposals : Json := " + lean_json(wire["proposals"]) + "\n"
    source += "def seams : Json := " + lean_json(wire["seams"]) + "\n"
    source += """
def wire : ComponentExport.Export :=
  (ComponentExport.decode proposals seams).toOption.getD ⟨[], []⟩
theorem decoded : ComponentExport.decode proposals seams = .ok wire := by kernel_rfl
-- The retained declarations are ordered by their source names. Use the
-- library sorting law rather than reducing its opaque implementation.
theorem ordered : Data.snapshot.protocolFunctions.mergeSort (fun left right => left.name ≤ right.name) =
    Data.snapshot.protocolFunctions := List.mergeSort_of_pairwise (by decide +kernel)
def derived : ComponentRoutes.Result := (do
  for owner in Data.snapshot.protocolFunctions do
    let environment ← ComponentRoutes.inputs Data.snapshot owner
    let _ ← ComponentRoutes.block Data.snapshot owner 65 owner.body owner.inputs environment
      (ComponentRoutes.liveOf environment) [] []
  : ComponentRoutes.Derive Unit).run {} |>.toOption.getD ((), {}) |>.2
theorem recomputed : ComponentRoutes.derive Data.snapshot = .ok derived := by
  unfold ComponentRoutes.derive
  change (do
    let (_, result) ← (do
      for owner in Data.snapshot.protocolFunctions.mergeSort (fun left right => left.name ≤ right.name) do
        let environment ← ComponentRoutes.inputs Data.snapshot owner
        let _ ← ComponentRoutes.block Data.snapshot owner 65 owner.body owner.inputs environment
          (ComponentRoutes.liveOf environment) [] []
      : ComponentRoutes.Derive Unit).run {}
    pure result) = .ok derived
  rw [ordered]
  kernel_rfl
def associated : ComponentExport.Associated Data.snapshot wire where
  derived := derived
  recomputed := recomputed
  seams := by kernel_rfl
  proposals := by unfold ComponentExport.check; rw [recomputed]; kernel_rfl
end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Association
"""
    (output / MODULE / "Components.lean").write_text(source)
    return True


def export_pair(compiler: Path, fixture: Path, output: Path, report: Path) -> None:
    """The frontend selects every draw and delivery from the authored proof."""
    bundle = run([str(compiler), "language-bundle", "--source-format=zkc", "--entry-kind=proof",
                  "--entry=mixed_sumcheck::Proof", "--module=mixed_sumcheck=" + str(fixture),
                  "--module=zkc::primitives::vector=" + str(REPOSITORY / "libraries/core/primitives/collections/vector.zkc")],
                 REPOSITORY, report)
    (report / "proof-bundle.json").write_text(bundle.stdout)
    policy = report / "policy.json"
    policy.write_text(json.dumps(json.loads(bundle.stdout)[2][1]) + "\n")
    mlir = report / "source.mlir"
    candidate = report / "candidate.mlir"
    candidate.write_text(run([str(compiler), "protocol-construct-proof", str(mlir), str(policy)],
                             REPOSITORY, report).stdout)
    arguments = [str(mlir), str(policy), str(candidate)]
    exported = run([str(compiler), "protocol-constructed-pair", *arguments], REPOSITORY, report)
    (report / "pair.json").write_text(exported.stdout)
    children = json.loads(exported.stdout)
    for role, child in zip(["producer", "validator"], children[1:]):
        result = run([str(compiler), "protocol-constructed-participant", *arguments, "--role=" + role],
                     REPOSITORY, report)
        if json.loads(result.stdout) != child:
            raise RuntimeError("individual participant differs from retained pair")
        (report / (role + ".json")).write_text(result.stdout)
    sys.path.insert(0, str(REPOSITORY / "lean"))
    from bridges.construction import pair
    (output / MODULE / "Pair.lean").write_text(pair.render(children, NAMESPACE + ".Pair"))
    identity = json.loads((report / "identity.json").read_text())
    identity.update({name + "_sha256": digest(report / filename) for name, filename in
                     [("policy", "policy.json"), ("candidate", "candidate.mlir"), ("pair", "pair.json"),
                      ("producer", "producer.json"), ("validator", "validator.json")]})
    (report / "identity.json").write_text(json.dumps(identity, indent=2) + "\n")
    identifiers = dict(sourceExport="snapshot_sha256", validatorExport="validator_sha256", producerExport="producer_sha256")
    lines = ["module", "", "@[expose] public section", "namespace " + NAMESPACE + ".Identity"]
    lines.extend("def " + name + " : String := " + json.dumps("sha256:" + identity[key]) for name, key in identifiers.items())
    lines.append("end " + NAMESPACE + ".Identity")
    (output / MODULE / "Identity.lean").write_text("\n".join(lines) + "\n")

def render_snapshot(snapshot: Path, output: Path, report: Path) -> bool:
    spec = importlib.util.spec_from_file_location("structured_snapshot", REPOSITORY / "lean/bridges/structured/snapshot.py")
    assert spec is not None and spec.loader is not None
    printer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(printer)
    data = output / MODULE / "Data.lean"
    data.parent.mkdir(parents=True, exist_ok=True)
    data.write_text(printer.render(json.loads(snapshot.read_text()), NAMESPACE + ".Data"))
    # The driver admits the snapshot and selects typed helper/callee signatures;
    # OriginalRoot.templateSource supplies all forms and occurrence associations.
    command = ["lake", "env", "lean"]
    environment = None
    if PRINTER_CACHE is not None:
        lean = run(["lake", "env", "which", "lean"], SECURITY, report).stdout.strip()
        search = run(["lake", "env", "printenv", "LEAN_PATH"], SECURITY, report).stdout.strip()
        paths = [str((SECURITY / path).resolve()) for path in search.split(os.pathsep)]
        environment = dict(os.environ, LEAN_PATH=str(PRINTER_CACHE) + os.pathsep + os.pathsep.join(paths))
        command = [lean]
    result = run(command + ["--run", "checks/GenerateKoalaBearSumcheck.lean", str(snapshot), str(output)],
                 SECURITY, report, env=environment, expected=None)
    return result.returncode == 0


def check_candidate(output: Path, report: Path, control: str) -> subprocess.CompletedProcess:
    lean = run(["lake", "env", "which", "lean"], SECURITY, report).stdout.strip()
    search = run(["lake", "env", "printenv", "LEAN_PATH"], SECURITY, report).stdout.strip()
    paths = [str((SECURITY / path).resolve()) for path in search.split(os.pathsep)]
    env = dict(os.environ, LEAN_PATH=str(output) + os.pathsep + os.pathsep.join(paths))
    # Lean resolves a package at the first matching directory. Mirror the
    # existing security library with read-only links, keeping candidate modules.
    library = PRINTER_CACHE or SECURITY / ".lake/build/lib/lean"
    for original in library.rglob("*"):
        if original.is_file() and not str(original.relative_to(library)).startswith(MODULE + "/"):
            linked = output / original.relative_to(library)
            if not linked.exists():
                linked.parent.mkdir(parents=True, exist_ok=True)
                linked.symlink_to(original)
    for module in MODULES:
        target = output / module.removesuffix(".lean")
        run([lean, "-DwarningAsError=true", "-o", str(target) + ".olean", str(output / module)],
            output, report, env=env)
    relative = "ZkcSecurity/Examples/Components/KoalaBearSumcheckSource.lean"
    source = output / relative
    text = (SECURITY / relative).read_text()
    if control == "helper-body":
        text = text[:text.index("\ndef results")] + "\nend ZkcSecurity.Examples.Components.KoalaBearSumcheckSource\n"
    source.write_text(text)
    return run([lean, "-DwarningAsError=true", str(source)], output, report, env=env, expected=1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, default=SECURITY)
    parser.add_argument("--report-dir", type=Path, default=REPOSITORY / "build/experiments/mixed-integration/generation")
    parser.add_argument("--negative-controls", action="store_true")
    parser.add_argument("--controls", nargs="+", choices=["ordered-operands", "helper-body", "nominal-domain", "wrong-role"])
    parser.add_argument("--printer-cache", type=Path, help="optional private cache for repository printer tools")
    args = parser.parse_args()
    global PRINTER_CACHE
    PRINTER_CACHE = args.printer_cache.resolve() if args.printer_cache else None
    compiler, output, report = args.compiler.resolve(), args.output_root.resolve(), args.report_dir.resolve()
    fixture = SECURITY / "fixtures/koala-bear-sumcheck-round.zkc"
    if not generate(compiler, fixture, output, report):
        raise RuntimeError("generic generation refused the actual source")
    export_pair(compiler, fixture, output, report)
    components_exported = export_components(compiler, fixture, output, report)
    (report / "component-export-result.json").write_text(json.dumps(dict(passed=components_exported)) + "\n")
    if args.negative_controls:
        text = fixture.read_text()
        variants = {
            "ordered-operands": text.replace("(received_high - received_low)", "(received_low - received_high)"),
            "helper-body": text.replace('fn embed(value: Base) -> Extension {',
                                         'fn embed(value: Base) -> Extension {\n  require false;'),
            "wrong-role": text.replace('Round roles(P,V)(a,b,initial,challenges)',
                                       'Round roles(V,P)(a,b,initial,challenges)'),
            "nominal-domain": text.replace("ext8-binomial3", "ext4-binomial3"),
        }
        for name, changed in variants.items():
            if args.controls and name not in args.controls:
                continue
            if changed == text:
                raise RuntimeError(f"mutation did not change source: {name}")
            case = report / name
            case.mkdir(parents=True, exist_ok=True)
            candidate = case / "fixture.zkc"
            candidate.write_text(changed)
            generated = generate(compiler, candidate, case / "modules", case)
            boundary = "native export or typed selection"
            if generated:
                boundary = "actual exported body and installed law"
            if generated:
                failure = check_candidate(case / "modules", case, name)
                # An import failure or resource timeout is not body-law evidence.
                if not any(message in failure.stdout for message in
                           ["declaration type mismatch", "unsolved goals", "Tactic `rfl` failed"]):
                    raise RuntimeError("negative control failed outside the installed body/helper law")
            (case / "refused.json").write_text(json.dumps(dict(control=name, refused=True, boundary=boundary)) + "\n")
    if not components_exported:
        raise RuntimeError("component export refused the actual source")


if __name__ == "__main__":
    main()
