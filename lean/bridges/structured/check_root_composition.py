#!/usr/bin/env python3
"""Check the actual four-call source using current connections and family laws.

Source checks run independently of artifact connections. The endpoint gate uses
the common subject, ABI, endpoint and exact-request consumers. Generated Lean
output and checked-object cache records stay in the isolated output directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "common/tests/support"))
from bridges.structured.generate_component_roots import Generation, quoted  # noqa: E402
from project import project_inputs  # noqa: E402
from checks.check_subject_roots import source_request_module  # noqa: E402


class ScratchGeneration(Generation):
    def __init__(self, args):
        super().__init__(args)
        self.cache_path = self.directory / "checked-modules.json"
        self.cache = json.loads(self.cache_path.read_text()) if self.cache_path.is_file() else {}

    def fingerprint(self, module, source):
        """Cache identity only; checked Lean proofs authorize every property."""
        files = {}
        visited = set()

        def visit(name, path=None):
            if name in visited:
                return
            visited.add(name)
            relative = Path(*name.split(".")).with_suffix(".lean")
            candidates = [self.directory / "source" / relative,
                          ROOT / "lean/security" / relative, ROOT / "lean" / relative]
            path = path or next((item for item in candidates if item.is_file()), None)
            obj = self.output / relative.with_suffix(".olean")
            for item in [path, obj]:
                if item is not None and item.is_file():
                    files[str(item)] = hashlib.sha256(item.read_bytes()).hexdigest()
            if path is not None:
                for imported in re.findall(r"^(?:public )?(?:meta )?import ([\w.]+)",
                                           path.read_text(), re.MULTILINE):
                    visit(imported)

        visit(module, source)
        return files

    def compile(self, module, source=None, run=False, source_root=None):
        source = source or self.module_path(module)
        identity = self.fingerprint(module, source) if not run else None
        if not run and self.args.resume and self.cache.get(module) == identity:
            print(f"Reusing checked {module} (identical source and dependency objects)", flush=True)
            return ""
        result = super().compile(module, source, run, source_root)
        if not run:
            self.cache[module] = self.fingerprint(module, source)
            self.cache_path.write_text(json.dumps(self.cache, indent=2) + "\n")
        return result

    def execute(self, command, cwd=ROOT):
        if str(command[0]) == self.lean:
            command = [command[0], "-j2", "-M16384", *command[1:]]
        return super().execute(command, cwd)

    def retain(self, module, text):
        path = self.directory / "source" / Path(*module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        self.generated.append(str(path))
        self.compile(module, path, source_root=self.directory / "source")

    def emit(self, label, imports, body, outputs, declarations=""):
        bindings = self.directory / "bindings"
        bindings.mkdir(exist_ok=True)
        self.printer(label, "\n".join("import " + item for item in imports) + f'''
open Zkc.Source.Structured ZkcTools.StructuredSource
set_option maxRecDepth 10000
def program : Program := (check ZkcExamples.Structured.Generated.Bindings.FourSumsData.snapshot).toOption.get (by decide +kernel)
def emit (name : String) (source : Except String String) : IO Unit := do
  let .ok text := source | throw (IO.userError "source proposal refused")
  IO.FS.writeFile ({quoted(str(bindings))} ++ "/" ++ name ++ ".lean") text
{declarations}
def main : IO Unit := do
{body}
''')
        for module in outputs:
            self.retain(module, (bindings / (module + ".lean")).read_text())


def endpoint_shells(generation, subject, pair):
    """Select existing theorems at the common consumers' fixed propositions."""
    component = "ZkcSecurityExamples.Generated.Components.FourSums"
    component_namespace = "ZkcSecurity.Examples.Generated.Components.FourSums"
    subject_namespace = "ZkcSecurity.Examples.Generated.FourSums"
    proof = "TestsSecurity.RootComposition.Four.Endpoints"
    outputs = [component + "Completeness", subject + "CompletenessClaims",
               component + "Soundness", subject + "SoundnessRegistration"]
    declarations = f'''
run_cmd do
  let metadata ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata {subject_namespace}.subject)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
  let completeness : RootCompleteness.Selection := {{
    moduleName := {quoted(outputs[0])}, namespaceName := {quoted(component_namespace + "Completeness")},
    subjectModule := {quoted(subject)}, subjectNamespace := {quoted(subject_namespace)}, error := .zero }}
  let soundness : OriginalEndpoint.Output := {{
    moduleName := {quoted(outputs[2])}, namespaceName := {quoted(component_namespace + "Soundness")},
    subjectModule := {quoted(subject)}, subjectNamespace := {quoted(subject_namespace)},
    methodModule := "TestsSecurity.RootComposition.FourSoundness",
    sampling := "ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus",
    capabilities := {quoted(proof + '.Soundness.claimCapabilities')},
    schedule := {quoted(proof + '.Soundness.schedule')},
    validatorCost := {quoted(proof + '.Soundness.validatorCost')},
    chargedExport := {quoted(proof + '.Soundness.reductionExport')},
    scalar := some ⟨{quoted(proof + '.Soundness.scalarBound')}, {quoted(proof + '.Soundness.scalar_bound')}⟩ }}
  let .ok soundnessText := OriginalEndpoint.soundnessSource metadata {pair}.Validator.participant soundness
    | Lean.throwError "common original endpoint refused"
  let registration : ZkcTools.StructuredSource.Root.DomainClaimLibraryOutput := {{
    moduleName := {quoted(outputs[3])}, namespaceName := {quoted(subject_namespace + "SoundnessRegistration")}, imports := [{quoted(subject)}, {quoted(outputs[2])}],
    subjectExpression := {quoted(subject_namespace + '.validatorSubject')},
    artifactsExpression := {quoted(subject_namespace + '.validatorArtifacts')},
    capabilitiesExpression := {quoted(component_namespace + 'Soundness.capabilities')},
    applicationParameter := some "application",
    theoremMethods := [("fs.keyed_soundness", 0, {quoted(component_namespace + 'Soundness.scalar_meaning')}),
      ("fs.keyed_charged", 0, {quoted(component_namespace + 'Soundness.charged_meaning')})],
    theoremNormalization := {quoted([component_namespace + 'Soundness.' + name for name in ['schedule', 'validatorCost', 'scalarBound']] + [proof + '.Soundness.' + name for name in ['schedule', 'price', 'priceBound', 'budget', 'validatorCost', 'scalarBound']] + ['ZkcSecurity.Claims.CompiledSoundness.uniformSchedule'])} }}
  let sources : List (String × String) := [
    ({quoted(outputs[0])}, RootCompleteness.directSource completeness
      "TestsSecurity.RootComposition.FourEndpoints" {quoted(proof + '.compiled_ideal_complete')}
      "rawSampleable blsModulus" ["ZkcSecurity.Domains.PrimeField"]),
    ({quoted(outputs[1])}, RootCompleteness.claimsSource completeness {{
      capabilities := "ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)" }}),
    ({quoted(outputs[2])}, soundnessText),
    ({quoted(outputs[3])}, ZkcTools.StructuredSource.Root.domainClaimLibrarySource registration)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))
'''
    generation.emit("EndpointShells", ["ZkcSecurityTools.Generation.RootCompleteness",
                    "ZkcSecurityTools.Generation.OriginalEndpoint", subject, pair],
                    "  for (name, text) in sources do emit name (.ok text)", outputs,
                    "open ZkcSecurity.Generation\n" + declarations)


def check(args):
    if os.environ.get("ELAN_TOOLCHAIN") != "leanprover/lean4:v4.35.0":
        raise ValueError("set ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0")
    generation = ScratchGeneration(args)
    fixture = Path(__file__).parent / "fixtures/root-composition"
    modules, assets = project_inputs(fixture / "zkc.toml")
    if assets:
        raise ValueError("the root-composition fixture must not contain assets")
    root = dict(name="FourSums", entry="example::Proof", source=str(modules.pop("example")),
                modules={key: str(value) for key, value in modules.items()}, target="totals")
    config = tomllib.loads((Path(__file__).parent / "roots/sampled.toml").read_text())
    name = root["name"]
    data = f"ZkcExamples.Structured.Generated.Bindings.{name}Data"
    inputs = f"ZkcExamples.Structured.Generated.Bindings.{name}Inputs"
    pair = f"ZkcExamples.Construction.Generated.{name}Pair"
    mathematics = f"ZkcExamples.Structured.Generated.Mathematics.{name}"
    connection = f"ZkcExamples.Structured.Generated.Connections.{name}"
    subject = f"ZkcSecurityExamples.Generated.{name}"
    subject_namespace = f"ZkcSecurity.Examples.Generated.{name}"
    abi = f"ZkcSecurityExamples.Generated.Components.{name}ABI"
    abi_namespace = f"ZkcSecurity.Examples.Generated.Components.{name}ABI"
    source_module = "TestsSecurity.RootComposition.FourSource"
    result_file = generation.directory / "acceptance.json"
    result_file.unlink(missing_ok=True)
    export_inputs = {path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
                     for path in [root["source"], *root["modules"].values()]}
    export_record = generation.directory / "export-inputs.json"
    if args.resume and (not export_record.is_file() or
                        json.loads(export_record.read_text()) != export_inputs):
        raise ValueError("resume requires identical recorded fixture inputs; use a fresh output otherwise")
    if not args.resume:
        generation.export(root)
        # The binding printer needs only the checked snapshot, not a connection.
        path = generation.directory / "Inputs.lean"
        generation.printer("InputBindings", f'''import ZkcTools.StructuredSource.Bindings.Inputs
import {data}
open Zkc.Source.Structured ZkcTools.StructuredSource
def main : IO Unit := do
  let program := (check {data}.snapshot).toOption.get (by decide +kernel)
  IO.FS.writeFile {quoted(str(path))} (Bindings.inputsSource program {quoted(inputs)} {quoted(data)})
''')
        generation.retain(inputs, path.read_text())
        export_record.write_text(json.dumps(export_inputs, indent=2) + "\n")
    source_modules = [source_module, "TestsSecurity.RootComposition.FourRuns"]
    source_record = generation.directory / "source-check.json"
    for module in source_modules:
        generation.retain(module, (fixture / (module.split(".")[-1] + ".lean")).read_text())
    source_record.write_text(json.dumps({module: generation.cache[module]
                                       for module in source_modules}, indent=2) + "\n")
    # Preserve the common renderer's exact requests before resolving them.
    request_module, requests = source_request_module(subject, subject_namespace, generation.directory / name)
    request_path = generation.directory / "unresolved-requests" / (request_module + ".lean")
    request_path.parent.mkdir(exist_ok=True)
    request_path.write_text(requests)
    result = {"phase": args.phase, "source": "checked", "fixture": str(fixture / "four.zkc"),
              "endpoint_status": "not_checked_in_this_phase", "receipt_status": "not_checked_in_this_phase",
              "source_requests": {"status": "bound_and_rendered_not_resolved", "path": str(request_path)},
              "remaining": []}
    if args.phase != "source":
        generation.prepare(["Zkc.Construction.ConnectionCertificateAdmission",
                            "ZkcTools.ConstructionBindings.Generate"])
        views = [f"ZkcExamples.Structured.Generated.Constructed.{name}{role}"
                 for role in ("Producer", "Validator")]
        generation.emit("Connections", ["ZkcTools.ConstructionBindings.Generate", inputs, pair], f'''
  let .ok outputs := ZkcTools.ConstructionBindings.Generate.bundle
    {{ sourceModule := {quoted(inputs)}.toName, program := {quoted(inputs + '.program')}.toName }}
    {quoted(connection)}.toName
    [({{ mode := .producer, artifactModule := {quoted(pair)}.toName,
         artifact := {quoted(pair + '.Producer.participant')}.toName, viewModule := {quoted(views[0])}.toName }},
       {pair}.Producer.participant),
     ({{ mode := .validator, artifactModule := {quoted(pair)}.toName,
         artifact := {quoted(pair + '.Validator.participant')}.toName, viewModule := {quoted(views[1])}.toName }},
       {pair}.Validator.participant)] | throw (IO.userError "connection proposal refused")
  for (moduleName, text) in outputs do emit moduleName.toString (.ok text)''', [*views, connection])
        # Current source-path selection supplies charges, subject and target data.
        identities = json.loads((generation.directory / name / "identities.json").read_text())
        path = generation.directory / "Subject.lean"
        generation.printer("Subject", f'''import ZkcSecurityExamples.Generation.Roots.Catalogue
import {inputs}
import {pair}
open ZkcSecurity.Generation ZkcTools.StructuredSource.Root
set_option maxRecDepth 10000
def selection : Roots.Selection := {{
 name := {quoted(name)}, snapshot := {data}.snapshot, helpers := [],
 artifacts := {pair}.artifacts, target := "totals",
 mathematics := {{
   moduleName := {quoted(config['model_module'])}
   model := {quoted(config['model'])}
   fieldType := {quoted(config['field_type'])}
   groupType := {quoted(config['group_type'])}
   modulus := "blsModulus"
   sampling := {quoted(config['sampling'])}
   capabilities := {quoted(config['capabilities'])}}},
 formulaNamespace := "TestsSecurity.RootComposition.Four.Formula",
 registryExpression := "Zkc.Source.Structured.OpaqueRegistry.empty" }}
def main : IO Unit := do
 let .ok selected := Roots.subjectOutput selection {quoted(identities['original'])}
     {quoted(identities['producer'])} {quoted(identities['validator'])}
   | throw (IO.userError "subject selection refused")
 IO.FS.writeFile {quoted(str(path))} (fixedSubjectSource {{selected with
   sourceModule := {quoted(inputs)}
   originalExpression := {quoted(data + '.snapshot')}
   importedExpression := {quoted(inputs + '.imported')}}})
''')
        generation.retain(subject, path.read_text())
        abi_path = generation.directory / "ABI.lean"
        generation.printer("ABI", f'''import ZkcSecurityTools.Generation.SubjectABI.Command
import {subject}
open ZkcSecurity.Generation.SubjectABI
set_option maxRecDepth 10000
derive_subject_abi generated for {subject_namespace}.subject using {{ moduleName := {quoted(abi)}, namespaceName := {quoted(abi_namespace)}, subjectModule := {quoted(subject)}, subjectNamespace := {quoted(subject_namespace)} }}
def main : IO Unit := IO.FS.writeFile {quoted(str(abi_path))} generated
''')
        generation.retain(abi, abi_path.read_text())
        generation.emit("Mathematics", ["ZkcTools.StructuredSource.MathematicsAliases", inputs],
                        f'  emit {quoted(mathematics)} (MathematicsAliases.source program "totals" '
                        f'{{moduleName := {quoted(mathematics)}, sourceModule := {quoted(inputs)}}})', [mathematics])
        generation.retain("TestsSecurity.RootComposition.FourFormula", (fixture / "FourFormula.lean").read_text())
        result["connections"] = "checked producer and validator"
        result["subject_abi_target"] = "checked"
    if args.phase in {"endpoints", "receipts", "all"}:
        for suffix in ["Properties", "Endpoints", "Soundness"]:
            generation.retain("TestsSecurity.RootComposition.Four" + suffix,
                              (fixture / ("Four" + suffix + ".lean")).read_text())
        endpoint_shells(generation, subject, pair)
        generation.retain(request_module, requests)
        generation.retain("TestsSecurity.RootComposition.FourReceipts",
                          (fixture / "FourReceipts.lean").read_text())
        result["endpoint_status"] = "checked"
        result["receipt_status"] = "proved_three_canonical_receipts"
        result["source_requests"]["status"] = "proved_unchanged"
    result["generated"] = generation.generated
    commands = generation.directory / f"commands-{generation.run_id}.json"
    result["commands"] = str(commands) if commands.is_file() else None
    result["source_check"] = str(source_record)
    result_file.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS FourSums " + args.phase)
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--output", default=ROOT / "build/experiments/root-composition/four", type=Path)
    parser.add_argument("--resume", action="store_true", help="reuse this output's checked exports")
    parser.add_argument("--dependency-path", action="append", type=Path, default=[])
    parser.add_argument("--phase", choices=["source", "structure", "endpoints", "receipts", "all"], default="all")
    parser.set_defaults(check=False)
    sys.exit(check(parser.parse_args()))
