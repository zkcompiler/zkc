#!/usr/bin/env python3
"""Check four actual calls with the production root printers in a scratch overlay.

The ordinary fixture supplies a complete protocol and a fixed target map. No
generated Lean output is retained in the source tree. Existing one/two-call
clients are checked by TestsSecurity.OriginalSecurityGeneration and their
canonical receipts. Pass a compiler built from the current language sources.
"""
import argparse
import json
from pathlib import Path
import shutil
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "common/tests/support"))
from bridges.structured.generate_component_roots import Generation, quoted  # noqa: E402
from project import project_inputs  # noqa: E402
from checks.check_subject_roots import source_request_module  # noqa: E402


class ScratchGeneration(Generation):
    def retain(self, module, text):
        path = self.directory / "source" / Path(*module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        self.generated.append(str(path))
        self.compile(module, path, source_root=self.directory / "source")

    def assemble(self, root, config):
        super().assemble(root, config)
        # The general completeness shell needs no adversarial charge selection.
        # This soundness client uses the production source-path discovery too.
        self.select_subject(root, config)
        abi = f"ZkcSecurity.Examples.Generated.Components.{root['name']}ABI"
        self.compile(abi, self.directory / "source" / Path(*abi.split(".")).with_suffix(".lean"),
                     source_root=self.directory / "source")

    def select_subject(self, root, config):
        name = root["name"]
        inputs = f"ZkcExamples.Structured.Generated.Bindings.{name}Inputs"
        pair = f"ZkcExamples.Construction.Generated.{name}Pair"
        subject = f"ZkcSecurity.Examples.Generated.{name}"
        identities = json.loads((self.directory / name / "identities.json").read_text())
        output = self.directory / "SelectedSubject.lean"
        self.printer("SelectRootSubject", f'''import ZkcSecurity.Generation.Roots.Catalogue
import {inputs}
import {pair}
open ZkcSecurity.Generation ZkcTools.StructuredSource.Root
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
def selection : Roots.Selection := {{
  name := {quoted(name)}, snapshot := ZkcExamples.Structured.Generated.Bindings.{name}Data.snapshot,
  helpers := [], artifacts := {pair}.artifacts, target := {quoted(root['target'])},
  mathematics := {{
    model := {quoted(config['model'])}, fieldType := {quoted(config['field_type'])},
    groupType := {quoted(config['group_type'])}, modulus := "blsModulus",
    sampling := {quoted(config['sampling'])}, capabilities := {quoted(config['capabilities'])} }},
  formulaNamespace := "TestsSecurity.RootComposition.Four.Formula",
  registryExpression := "Zkc.Source.Structured.OpaqueRegistry.empty" }}
def main : IO Unit := do
  let .ok output := Roots.subjectOutput selection {quoted(identities['original'])}
      {quoted(identities['producer'])} {quoted(identities['validator'])}
    | throw (IO.userError "source charge selection refused")
  IO.FS.writeFile {quoted(str(output))} (fixedSubjectSource output)
''')
        self.retain(subject, output.read_text())


def check(args):
    if args.phase == "receipts" and not args.resume:
        raise ValueError("the receipts phase requires --resume and checked body proofs")
    generation = ScratchGeneration(args)
    (generation.directory / "acceptance.json").unlink(missing_ok=True)
    fixture = Path(__file__).parent / "fixtures/root-composition"
    modules, assets = project_inputs(fixture / "zkc.toml")
    if assets:
        raise ValueError("the root-composition fixture must not contain assets")
    root = dict(name="FourSums", entry="example::Proof", source=str(modules.pop("example")),
                modules={key: str(value) for key, value in modules.items()}, target="totals")
    config = tomllib.loads((Path(__file__).parent / "roots/sampled.toml").read_text())
    if not args.resume:
        generation.export(root)
        generation.assemble(root, config)
    name = root["name"]
    inputs = f"ZkcExamples.Structured.Generated.Bindings.{name}Inputs"
    pair = f"ZkcExamples.Construction.Generated.{name}Pair"
    original = f"ZkcExamples.Structured.Generated.Original.{name}"
    artifact = f"ZkcExamples.Structured.OriginalArtifacts.{name}"
    producer = f"ZkcExamples.Structured.Generated.OriginalArtifacts.{name}ProducerSource"
    mathematics = f"ZkcExamples.Structured.Generated.Mathematics.{name}"
    output = f"ZkcSecurity.Examples.Generated.OriginalSecurity.{name}"
    subject = f"ZkcSecurity.Examples.Generated.{name}"
    abi = f"ZkcSecurity.Examples.Generated.Components.{name}ABI"
    formula = "TestsSecurity.RootComposition.FourFormula"
    sources = generation.directory / "bindings"
    sources.mkdir(exist_ok=True)

    def generate(label, imports, body, outputs):
        generation.printer(label, "\n".join("import " + item for item in imports) + f'''
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
open Zkc.Source.Structured ZkcTools.StructuredSource ZkcSecurity.Generation
def program : Program := (check ZkcExamples.Structured.Generated.Bindings.FourSumsData.snapshot).toOption.get (by decide +kernel)
def emit (name : String) (candidate : Except String String) : IO Unit := do
  match candidate with
  | .error reason => throw (IO.userError reason)
  | .ok text => IO.FS.writeFile ({quoted(str(sources))} ++ "/" ++ name ++ ".lean") text
def main : IO Unit := do
{body}
''')
        for module in outputs:
            generation.retain(module, (sources / (module + ".lean")).read_text())

    if args.phase not in {"endpoints", "receipts"}:
        generate("RootStructure", ["ZkcTools.StructuredSource.Methods.SumcheckRoot",
                 "ZkcTools.StructuredSource.MathematicsAliases", "ZkcSecurity.Generation.OriginalSecurityBindings",
                 inputs], f'''  emit {quoted(original)} (Methods.SumcheckRoot.source program {{
    moduleName := {quoted(original)}, sourceModule := {quoted(inputs)}, libraries := [Methods.SumcheckRoot.sumcheckLibrary] }})
  emit {quoted(mathematics)} (MathematicsAliases.source program "totals" {{
    moduleName := {quoted(mathematics)}, sourceModule := {quoted(inputs)} }})''', [original, mathematics])

        generate("RootArtifacts", ["ZkcSecurity.Generation.ConstructionBindingsRoots", inputs, pair, original], f'''
  let validator := {pair}.Validator.participant
  let prover := {pair}.Producer.participant
  emit {quoted(artifact)} (ConstructionBindings.source program validator prover
    {quoted(artifact)} {quoted(inputs)} {quoted(pair)})
  emit {quoted(producer)} (ZkcTools.ConstructionBindings.Source.source program {quoted(producer)} {quoted(original)})
  let .ok layout := ZkcTools.ConstructionBindings.analyze program validator
    | throw (IO.userError "validator layout refused")
  for (role, participant) in [(0, prover), (1, validator)] do
    let .ok selected := ZkcTools.ConstructionBindings.analyzeWithContext program layout.context participant
      | throw (IO.userError "participant layout refused")
    let moduleName := {quoted(artifact)} ++ (if role == 0 then "ProducerRoot" else "ValidatorRoot")
    emit moduleName (ConstructionBindingsRoots.source program participant selected role moduleName
      {quoted(artifact)} {quoted(original)} {quoted(producer)})''',
                 [artifact, producer, artifact + "ProducerRoot", artifact + "ValidatorRoot"])

    if args.phase != "receipts":
        # The only client-authored proof is its ordinary mathematical target map.
        if args.phase != "structure":
            generation.retain(formula, (fixture / "FourFormula.lean").read_text())
        properties = [("Sources", "sourceBindings"), ("Honest", "honestBindings")]
        if args.phase != "structure":
            properties = [("Sources", "sourceBindings"), ("Installation", "installationBindings"),
                          ("Soundness", "soundnessBindings"), ("Honest", "honestBindings"),
                          ("Completeness", "completenessBindings")]
        emit_calls = "\n".join(f"  emit {quoted(output + '.' + suffix)} (OriginalSecurityBindings.{function} program binding selected)"
                               for suffix, function in properties)
        generate("RootSecurity", ["ZkcSecurity.Generation.OriginalSecurityBindingsHonest", inputs, pair, subject], f'''
  let .ok binding := OriginalSecurityBindings.analyze program
      {pair}.Validator.participant {pair}.Producer.participant
    | throw (IO.userError "four-call binding refused")
  unless binding.calls.length == 4 && binding.conjunctions.length == 3 do
    throw (IO.userError "fixture did not exercise four calls and a conjunction tree")
  let selected : OriginalSecurityBindings.Output := {{
    moduleName := {quoted(output)}, originalModule := {quoted(original)}, artifactModule := {quoted(artifact)},
    subjectModule := {quoted(subject)}, abiModule := {quoted(abi)},
    formulaNamespace := "TestsSecurity.RootComposition.Four.Formula",
    fieldType := {quoted(config['field_type'])}, groupType := {quoted(config['group_type'])},
    modulus := "blsModulus", sampling := {quoted(config['sampling'])},
    capabilities := {quoted(config['capabilities'])} }}
{emit_calls}''', [output + "." + suffix for suffix, _ in properties])
    canonical_imports = []
    canonical_axioms = ""
    if args.phase != "structure":
        complete = f"ZkcSecurity.Examples.Generated.Components.{name}Completeness"
        sound = f"ZkcSecurity.Examples.Generated.Components.{name}Soundness"
        registration = subject + "SoundnessRegistration"
        normalization = [sound + "." + item for item in ["schedule", "validatorCost", "scalarBound"]]
        normalization += [output + ".Soundness." + item for item in
                          ["schedule", "price", "priceBound", "budget", "validatorCost", "scalarBound"]]
        normalization += ["ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"]
        generation.printer("CanonicalEndpoints", f'''import ZkcSecurity.Generation.OriginalEndpoint
import ZkcSecurity.Generation.RootCompleteness
import {subject}
open ZkcSecurity.Generation ZkcTools.StructuredSource
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
run_cmd do
 let metadata ← Lean.Elab.Command.liftTermElabM do
  let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata {subject}.subject)) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
  Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
 let .ok source := OriginalEndpoint.soundnessSource metadata {pair}.Validator.participant {{
   moduleName := {quoted(sound)}, subjectModule := {quoted(subject)}, methodModule := {quoted(output + '.Soundness')},
   sampling := {quoted(config['sampling'])}, capabilities := {quoted(config['capabilities'])},
   schedule := {quoted(output + '.Soundness.schedule')}, validatorCost := {quoted(output + '.Soundness.validatorCost')},
   chargedExport := {quoted(output + '.Soundness.reductionExport')},
   scalar := some ⟨{quoted(output + '.Soundness.scalarBound')}, {quoted(output + '.Soundness.scalar_bound')}⟩ }}
   | throwError "canonical soundness assembly refused"
 let name := Lean.mkIdent `soundness
 Lean.Elab.Command.elabCommand (← `(def $name : String := $(Lean.quote source)))
def selection : RootCompleteness.Selection := {{moduleName := {quoted(complete)}, subjectModule := {quoted(subject)}, error := .zero}}
def main : IO Unit := do
 IO.FS.writeFile {quoted(str(sources / (complete + '.lean')))} (RootCompleteness.directSource selection
   {quoted(output + '.Completeness')} {quoted(output + '.Completeness.compiled_ideal_complete')}
   {quoted(config['sampling'])} ["ZkcSecurity.Domains.PrimeField"])
 IO.FS.writeFile {quoted(str(sources / (subject + 'CompletenessClaims.lean')))}
   (RootCompleteness.claimsSource selection {{capabilities := {quoted(config['capabilities'])}}})
 IO.FS.writeFile {quoted(str(sources / (sound + '.lean')))} soundness
 IO.FS.writeFile {quoted(str(sources / (registration + '.lean')))} (Root.domainClaimLibrarySource {{
   moduleName := {quoted(registration)}, imports := [{quoted(subject)}, {quoted(sound)}],
   subjectExpression := {quoted(subject + '.validatorSubject')}, artifactsExpression := {quoted(subject + '.validatorArtifacts')},
   capabilitiesExpression := {quoted(sound + '.capabilities')}, applicationParameter := some "application",
   theoremMethods := [("fs.keyed_soundness",0,{quoted(sound + '.scalar_meaning')}), ("fs.keyed_charged",0,{quoted(sound + '.charged_meaning')})],
   theoremNormalization := [{', '.join(map(quoted, normalization))}] }})
''')
        for module in [complete, subject + "CompletenessClaims", sound, registration]:
            generation.retain(module, (sources / (module + ".lean")).read_text())
        modules, _ = project_inputs(fixture / "zkc.toml")
        flags = ["--source-format=zkc", "--entry=example::Proof",
                 *[f"--module={key}={path}" for key, path in modules.items()]]
        directory = generation.directory / name
        for filename, command in [("interface.json", "language-interface"),
                                  ("source-claims.json", "language-check"),
                                  ("deployment.json", "language-bundle")]:
            text = generation.execute([args.compiler, command, *flags,
                                       *(["--source-claims"] if command == "language-check" else [])])
            (directory / filename).write_text(text)
        for role in ["producer", "validator"]:
            shutil.copyfile(directory / (role + ".json"), directory / (role + ".identity"))
        module, text = source_request_module(subject, directory)
        generation.retain(module, text)
        canonical_imports = [subject + "CompletenessClaims", module]
        canonical_axioms = (f"\n#print axioms {subject}CompletenessClaims.completeReceipt\n"
                      f"#print axioms {module}.request0Receipt\n"
                      f"#print axioms {module}.request1Receipt")
    imports = [output + "." + suffix for suffix in
               (["Soundness", "Completeness"] if args.phase != "structure" else ["Sources", "Honest"])]
    imports += canonical_imports
    prefix = "\n".join("import " + item for item in imports)
    endpoints = ("#print axioms Soundness.rejected\n#print axioms Soundness.costs\n"
                 "#print axioms Completeness.compiled_ideal_complete\n"
                 "example : Soundness.budget = 16 := rfl" if args.phase != "structure" else "")
    endpoints += canonical_axioms
    generation.printer("FourAcceptance", f'''{prefix}
open ZkcSecurity.Examples.Generated.OriginalSecurity.FourSums
example : Sources.terminalTree = .and (.and (.leaf 0) (.leaf 1)) (.and (.leaf 2) (.leaf 3)) := rfl
example : ZkcSecurity.Examples.Generated.FourSums.validatorSites.length = 4 := by decide +kernel
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
def zeroReplies : PIR.Handler (ZkcSecurity.FiatShamir.NominalField.signature Rat "bls12-381.fr") Unit String
  | .receive _, _ => ⟨.returned 0, (), ["receive"]⟩
  | .query .., _ => ⟨.returned 0, (), ["query"]⟩
  | .deliver .., _ => ⟨.returned (), (), ["deliver"]⟩
set_option maxRecDepth 50000 in
example : ((Sources.presented (F := Rat) (G := Rat) [] [] [] [] 0 0 0 0 1 []).run zeroReplies ()).events.length = 16 := by
  simp [Sources.presented, composition, ZkcSecurity.Realizations.Sumcheck.OriginalRaw.sequence,
    Sources.calls, Sources.terminalTree, root, TableComponent.Execution.run, TableComponent.Execution.advance,
    terminal, PIR.Process.bind, PIR.Process.run, PIR.Execution.follow, zeroReplies,
    ZkcExamples.Structured.PrimitiveLibrary.HasShape, Zkc.Source.Structured.indexLimit]
#print axioms Sources.source_root
#print axioms Sources.bridge
#print axioms Honest.actual
{endpoints}
def main : IO Unit := IO.println "PASS four actual calls: {args.phase}"
''')
    (generation.directory / "acceptance.json").write_text(json.dumps({
        "calls": 4, "terminal": "balanced conjunction", "phase": args.phase,
        "generated": generation.generated,
        "commands": str(generation.directory / f"commands-{generation.run_id}.json")}, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--output", default=ROOT / "build/experiments/root-composition/four", type=Path)
    parser.add_argument("--resume", action="store_true",
                        help="reuse this output directory's exports and checked ABI; receipts also reuses body proofs")
    parser.add_argument("--dependency-path", action="append", type=Path, default=[])
    parser.add_argument("--phase", choices=["structure", "endpoints", "receipts", "all"], default="all")
    parser.set_defaults(check=False)
    check(parser.parse_args())
