#!/usr/bin/env python3
"""Regenerate actual sampled roots through the shared Lean assemblers.

Only source/model/theorem selections are configured in roots/sampled.toml.
All Lean outputs are checked in an isolated tree. No Lake build runs. Use
--check to compare generated files and --phase for a bounded incremental check.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"
sys.path.insert(0, str(LEAN))
from bridges.construction import pair  # noqa: E402
from bridges.structured import snapshot  # noqa: E402


def quoted(value):
    return json.dumps(value, ensure_ascii=False)


def validate_config(config):
    """Refuse malformed persisted descriptors before any generation starts."""
    def shape(value, required, optional, location):
        if not isinstance(value, dict):
            raise ValueError(f"{location}: expected a table")
        unknown = value.keys() - required - optional
        missing = required - value.keys()
        if unknown:
            raise ValueError(f"{location}: unknown keys: {', '.join(sorted(unknown))}")
        if missing:
            raise ValueError(f"{location}: missing keys: {', '.join(sorted(missing))}")

    def string(value, location):
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f"{location}: expected a nonempty string")

    strings = {"schema", "model_module", "model", "registry", "sampling", "field_type",
               "group_type", "capabilities"}
    lists = {"receipt_normalization", "theorem_normalization"}
    shape(config, strings | {"root"}, lists, "component roots")
    for key in strings:
        string(config[key], key)
    if config["schema"] != "zkc.component-roots/0":
        raise ValueError("unsupported component root configuration")
    for key in lists:
        values = config.get(key, [])
        if not isinstance(values, list):
            raise ValueError(f"{key}: expected a list of strings")
        for value in values:
            string(value, key)
    roots = config["root"]
    if not isinstance(roots, list) or not roots:
        raise ValueError("root: expected a nonempty list of tables")
    common = {"name", "source", "entry", "modules", "target", "method"}
    names = set()
    for index, root in enumerate(roots):
        location = f"root[{index}]"
        shape(root, common, {"error_bound", "error_expression", "proof_module", "proof_name",
                             "method_imports", "nonvacuity_law"}, location)
        for key in common - {"modules"}:
            string(root[key], f"{location}.{key}")
        method = root["method"]
        if method not in {"sigma", "direct"}:
            raise ValueError(f"{location}: uninstalled proof method: {method}")
        required = common | ({"proof_module", "error_bound", "error_expression"}
                             if method == "direct" else set())
        optional = {"proof_name"} if method == "direct" else {"method_imports", "nonvacuity_law"}
        shape(root, required, optional, location)
        for key in (required | optional) - {"modules", "method_imports"}:
            if key in root:
                string(root[key], f"{location}.{key}")
        method_imports = root.get("method_imports", [])
        if not isinstance(method_imports, list):
            raise ValueError(f"{location}.method_imports: expected a list of strings")
        for module in method_imports:
            string(module, f"{location}.method_imports")
        name = root["name"]
        if not name.isidentifier():
            raise ValueError(f"{location}: invalid root name: {name}")
        if name in names:
            raise ValueError(f"{location}: duplicate root name: {name}")
        names.add(name)
        modules = root["modules"]
        if not isinstance(modules, dict):
            raise ValueError(f"{location}.modules: expected a string map")
        for key, value in modules.items():
            string(key, f"{location}.modules key")
            string(value, f"{location}.modules.{key}")


def completeness_selection(root):
    """Serialize one Lean endpoint/request selection; never interpret a bound."""
    name = root["name"]
    error = (".zero" if root["method"] == "sigma" else
             "{ bound := " + quoted(root["error_bound"]) +
             ", expression := " + quoted(root["error_expression"]) + " }")
    return ("({ moduleName := " + quoted(f"ZkcSecurity.Examples.Generated.Components.{name}Completeness") +
            ", subjectModule := " + quoted(f"ZkcSecurity.Examples.Generated.{name}") +
            ", error := " + error + " } : RootCompleteness.Selection)")


class Generation:
    def __init__(self, args):
        self.args = args
        self.directory = args.output.resolve()
        self.directory.mkdir(parents=True, exist_ok=True)
        self.output = self.directory / "lib"
        self.output.mkdir(exist_ok=True)
        self.package = LEAN / "security"
        self.base = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                            cwd=self.package, text=True).strip()
        self.lean = subprocess.check_output(["lake", "env", "which", "lean"],
                                            cwd=self.package, text=True).strip()
        self.environment = dict(os.environ, LEAN_PATH=f"{self.output}:{self.base}",
                                LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "2"))
        self.commands = []
        self.run_id = str(time.time_ns())
        self.generated = []
        self.prepared = set()
        self.dependency_links = set()
        # An overlay also contains inherited cache links. Prefer every explicit
        # dependency's own checked objects before considering those inherited
        # links, which may name an older build of another supplied dependency.
        for root in args.dependency_path:
            self.overlay(Path(root).resolve(), self.output, owned_only=True)
        for root in [*args.dependency_path, *self.base.split(os.pathsep)]:
            self.overlay(Path(root).resolve(), self.output)

    def execute(self, command, cwd=ROOT):
        command = [str(item) for item in command]
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=self.environment,
                                text=True, capture_output=True)
        log = self.directory / f"command-{self.run_id}-{len(self.commands):03}.log"
        log.write_text(result.stdout + result.stderr)
        self.commands.append({"command": command, "cwd": str(cwd),
                              "returncode": result.returncode,
                              "elapsedSeconds": time.monotonic() - started,
                              "log": str(log)})
        (self.directory / f"commands-{self.run_id}.json").write_text(json.dumps(self.commands, indent=2) + "\n")
        (self.directory / "commands.json").write_text(json.dumps(self.commands, indent=2) + "\n")
        if result.returncode:
            lines = (result.stdout + result.stderr).splitlines()
            first = next((index for index, line in enumerate(lines)
                          if ": error" in line or line.startswith("error") or "fatal error" in line), 0)
            excerpt = "\n".join(lines[first:first + 40])[:4000]
            raise RuntimeError(f"{command[0]} failed (full output: {log}):\n" + excerpt)
        if "sorryAx" in result.stdout:
            raise RuntimeError("unfinished theorem in generated root")
        return result.stdout

    def overlay(self, source, target, *, owned_only=False):
        if not source.is_dir():
            return
        for item in source.iterdir():
            if owned_only and item.is_symlink():
                continue
            destination = target / item.name
            if destination in self.dependency_links:
                continue
            if not item.exists():
                continue
            if destination.is_symlink():
                if item.is_dir():
                    destination.unlink()
                    destination.mkdir()
                    self.overlay(item, destination, owned_only=owned_only)
                elif destination not in self.dependency_links:
                    same_link = destination.readlink() == item
                    if item.is_symlink():
                        same_link = same_link or destination.readlink() == item.readlink()
                    if not same_link and destination.resolve() != item.resolve():
                        destination.unlink()
                        destination.symlink_to(item.resolve())
                    self.dependency_links.add(destination)
            elif destination.is_dir() and item.is_dir():
                self.overlay(item, destination, owned_only=owned_only)
            elif not destination.exists():
                if item.is_dir():
                    destination.mkdir(parents=True)
                    self.overlay(item, destination, owned_only=owned_only)
                else:
                    destination.symlink_to(item.resolve())
                    self.dependency_links.add(destination)

    def module_path(self, module):
        package = self.package if module.startswith(("ZkcSecurity.", "TestsSecurity.")) else LEAN
        return package.joinpath(*module.split(".")).with_suffix(".lean")

    def compile(self, module, source=None, run=False, source_root=None):
        # Merge cached namespaces because Lean resolves each namespace from
        # one search root. All own output artifacts replace symlinks first.
        source = source or self.module_path(module)
        target = self.output.joinpath(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        for artifact in target.parent.glob(target.stem + ".*"):
            if artifact.is_symlink():
                artifact.unlink()
        package = self.package if source.is_relative_to(self.package) else LEAN
        flags = ([f"--root={source_root}"] if source_root is not None else
                 [] if source.is_relative_to(package) else [f"--root={source.parent}"])
        command = [self.lean, "-j2", "-M16384", "-DwarningAsError=true", *flags]
        command += ["--run", source] if run else ["-o", target, source]
        print(f"Checking {module}", flush=True)
        return self.execute(command, package)

    def retain(self, module, text):
        path = self.module_path(module)
        if self.args.check:
            if not path.is_file() or path.read_text() != text:
                raise RuntimeError(f"generated source differs: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.generated.append(str(path.relative_to(ROOT)))
        self.compile(module)

    def printer(self, name, source):
        path = self.directory / f"{name}.lean"
        path.write_text(source)
        return self.compile(name, path, run=True)

    def prepare(self, modules):
        for module in modules:
            if module not in self.prepared:
                self.compile(module)
                self.prepared.add(module)

    def export(self, root):
        name = root["name"]
        directory = self.directory / name
        directory.mkdir(exist_ok=True)
        flags = ["--source-format=zkc", "--entry=" + root["entry"],
                 "--module=example=" + root["source"],
                 *["--module=" + key + "=" + value for key, value in root["modules"].items()]]
        def native(*args):
            return self.execute([self.args.compiler, *args])
        original = native("language-emit", *flags)
        (directory / "original.mlir").write_text(original)
        interface_text = native("language-interface", *flags)
        interface = json.loads(interface_text)
        (directory / "interface.json").write_text(interface_text)
        bundle_text = native("language-bundle", *flags)
        bundle = json.loads(bundle_text)
        (directory / "deployment.json").write_text(bundle_text)
        source_digest = hashlib.sha256(original.encode()).hexdigest()
        if interface["original"] != source_digest or bundle[1] != source_digest:
            raise RuntimeError("root interface or deployment identifies different source bytes")
        (directory / "source-claims.json").write_text(native("language-check", *flags, "--source-claims"))
        policy = bundle[2][1]
        (directory / "policy.json").write_text(json.dumps(policy))
        candidate = native("protocol-construct-proof", directory / "original.mlir", directory / "policy.json")
        (directory / "candidate.mlir").write_text(candidate)
        arguments = [directory / "original.mlir", directory / "policy.json", directory / "candidate.mlir"]
        exported = native("protocol-constructed-pair", *arguments)
        (directory / "pair.json").write_text(exported)
        children = json.loads(exported)
        individual = {}
        for role, child in zip(("producer", "validator"), children[1:]):
            text = native("protocol-constructed-participant", *arguments, "--role=" + role)
            if json.loads(text) != child:
                raise RuntimeError("individual export differs from retained pair")
            individual[role] = text
            (directory / (role + ".json")).write_text(text)
            (directory / (role + ".identity")).write_text(text)
        source = native("protocol-structured", directory / "original.mlir", "--symbol=" + policy[1])
        (directory / "source.json").write_text(source)
        for module, text in [
                (f"ZkcExamples.Structured.Generated.Bindings.{name}Data",
                 snapshot.render(json.loads(source), f"ZkcExamples.Structured.Generated.Bindings.{name}Data")),
                (f"ZkcExamples.Construction.Generated.{name}Pair",
                 pair.render(children, f"ZkcExamples.Construction.Generated.{name}Pair"))]:
            self.retain(module, text)
        identities = {key: "sha256:" + hashlib.sha256(value.encode()).hexdigest()
                      for key, value in dict(original=source, **individual).items()}
        (directory / "identities.json").write_text(json.dumps(identities, indent=2) + "\n")

    def assemble(self, root, config):
        self.prepare(["ZkcTools.StructuredSource.Root",
                      "ZkcTools.ConstructionBindings.Generate"])
        name = root["name"]
        directory = self.directory / name
        identities = json.loads((directory / "identities.json").read_text())
        data = f"ZkcExamples.Structured.Generated.Bindings.{name}Data"
        inputs = data.removesuffix("Data") + "Inputs"
        pair_module = f"ZkcExamples.Construction.Generated.{name}Pair"
        subject = f"ZkcSecurity.Examples.Generated.{name}"
        producer = f"ZkcExamples.Structured.Generated.Constructed.{name}Producer"
        validator = producer.removesuffix("Producer") + "Validator"
        connection = f"ZkcExamples.Structured.Generated.Connections.{name}"
        # Printers write into scratch. retain() owns comparisons and writes.
        paths = {module: directory.joinpath(*module.split(".")).with_suffix(".lean")
                 for module in (inputs, producer, validator, connection, subject)}
        for path in paths.values():
            path.parent.mkdir(parents=True, exist_ok=True)
        self.printer("Assemble" + name, f'''import ZkcTools.StructuredSource.Bindings.Inputs
import ZkcTools.StructuredSource.Constructed
import ZkcTools.StructuredSource.Root
import ZkcTools.ConstructionBindings.Generate
import {data}
import {pair_module}
open Zkc.Source.Structured ZkcTools.StructuredSource
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
def program : Program := (check {data}.snapshot).toOption.get (by decide +kernel)
def main : IO Unit := do
  IO.FS.writeFile {quoted(str(paths[inputs]))} (Bindings.inputsSource program {quoted(inputs)} {quoted(data)})
  for (moduleName, artifactExpression, artifact, path) in [
    ({quoted(producer)}, {quoted(pair_module+'.Producer.participant')}, {pair_module}.Producer.participant, {quoted(str(paths[producer]))}),
    ({quoted(validator)}, {quoted(pair_module+'.Validator.participant')}, {pair_module}.Validator.participant, {quoted(str(paths[validator]))})] do
    match Constructed.source artifact {{moduleName, artifactModule := {quoted(pair_module)}, artifactExpression}} with
    | .error reason => throw (IO.userError reason)
    | .ok source => IO.FS.writeFile path source
  let .ok connection := ZkcTools.ConstructionBindings.Generate.source
    {{ sourceModule := {quoted(inputs)}.toName, program := {quoted(inputs + '.program')}.toName }}
    {{ moduleName := {quoted(connection)}.toName, participants := [
      {{ mode := .producer, artifactModule := {quoted(pair_module)}.toName,
         artifact := {quoted(pair_module + '.Producer.participant')}.toName,
         viewModule := {quoted(producer)}.toName }},
      {{ mode := .validator, artifactModule := {quoted(pair_module)}.toName,
         artifact := {quoted(pair_module + '.Validator.participant')}.toName,
         viewModule := {quoted(validator)}.toName }}] }}
    | throw (IO.userError "connection proposal refused")
  IO.FS.writeFile {quoted(str(paths[connection]))} connection
  IO.FS.writeFile {quoted(str(paths[subject]))} (Root.fixedSubjectSource {{
    connectionModule := {quoted(connection)},
    moduleName := {quoted(subject)}, sourceModule := {quoted(inputs)},
    originalExpression := {quoted(data+'.snapshot')}, importedExpression := {quoted(inputs+'.imported')},
    pairModule := {quoted(pair_module)}, artifactsExpression := {quoted(pair_module+'.artifacts')},
    modelModule := {quoted(config['model_module'])}, modelExpression := {quoted(config['model'])},
    registryExpression := {quoted(config['registry'])},
    targetName := {quoted(root['target'])},
    originalExportExpression := {quoted(quoted(identities['original']))},
    producerExportExpression := {quoted(quoted(identities['producer']))},
    validatorExportExpression := {quoted(quoted(identities['validator']))} }})
''')
        for module in (inputs, producer, validator, connection, subject):
            self.retain(module, paths[module].read_text())
        self.prepare(["ZkcSecurity.Generation.SubjectABI",
                      "ZkcSecurity.Generation.SubjectABI.Command"])
        abi = f"ZkcSecurity.Examples.Generated.Components.{name}ABI"
        abi_path = directory / "ABI.lean"
        self.printer("GenerateABI" + name, f'''import ZkcSecurity.Generation.SubjectABI.Command
import {subject}
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
open ZkcSecurity.Generation.SubjectABI
derive_subject_abi generated for {subject}.subject
  module {quoted(abi)} from {quoted(subject)}
def main : IO Unit := IO.FS.writeFile {quoted(str(abi_path))} generated
''')
        self.retain(abi, abi_path.read_text())

    def prove(self, root, config):
        name = root["name"]
        self.prepare(["ZkcSecurity.Generation.RootCompleteness"])
        module = f"ZkcSecurity.Examples.Generated.Components.{name}Completeness"
        output = self.directory / name / "Completeness.lean"
        if root["method"] == "direct":
            self.compile(root["proof_module"])
            proof = root.get("proof_name", root["proof_module"] + ".compiled_ideal_complete")
            self.printer("GenerateCompleteness" + name, f'''import ZkcSecurity.Generation.RootCompleteness
open ZkcSecurity.Generation
def main : IO Unit := IO.FS.writeFile {quoted(str(output))} (RootCompleteness.directSource
  {completeness_selection(root)} {quoted(root['proof_module'])} {quoted(proof)}
  {quoted(config['sampling'])} ["ZkcSecurity.Domains.PrimeField"])
''')
            self.retain(module, output.read_text())
            return
        self.prepare(root.get("method_imports", []))
        self.prepare([
            "Zkc.Construction.ProcessViewTactic", "ZkcSecurity.Families.Sigma.Algebra",
            "ZkcSecurity.Families.Sigma.Realization", "ZkcSecurity.Tools.SigmaReadback",
            "ZkcSecurity.Generation.UniformRoot",
            "ZkcSecurity.Generation.SigmaCompleteness", "ZkcSecurity.Generation.SigmaCompleteness.Command"])
        subject = f"ZkcSecurity.Examples.Generated.{name}"
        self.printer("GenerateCompleteness" + name, f'''import ZkcSecurity.Generation.SigmaCompleteness.Command
import {subject}
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
open ZkcSecurity.Generation
derive_sigma_completeness generated from {{
  metadata := SubjectABI.metadata {subject}.subject
  imports := [{', '.join(map(quoted, root.get('method_imports', [])))}]
  nonvacuityLaw := {('some ' + quoted(root['nonvacuity_law'])) if 'nonvacuity_law' in root else 'none'}
  output := {{
    moduleName := {quoted(module)}, subjectModule := {quoted(subject)},
    producerModule := "ZkcExamples.Structured.Generated.Constructed.{name}Producer",
    validatorModule := "ZkcExamples.Structured.Generated.Constructed.{name}Validator",
    abiModule := "ZkcSecurity.Examples.Generated.Components.{name}ABI",
    fieldType := {quoted(config['field_type'])}, groupType := {quoted(config['group_type'])},
    sampling := {quoted(config['sampling'])} }} }}
def main : IO Unit := IO.FS.writeFile {quoted(str(output))} generated
''')
        self.retain(module, output.read_text())

    def receipt(self, root, config):
        self.prepare(["ZkcSecurity.Generation.RootCompleteness"])
        name = root["name"]
        subject = f"ZkcSecurity.Examples.Generated.{name}"
        module = subject + "CompletenessClaims"
        output = self.directory / name / "CompletenessClaims.lean"
        self.printer("GenerateReceipt" + name, f'''import ZkcSecurity.Generation.RootCompleteness
open ZkcSecurity.Generation
def main : IO Unit := IO.FS.writeFile {quoted(str(output))} (RootCompleteness.claimsSource
  {completeness_selection(root)} {{
  normalization := [{', '.join(map(quoted, config.get('receipt_normalization', [])))}],
  theoremNormalization := [{', '.join(map(quoted, config.get('theorem_normalization', [])))}],
  capabilities := {quoted(config['capabilities'])} }})
''')
        self.retain(module, output.read_text())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--config", type=Path, default=Path(__file__).parent / "roots/sampled.toml")
    parser.add_argument("--output", type=Path, default=ROOT / "build/lean/component-roots")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--dependency-path", type=Path, action="append", default=[],
                        help="additional prechecked Lean dependency tree (repeatable)")
    parser.add_argument("--only", action="append", default=[])
    parser.add_argument("--phase", choices=["all", "export", "assembly", "proof", "receipt"], default="all")
    args = parser.parse_args(argv)
    config = tomllib.loads(args.config.read_text())
    validate_config(config)
    roots = [root for root in config["root"] if not args.only or root["name"] in args.only]
    if not roots or any(name not in [root["name"] for root in roots] for name in args.only):
        raise ValueError("unknown or empty root selection")
    generation = Generation(args)
    phases = ["export", "assembly", "proof", "receipt"] if args.phase == "all" else [args.phase]
    for root in roots:
        for phase in phases:
            if phase == "export":
                generation.export(root)
            else:
                getattr(generation, {"assembly": "assemble", "proof": "prove", "receipt": "receipt"}[phase])(root, config)
    (generation.directory / ("generated-inventory-" + generation.run_id + ".json")).write_text(json.dumps({
        "generated": generation.generated, "roots": [root["name"] for root in roots],
        "sharedLakeBuilds": 0,
        "nativeExportSeconds": sum(command["elapsedSeconds"] for command in generation.commands
                                   if command["command"][0] != generation.lean),
        "printerSeconds": sum(command["elapsedSeconds"] for command in generation.commands
                              if command["command"][0] == generation.lean and "--run" in command["command"]),
        "moduleCheckSeconds": sum(command["elapsedSeconds"] for command in generation.commands
                                  if command["command"][0] == generation.lean and "--run" not in command["command"]),
        "checkingSeconds": sum(command["elapsedSeconds"] for command in generation.commands
                               if command["command"][0] == generation.lean)}, indent=2) + "\n")
    print("Selected source roots generated and checked.")


if __name__ == "__main__":
    main()
