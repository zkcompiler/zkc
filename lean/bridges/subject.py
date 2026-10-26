#!/usr/bin/env python3
"""Check (or regenerate) verification subjects from their manifests.

For each manifest in `lean/subjects` (or each `--subject`), the driver runs one
pipeline, with no step specific to a subject:

1. compile and export: the proof Entry's original MLIR, language interface,
   native deployment, Entry package, constructed candidate, constructed
   validator and original snapshot, declared variants, and the interactive
   Entry's snapshot;
2. regenerate every generated module the manifest owns, through the shared
   renderer library, printed Bodies and generated Views included, and require
   the committed modules to equal them (`--write` rewrites them first);
3. regenerate the per-Entry glue and executable facts, which the kernel checks
   when built; check and build the requested normal-form module before deriving
   dependent construction, executable or claim receipts;
4. run the kernel checks on the fresh exports: the composed construction and
   projection check (or the construction rule alone), the occurrence-template
   encoding and the lowering rule;
5. apply the manifest's generic mutation kinds to the fresh exports, the native
   candidate and the validator program, and require each applicable one to be
   refused by its stage (or accepted, for a change the rule does not read); a
   helper body's copy is refused by the helper rule and accepted by the
   lowering rule;
6. with `--runtime`, run the runtime verifier on an honest proof at every
   instruction budget up to one past the threshold the Lean charge derives
   (evaluated after every generated module is regenerated and built) and
   on generic proof edits, and require its observations to equal those the Lean
   executable meaning predicts; check the axiom closures and proof dependencies
   the manifest's receipt names and that the runtime executes exactly the
   program the receipt names;
7. regenerate configured artifact/request modules and build typed Lean
   resolution, evaluation and registered-method receipts. Source spec/verify
   and typed Lean exports select meanings; manifests configure physical files;
8. write a per-subject evidence record: artifact and module digests, kernel
   results, mutation outcomes, runtime summary and requested assumptions.

This is bounded agreement evidence for the stated trusted links: the
exporters, the renderers, the runtime and its kernels.
"""

import argparse
import copy
import json
from pathlib import Path
import re
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
sys.path.append(str(LEAN))
sys.path.append(str(ROOT / "scripts"))

from bridges.common.lean_render import (  # noqa: E402
    ALLOWED_AXIOMS, Refused, Runner, axioms_allowed, digest, file_digest, now, printed_axioms,
    regenerate, require, strip_header)
from bridges.construction import render as constructed  # noqa: E402
from bridges.executable import render as executable  # noqa: E402
from bridges.pipeline import compile as pipeline_compile, evidence, glue, manifest, mutations, runtime  # noqa: E402
from bridges.pipeline.source_claims import canonical  # noqa: E402
from bridges.structured import bodies as printer, snapshot as structured  # noqa: E402

BODIES = ROOT / "lean/bridges/structured/bodies.py"
NORMAL_FORMS = ROOT / "lean/bridges/structured/normal_forms.py"
# Example-namespace theorems are Entry-specific. Among those a proof reaches, the
# walk lists every equation between processes (`PIR.Process`), whether the kernel
# checks it by evaluation (`rfl`), and whether its statement names a meaning of a
# compiled program. Derived artifact/source connections are recorded separately
# from evaluated original-side normal forms.
ENTRY_PREFIXES = ["ZkcExamples", "ZkcSecurity.Examples"]
COMPILED_MEANINGS = [
    "Zkc.Construction.spec", "Zkc.Construction.specK", "Zkc.Construction.ideal", "Zkc.Construction.idealK",
    "Zkc.Construction.Domain.participant", "Zkc.Construction.Domain.run",
    "Zkc.Construction.Domain.validate", "Zkc.Construction.Domain.step",
    "Zkc.Construction.Domain.evaluate", "Zkc.Construction.ScalarVerifier.verify",
    "Zkc.Construction.Uniform.DomainAdapter.validate",
    "Zkc.Executable.execute", "Zkc.Executable.validate", "Zkc.Executable.metered",
]


def record_accepted(record, name, **detail):
    """Record one kernel or native check of the actual artifacts as accepted: a
    failed check stops the run before its record is written."""
    record["checks"].append(dict(name=name, outcome="accepted", **detail))


class Driver(Runner):
    def __init__(self, args):
        super().__init__()
        self.args = args
        self.output = args.output
        self.evidence = {}
        self.built = set()
        self.registry_entries = {}

    # Directories, Lean and generated files.

    def directory(self, subject, *parts):
        path = self.output.joinpath(subject.name, *parts)
        path.mkdir(parents=True, exist_ok=True)
        return path

    def lake(self, *arguments, cwd=LEAN, name, expect=0):
        return self.run([self.args.lake, *arguments], cwd=cwd, name=name, expect=expect)

    def registry(self, package="security"):
        """The assumption registry of the security integration: identifier to
        category and statement, read from the selected physical package registry."""
        if package not in self.registry_entries:
            optional = package == "arklib"
            module = "ZkcArkLib.Registry" if optional else "ZkcSecurity.Registry"
            table = module + (".reportTable" if optional else ".table")
            cwd = LEAN / "integrations/arklib" if optional else LEAN / "security"
            result = self.evaluate(
                self.output / f"Registry-{package}.lean",
                f"import {module}\n\n"
                f"#eval for (identifier, category, _, statement) in {table} do\n"
                "  IO.println s!\"ENTRY\\t{identifier}\\t{category}\\t{statement}\"\n",
                cwd=cwd, name=f"registry:{package}")
            entries = {}
            for line in result.stdout.splitlines():
                if line.startswith("ENTRY\t"):
                    _, identifier, category, statement = line.split("\t", 3)
                    self.check(f"registry-unique:{identifier}", identifier not in entries,
                               f"duplicate assumption registry identifier: {identifier}")
                    entries[identifier] = dict(category=category, statement=statement)
            self.check("registry-read", bool(entries), result.stdout[-400:])
            self.registry_entries[package] = entries
        return self.registry_entries[package]

    def build(self, *modules, cwd=LEAN):
        """Build Lean modules of the package at `cwd`: their kernel checks."""
        wanted = [module for module in modules if module and (str(cwd), module) not in self.built]
        if wanted:
            self.lake("build", *wanted, cwd=cwd, name="lake-build:" + ",".join(wanted))
            self.built.update((str(cwd), module) for module in wanted)

    def evaluate(self, path, source, *, cwd, name, expect=0):
        """Lake builds the file's imports and applies its owning package options."""
        path.write_text(source, encoding="utf-8")
        return self.lake("lean", path, cwd=cwd, name=name, expect=expect)

    def lean(self, subject, name, source, cwd=LEAN, expect=0):
        return self.evaluate(self.directory(subject) / name, source, cwd=cwd, name=f"{subject.name}:{name}",
                             expect=expect)

    def generated(self, subject, key, text, record):
        path = subject.generated(key)
        before = path.read_text(encoding="utf-8") if path.exists() else None
        regenerate(self, path, text, self.args.write)
        if before != text:
            # A rewritten module invalidates every build that may have read it.
            self.built.clear()
        record["generated"][str(path.relative_to(ROOT))] = dict(sha256=digest(text.encode()), role=key)

    # 1-3. Interactive Entry.

    def interactive(self, subject, record):
        artifacts = pipeline_compile.interactive_entry(self, subject, self.args.compiler,
                                                       self.directory(subject, "interactive"))
        modules = record
        if subject.generated("interactive_source"):
            self.generated(subject, "interactive_source", artifacts["source"], modules)
        if subject.generated("interactive_export"):
            self.generated(subject, "interactive_export", artifacts["export_text"], modules)
        data = subject.module_name("interactive_data")
        if data:
            self.generated(subject, "interactive_data", structured.render(artifacts["snapshot"], data), modules)
        bodies = subject.module_name("interactive_bodies")
        if bodies:
            names = glue.body_names(artifacts["snapshot"], subject.get("bodies", "interactive_entry"))
            self.build(data)
            text, helpers, protocols = printer.printed_module(data, bodies, subject.get("bodies", "closed", False),
                                                              names, self, self.args.lake,
                                                              fresh=self.args.fresh_bodies)
            self.generated(subject, "interactive_bodies", text, modules)
            views = subject.module_name("interactive_views")
            if views:
                self.generated(subject, "interactive_views",
                               glue.views_module(views, data, bodies, helpers, protocols), modules)
                self.build(views)
                record_accepted(record, "interactive-admission", module=views)
        record["artifacts"].update(interactive_source="sha256:" + digest(artifacts["source"].encode()),
                                   interactive_export="sha256:" + digest(artifacts["export_text"].encode()))
        record["interactive"] = dict(entry=subject.get("entries", "interactive"))
        return artifacts

    # 1-5. Proof Entry.

    def proof(self, subject, record):
        executable_profile = subject.profile("executable")
        artifacts = pipeline_compile.proof_entry(self, subject, self.args.compiler, self.directory(subject, "proof"),
                                                 executable_profile)
        modules = record
        if subject.generated("original_export"):
            self.generated(subject, "original_export", artifacts["original_text"], modules)
        data, participant = subject.module_name("data"), subject.module_name("participant")
        self.generated(subject, "data", structured.render(artifacts["original"], data), modules)
        self.generated(subject, "participant", constructed.render(artifacts["exported"], participant), modules)
        entry = glue.Entry(artifacts["original"], artifacts["exported"], artifacts["interface"])
        names = {"glue": subject.construction_namespace, "data": data, "participant": participant}
        admission = subject.get("construction", "admission", "views")
        if subject.generated("bodies"):
            bodies = subject.module_name("bodies")
            body_names = glue.body_names(artifacts["original"], subject.get("bodies", "entry"))
            self.build(data)
            text, helpers, protocols = printer.printed_module(data, bodies, False, body_names, self, self.args.lake,
                                                              fresh=self.args.fresh_bodies)
            self.generated(subject, "bodies", text, modules)
            names.update(bodies=bodies, helpers=helpers, protocols=protocols)
        if admission != "views":
            names.pop("bodies", None)
        if subject.generated("glue"):
            self.generated(subject, "glue", glue.construction_glue(subject, entry, names), modules)
            self.build(subject.module_name("glue"))
        record["artifacts"].update(
            source="sha256:" + digest(artifacts["source"]),
            original_export="sha256:" + digest(artifacts["original_text"].encode()),
            constructed_candidate=artifacts["exported"][2],
            constructed_candidate_text="sha256:" + digest(artifacts["candidate"].encode()),
            constructed_export="sha256:" + digest(artifacts["export_text"].encode()),
            deployment="sha256:" + digest(artifacts["deployment_text"].encode()))
        if executable_profile:
            record["artifacts"].update(program="sha256:" + digest(artifacts["program"]),
                                       package="sha256:" + digest(artifacts["package_bytes"]))
        record["proof"] = dict(entry=subject.get("entries", "proof"), policy=artifacts["policy"])
        record["source_claims"] = artifacts["source_claims"]
        record_accepted(record, "source-claims-artifact-binding",
                        export_digest=artifacts["source_claims"]["native_export_digest"])
        record_accepted(record, "native-constructed-candidate")
        if subject.generated("glue"):
            record_accepted(record, "per-entry-glue", module=subject.module_name("glue"))
        record["kernel"] = {}
        self.construction_rule(subject, artifacts, record)
        self.native_refusals(subject, artifacts, record)
        return artifacts, entry

    def construction_rule(self, subject, artifacts, record):
        """The composed Lean check on the fresh export and on generic mutations."""
        exported, original = artifacts["exported"], artifacts["original"]
        rule = subject.get("construction", "rule", "compiled")
        glue_module = subject.module_name("glue")
        glue_namespace = subject.construction_namespace
        data = subject.module_name("data")
        kinds = [item for item in mutations.kinds_for(subject.get("mutations", "kinds", []))
                 if item[1].stage == "construction"]

        def templates(instructions):
            for item in mutations.nested(instructions):
                if item[0] in (mutations.OBSERVE, mutations.CHALLENGE):
                    yield list(bytes.fromhex(dict(item[1])["parameters"][1][0]))

        parts = [f"import {glue_module}", "import Zkc.Construction.Encoding", "set_option maxRecDepth 20000",
                 strip_header(structured.render(original, "Fresh.Original")),
                 strip_header(constructed.render(exported, "Fresh.Actual")),
                 "/-- Whether a check refuses with a code of the given rule. -/\n"
                 "def refusedBy (rule : String) : Except String Unit → Bool\n"
                 "  | .error code => code.startsWith rule\n  | .ok _ => false"]
        evaluations = []
        encoded = json.dumps(list(templates(exported[7])))
        proofs = [f"theorem original_retained : Fresh.Original.snapshot = {data}.snapshot := rfl",
                  "theorem templates_encoded : (Zkc.Construction.Instruction.templatesList "
                  "Fresh.Actual.participant.instructions).map (fun template => "
                  f"(Zkc.Construction.templateTree template).encode) = {encoded} := by decide +kernel"]
        if rule == "compiled":
            imported = f"{glue_namespace}.imported"
            proofs += ["/-- The retained original's admission, for the fresh original. -/\n"
                       "def freshImported : Zkc.Source.Structured.Imported Fresh.Original.snapshot :=\n"
                       f"  ⟨{imported}.program, by rw [original_retained]; exact {imported}.admitted⟩",
                       "theorem actual_accepted : Zkc.Construction.checkCompiled freshImported "
                       "Fresh.Actual.participant = .ok () := by decide +kernel",
                       "theorem actual_selected : Zkc.Construction.checkSelection freshImported "
                       "Fresh.Actual.participant = true := by decide +kernel"]
        else:
            proofs.append("theorem actual_accepted : Zkc.Construction.checkExport Fresh.Original.snapshot "
                          "Fresh.Actual.participant = .ok () := by decide +kernel")
        outcomes = {}
        index = 0
        for name, kind, function in kinds:
            if rule != "compiled" and kind.refusing_rule != "construction-":
                # Without the projection rule, only the construction rule's obligations apply.
                outcomes[name] = dict(stage=kind.stage, property=kind.property, expected=kind.expected, sites=[],
                                      applicable=False, reason="the projection rule is not applied to this Entry")
                continue
            copies = function(exported)
            sites = []
            for value in copies:
                namespace = f"Fresh.Mutation{index}"
                try:
                    rendered = constructed.render(value, namespace)
                except Refused as error:
                    sites.append(dict(site=len(sites), applicable=False, reason=f"malformed: {error}"))
                    continue
                self.check(f"{subject.name}:mutation-differs:{name}:{len(sites)}", value != exported)
                parts.append(strip_header(rendered))
                if kind.construction_accepts:
                    proofs.append(f"/-- {name} -/\ntheorem mutation{index}_construction_accepted : "
                                  f"Zkc.Construction.checkExport Fresh.Original.snapshot {namespace}.participant "
                                  "= .ok () := by decide +kernel")
                checked = (f"Zkc.Construction.checkCompiled freshImported {namespace}.participant" if rule == "compiled"
                           else f"Zkc.Construction.checkExport Fresh.Original.snapshot {namespace}.participant")
                proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : refusedBy \"{kind.refusing_rule}\" "
                              f"({checked}) = true := by decide +kernel")
                evaluations.append(f'#eval IO.println ("mutation {index} " ++ (repr ({checked})).pretty 1000)')
                sites.append(dict(site=len(sites), applicable=True, theorem=f"mutation{index}_refused", index=index,
                                  refusing_rule=kind.refusing_rule, construction_accepts=kind.construction_accepts))
                index += 1
            outcomes[name] = dict(stage=kind.stage, property=kind.property, expected=kind.expected,
                                  sites=sites, applicable=any(site["applicable"] for site in sites))
        proofs.append("#print axioms actual_accepted")
        result = self.lean(subject, "FreshExport.lean", "\n\n".join(parts + proofs + evaluations) + "\n")
        self.check(f"{subject.name}:lean-rule", axioms_allowed(result.stdout, "actual_accepted"),
                   result.stdout[-400:])
        codes = dict(re.findall(r"^mutation (\d+) Except\.error \"([^\"]*)\"$", result.stdout, re.M))
        for name, outcome in outcomes.items():
            for site in outcome["sites"]:
                if site["applicable"]:
                    site["code"] = codes.get(str(site["index"]))
                    self.check(f"{subject.name}:mutation-code:{name}:{site['site']}", site["code"] is not None,
                               result.stdout[-400:])
            outcome["refused"] = sum(1 for site in outcome["sites"] if site["applicable"])
        axioms = printed_axioms(result.stdout).get("actual_accepted")
        record["kernel"]["construction"] = dict(rule=rule, file="FreshExport.lean", accepted=True, axioms=axioms)
        record_accepted(record, "construction-and-projection" if rule == "compiled" else "construction", axioms=axioms)
        if rule == "compiled":
            record_accepted(record, "selection")
        record_accepted(record, "occurrence-encoding")
        record.setdefault("mutations", {}).update(outcomes)

    def native_refusals(self, subject, artifacts, record):
        """The native checker refuses mutated candidates before any export."""
        directory = self.directory(subject, "proof")
        for name, kind, function in mutations.kinds_for(subject.get("mutations", "kinds", [])):
            if kind.stage != "native":
                continue
            copies = function(artifacts["candidate"], artifacts["exported"])
            sites = []
            for index, text in enumerate(copies):
                self.check(f"{subject.name}:mutation-differs:{name}:{index}", text != artifacts["candidate"])
                path = directory / f"candidate-{name}-{index}.mlir"
                path.write_text(text)
                result = self.run([self.args.compiler, "protocol-constructed-participant", directory / "source.mlir",
                                   directory / "policy.json", path], expect=None,
                                  name=f"{subject.name}:native-refusal:{name}")
                reason = result.stderr.strip().splitlines()[-1] if result.stderr.strip() else ""
                self.check(f"{subject.name}:native-refusal:{name}:{index}",
                           result.returncode > 0 and reason == kind.expected, result.stderr[-400:])
                sites.append(dict(site=index, applicable=True, reason=reason))
            record.setdefault("mutations", {})[name] = dict(
                stage=kind.stage, property=kind.property, expected=kind.expected, sites=sites,
                applicable=bool(sites), refused=len(sites))

    # 4-6. Executable validator.

    def executable(self, subject, artifacts, entry, record):
        deployment = artifacts["deployment"]
        modules = record
        program = subject.module_name("program")
        self.generated(subject, "program", executable.render(deployment, program), modules)
        self.build(program)
        facts = self.lowering_rule(subject, artifacts, entry, record)
        if subject.generated("facts"):
            form = subject.get("construction", "inputs", "values")
            construction = dict(names=entry.names, types=entry.types, glue=subject.construction_namespace,
                                module=subject.module_name("glue"))
            # The facts are declared in the namespace the Entry's hand executable module
            # continues, so that its names are the facts' own declarations.
            namespace = subject.get("executable", "namespace") or subject.module_name("facts")
            self.generated(subject, "facts", glue.facts_module(namespace, construction, program, facts, form),
                           modules)
            self.build(subject.module_name("facts"))
        self.threshold(subject, facts, record)
        return facts

    def threshold(self, subject, facts, record):
        """The acceptance threshold the Lean charge derives: the static total charge,
        or the manifest's charge function at the public inputs it names. The charge is
        evaluated only now, once every generated module of the subject is regenerated,
        and every module the evaluation imports, the hand proofs included, is built
        first."""
        charge = subject.get("executable", "charge")
        threshold = facts["total"]
        if charge:
            public = json.loads(subject.inputs(subject.get("entries", "proof"), "public").read_text())
            arguments = " ".join(str(int(public[name])) for name in subject.get("executable", "charge_arguments", []))
            module = subject.get("executable", "completeness_module") or charge.rsplit(".", 1)[0]
            result = self.lean(subject, "FreshCharge.lean",
                               f"import {module}\n\n#eval IO.println (\"charge \" ++ toString ({charge} {arguments}))\n")
            found = [line.removeprefix("charge ") for line in result.stdout.splitlines() if line.startswith("charge ")]
            self.check(f"{subject.name}:lean-evaluated:charge", len(found) == 1, result.stdout[-400:])
            threshold = int(found[0])
        self.check(f"{subject.name}:threshold-derived", threshold is not None,
                   "the Lean charge of a complete run is not static and the manifest names no charge function")
        if subject.get("executable", "threshold", "derived") != "derived":
            self.check(f"{subject.name}:threshold-declared", int(subject.get("executable", "threshold")) == threshold)
        record["kernel"]["lowering"]["threshold"] = threshold
        facts["threshold"] = threshold
        return threshold

    def lowering_rule(self, subject, artifacts, entry, record):
        deployment, exported = artifacts["deployment"], artifacts["exported"]
        glue_module = subject.module_name("glue")
        glue_namespace = subject.construction_namespace
        # Only the generated glue and the rules: the charge, whose module reads the
        # generated facts and the hand proofs, is evaluated after they are rebuilt.
        parts = ["import Zkc.Executable.Installed", "import Zkc.Executable.Reading",
                 "import Zkc.Executable.Helpers", "import Zkc.Construction.Participant", f"import {glue_module}"]
        parts += ["set_option maxRecDepth 20000",
                  strip_header(constructed.render(exported, "Fresh.Constructed")),
                  strip_header(executable.render(deployment, "Fresh.Actual")),
                  *[strip_header(executable.render(variant, f"Fresh.{name}"))
                    for name, variant in artifacts["variants"].items()],
                  "open Zkc.Construction Zkc.Executable",
                  "def refusal : Except Refusal Lowered → Option Refusal\n"
                  "  | .error refusal => some refusal\n  | .ok _ => none",
                  "def exact (lowered : Except Refusal Lowered) : Option Bool :=\n"
                  "  lowered.toOption.map (fun lowered => decide (Code.instructionList lowered.code = "
                  "Fresh.Constructed.participant.instructions))",
                  "def helperAccepted : Except HelperRefusal Unit → Bool\n"
                  "  | .ok () => true\n  | .error _ => false",
                  "def helperOutcome : Except HelperRefusal Unit → String\n"
                  "  | .ok () => \"none\"\n  | .error refusal => (repr refusal).pretty 1000000"]
        selected = self.role_map(subject, deployment)
        proofs = ["theorem actual_accepted : refusal (checkLowering installed Fresh.Constructed.participant "
                  "Fresh.Actual.validator) = none := by decide +kernel",
                  # The runtime decides acceptance at its role map's index; the theorems read the
                  # committed acceptance position and bind data inputs in policy order.
                  f"theorem acceptance_position : {glue_namespace}.acceptancePosition = "
                  f"{int(selected['acceptance'])} := by decide +kernel",
                  f"theorem public_inputs : {glue_namespace}.participant.policy.publicInputs = "
                  f"[{', '.join(str(int(port)) for port in selected['data_inputs'])}] := by decide +kernel"]
        for name in artifacts["variants"]:
            proofs.append(f"theorem variant_{name}_accepted : refusal (checkLowering installed "
                          f"Fresh.Constructed.participant Fresh.{name}.validator) = none := by decide +kernel")
        # Facts Lean evaluates for the generated facts module.
        lowered = "(checkLowering installed Fresh.Constructed.participant Fresh.Actual.validator)"
        evaluations = [
            f'#eval IO.println ("total " ++ toString ({lowered}.toOption.bind (·.total?)))',
            f'#eval IO.println ("receives " ++ (repr ({lowered}.toOption.bind (fun l => Plan.static l.plan))).pretty 1000000)',
            '#eval IO.println ("helpers " ++ (repr (Instruction.helperList '
            'Fresh.Constructed.participant.instructions)).pretty 1000000)',
            '#eval IO.println ("calls " ++ toString (Instruction.callList Fresh.Constructed.participant.instructions).length)',
            f'#eval IO.println ("exact actual " ++ toString (exact {lowered}))',
            *[f'#eval IO.println ("exact {name} " ++ toString (exact (checkLowering installed '
              f'Fresh.Constructed.participant Fresh.{name}.validator)))' for name in artifacts["variants"]]]
        outcomes = {}
        index = 0
        kinds = mutations.kinds_for(subject.get("mutations", "kinds", []))
        if any(kind.stage == "helpers" for _, kind, _ in kinds):
            # The helper rule reads the checked helpers of the admitted program,
            # which only the composed rules' glue declares.
            self.check(f"{subject.name}:helper-mutations-admitted-program",
                       subject.get("construction", "rule", "compiled") == "compiled",
                       "helper mutations need the glue's admitted program (construction.rule = compiled)")
        for name, kind, function in kinds:
            if kind.stage not in ("lowering", "helpers"):
                continue
            sites = []
            for program in function(deployment, exported):
                program, helper = program if kind.stage == "helpers" else (program, None)
                value = copy.deepcopy(deployment)
                value[4] = json.dumps(program, separators=(",", ":"))
                value[5] = digest(value[4].encode())
                self.check(f"{subject.name}:mutation-differs:{name}:{len(sites)}", value[4] != deployment[4])
                namespace = f"Fresh.Mutation{index}"
                try:
                    rendered = executable.render(value, namespace)
                except Refused as error:
                    sites.append(dict(site=len(sites), applicable=False, reason=f"malformed: {error}"))
                    continue
                parts.append(strip_header(rendered))
                statement = (f"refusal (checkLowering installed Fresh.Constructed.participant {namespace}.validator)")
                if kind.stage == "helpers":
                    rule = f'checkHelpers installed {{}}.validator {glue_namespace}.program ["{helper}"]'
                    actual, mutated = rule.format("Fresh.Actual"), rule.format(namespace)
                    # The helper rule refuses the copy wherever it accepts the actual
                    # helper; the lowering rule accepts the copy.
                    proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : helperAccepted ({actual}) = true → "
                                  f"helperAccepted ({mutated}) = false := by decide +kernel")
                    proofs.append(f"theorem mutation{index}_lowering_accepted : {statement} = none := by decide +kernel")
                    evaluations.append(f'#eval IO.println ("helper-rule {index} " ++ helperOutcome ({actual}))')
                    evaluations.append(f'#eval IO.println ("mutation {index} " ++ helperOutcome ({mutated}))')
                    sites.append(dict(site=len(sites), applicable=True, index=index, expected=kind.expected,
                                      helper=helper))
                    index += 1
                    continue
                if kind.expected == "accepted":
                    proofs.append(f"/-- {name} -/\ntheorem mutation{index}_accepted : {statement} = none := "
                                  "by decide +kernel")
                else:
                    proofs.append(f"/-- {name} -/\ntheorem mutation{index}_refused : ({statement}).isSome = true := "
                                  "by decide +kernel")
                evaluations.append(f'#eval IO.println ("mutation {index} " ++ (repr ({statement})).pretty 1000000)')
                sites.append(dict(site=len(sites), applicable=True, index=index, expected=kind.expected))
                index += 1
            outcomes[name] = dict(stage=kind.stage, property=kind.property, expected=kind.expected, sites=sites,
                                  applicable=any(site["applicable"] for site in sites))
        proofs.append("#print axioms actual_accepted")
        result = self.lean(subject, "FreshLowering.lean", "\n\n".join(parts + proofs + evaluations) + "\n")
        self.check(f"{subject.name}:lean-rule-lowering", axioms_allowed(result.stdout, "actual_accepted"),
                   result.stdout[-400:])
        lines = result.stdout.splitlines()

        def value(prefix):
            found = [line[len(prefix) + 1:] for line in lines if line.startswith(prefix + " ")]
            self.check(f"{subject.name}:lean-evaluated:{prefix}", len(found) == 1, result.stdout[-400:])
            return found[0]
        for name, outcome in outcomes.items():
            for site in outcome["sites"]:
                if site.get("applicable") and outcome["stage"] == "helpers":
                    # A site applies where the helper rule accepts the actual helper.
                    actual = value(f"helper-rule {site['index']}")
                    if actual != "none":
                        site.update(applicable=False, reason=f"the helper rule refuses the actual helper: {actual}")
                        continue
                    site["lowering"] = "accepted"
                if site.get("applicable"):
                    site["reason"] = value(f"mutation {site['index']}")
            outcome["applicable"] = any(site.get("applicable") for site in outcome["sites"])
            outcome["refused"] = sum(1 for site in outcome["sites"]
                                     if site.get("applicable") and site["reason"] != "none")
            outcome["accepted"] = sum(1 for site in outcome["sites"]
                                      if site.get("applicable") and site["reason"] == "none")
        total = value("total")
        receives = value("receives")
        helpers = value("helpers")
        facts = dict(total=None if total == "none" else int(total.removeprefix("(some ").removesuffix(")")),
                     receives=None if receives == "none" else receives.removeprefix("some "),
                     helpers=helpers, calls=int(value("calls")))
        exact = {"actual": value("exact actual")}
        exact.update({name: value(f"exact {name}") for name in artifacts["variants"]})
        for name, expected in subject.get("executable", "exact", {}).items():
            self.check(f"{subject.name}:lowering-exact:{name}", exact.get(name) == f"(some {str(expected).lower()})",
                       json.dumps(exact))
        axioms = printed_axioms(result.stdout).get("actual_accepted")
        record["kernel"]["lowering"] = dict(file="FreshLowering.lean", accepted=True, exact=exact, facts=facts,
                                            threshold=None, axioms=axioms)
        record_accepted(record, "lowering", axioms=axioms)
        for name in artifacts["variants"]:
            record_accepted(record, f"lowering-variant:{name}")
        record["runtime_selection"] = selected
        record.setdefault("mutations", {}).update(outcomes)
        return facts

    @staticmethod
    def role_selection(deployment):
        """The validator's role-map row, which the runtime uses for inputs and acceptance, and
        whether it takes the policy's public inputs in order and selects its acceptance output."""
        policy = deployment[2][1]
        rows = [row for row in deployment[6] if row[0] == policy[3]]
        if len(rows) != 1:
            return None
        _, symbol, inputs, outputs, _, acceptance = rows[0]
        data_inputs = [port for port, _ in inputs]
        selects = (acceptance.isdigit() and int(acceptance) < len(outputs)
                   and outputs[int(acceptance)][0] == policy[4])
        return dict(symbol=symbol, data_inputs=data_inputs, acceptance=acceptance,
                    inputs_match=data_inputs == policy[7], acceptance_match=selects)

    def role_map(self, subject, deployment):
        prefix = subject.name
        selection = self.role_selection(deployment)
        self.check(f"{prefix}:role-map-validator", selection is not None)
        self.check(f"{prefix}:role-map-public-inputs", selection["inputs_match"], json.dumps(selection))
        self.check(f"{prefix}:role-map-acceptance", selection["acceptance_match"], json.dumps(selection))
        # Controls: a policy selecting another output, or other public inputs (in another order,
        # or none when there is one), fails.
        other = copy.deepcopy(deployment)
        other[2][1][4] = str(int(other[2][1][4]) + 1)
        reordered = copy.deepcopy(deployment)
        inputs = reordered[2][1][7]
        reordered[2][1][7] = list(reversed(inputs)) if len(inputs) > 1 else []
        self.check(f"{prefix}:role-map-refuses-other-acceptance",
                   not self.role_selection(other)["acceptance_match"])
        self.check(f"{prefix}:role-map-refuses-other-inputs",
                   not self.role_selection(reordered)["inputs_match"])
        return dict(symbol=selection["symbol"], data_inputs=selection["data_inputs"],
                    acceptance=selection["acceptance"])

    # 6. Runtime differential.

    def verify(self, subject, package, pin, proof, name, public, *, instructions=None):
        output = self.directory(subject, "runtime")
        path = output / f"proof-{name}.bin"
        path.write_bytes(proof)
        arguments = [self.args.native, "--json", "verify", f"--package={package}", f"--sha256={pin}",
                     f"--public={public}", f"--proof={path}"]
        if instructions is not None:
            limits = output / f"capacity-{instructions}.json"
            limits.write_text(json.dumps(runtime.capacity(instructions)))
            arguments.append(f"--capacity={limits}")
        result = self.run(arguments, expect=None, name=f"{subject.name}:verify:{name}")
        report = json.loads(result.stdout) if result.stdout.strip() else {}
        (output / f"verify-{name}.json").write_text(result.stdout)
        return result.returncode, report

    def runtime(self, subject, artifacts, entry, facts, record):
        output = self.directory(subject, "runtime")
        proof_directory = self.directory(subject, "proof")
        package = proof_directory / "package.zkpkg"
        pin = digest(artifacts["package_bytes"])
        entry_name = subject.get("entries", "proof")
        public = subject.inputs(entry_name, "public")
        witness = subject.inputs(entry_name, "witness")
        arguments = [self.args.native, "--json", "prove", f"--package={package}", f"--sha256={pin}",
                     f"--public={public}", f"--output={output / 'proof.bin'}"]
        if witness is not None:
            arguments.append(f"--witness={witness}")
        producer = json.loads(self.run(arguments, name=f"{subject.name}:prove").stdout)
        proof = (output / "proof.bin").read_bytes()
        binding = proof[8:runtime.HEADER]
        self.check(f"{subject.name}:proof-binding", binding.hex() == producer["execution"]["binding_sha256"])
        threshold = facts["threshold"]
        cases, observed, codes = [], [], {}
        for budget in range(0, threshold + 2):
            exit_code, report = self.verify(subject, package, pin, proof, f"budget-{budget}", public,
                                            instructions=budget)
            cases.append((budget, proof, [], []))
            observed.append((f"budget-{budget}", runtime.observed(exit_code, report)))
        scenarios = runtime.scenarios(proof)
        for name, (bytes_, invalid, ones, wrong) in scenarios.items():
            exit_code, report = self.verify(subject, package, pin, bytes_, name, public)
            cases.append((1000000, bytes_, invalid, ones))
            observed.append((name, runtime.observed(exit_code, report)))
            codes[name] = (exit_code, report.get("code"))
            if wrong:
                # A changed message value: the prediction maps every value to zero or one, so
                # the runtime must reject it itself.
                self.check(f"{subject.name}:runtime-rejects-{name}", exit_code > 0, json.dumps(codes[name]))
        predicted = self.predictions(subject, artifacts, entry, cases, binding, json.loads(public.read_text()))
        comparisons = []
        for (name, actual), expected in zip(observed, predicted):
            if expected["outcome"] == "returned" and actual["outcome"] == "accepted":
                expected = dict(expected, outcome="accepted")
            keys = ["outcome"] if expected["outcome"] == "header" else \
                ["outcome", "site", "call", "used", "transitions", "messages"]
            if expected["outcome"] in ("accepted", "returned"):
                keys.append("complete")
            same = all(actual.get(key) == expected.get(key) for key in keys)
            comparisons.append(dict(case=name, runtime=actual, lean=expected, compared=keys, same=same))
            self.check(f"{subject.name}:runtime-agrees:{name}", same, json.dumps(dict(runtime=actual, lean=expected)))
        accepted = [c["case"] for c in comparisons if c["runtime"]["outcome"] == "accepted"]
        self.check(f"{subject.name}:runtime-accepted-cases",
                   accepted == [f"budget-{threshold}", f"budget-{threshold + 1}", "honest"], json.dumps(accepted))
        wrong = next(name for name, scenario in scenarios.items() if scenario[3])
        record["runtime"] = dict(pin=pin, proof_sha256=digest(proof), binding=binding.hex(), threshold=threshold,
                                 scenarios=sorted(scenarios), comparisons=len(comparisons),
                                 agreeing=sum(1 for c in comparisons if c["same"]))
        record_accepted(record, "runtime-differential", cases=len(comparisons))
        return dict(pin=pin, proof=proof, wrong=scenarios[wrong][0], public=public)

    def predictions(self, subject, artifacts, entry, cases, binding, public):
        """Evaluate the Lean executable meaning on every case."""
        glue_module = subject.module_name("glue")
        glue_namespace = subject.construction_namespace
        definitions = runtime.PREDICTION.replace("CONTEXT", f"{glue_namespace}.context").replace(
            "DATA", runtime.prediction_data(entry, public))
        lines = ["import Zkc.Executable.Installed", "import Mathlib.Algebra.Field.ZMod", f"import {glue_module}",
                 strip_header(executable.render(artifacts["deployment"], "Fresh.Actual")),
                 "open Zkc.Construction Zkc.Executable",
                 "local instance : Fact (Nat.Prime 5) := ⟨by decide⟩",
                 "abbrev Scalar := ZMod 5", definitions]
        for budget, bytes_, invalid, ones in cases:
            lines.append(f"#eval IO.println (predict {budget} {runtime.lean_bytes(binding)} "
                         f"{runtime.lean_bytes(bytes_)} [{', '.join(runtime.lean_bytes(item) for item in invalid)}] "
                         f"[{', '.join(runtime.lean_bytes(item) for item in ones)}])")
        result = self.lean(subject, "Predictions.lean", "\n\n".join(lines) + "\n")
        values = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        self.check(f"{subject.name}:lean-predictions", len(values) == len(cases), result.stdout[-400:])
        return values

    # The receipt: axiom closures, proof dependencies and the binding to the runtime.

    def receipt_axioms(self, subjects):
        """The axiom closure of every theorem in the receipts' chains, and the declarations
        each byte-level theorem's proof reaches."""
        receipts = [subject for subject in subjects if subject.table("receipt")]
        if not receipts:
            return {}
        control = "ZkcExamples.ClassificationControl.compiled"
        imports = sorted({subject.get("receipt", "security_module") for subject in receipts}
                         | {subject.get("executable", "completeness_module") for subject in receipts
                            if subject.get("executable", "completeness_module")})
        chain = []
        for subject in receipts:
            chain += [name for name in subject.get("receipt", "chain", []) if name not in chain]
        reaches = [(subject.get("receipt", "theorem"), name) for subject in receipts
                   for name in subject.get("receipt", "used", []) + subject.get("receipt", "unused", [])]
        prefixes = ", ".join(f"`{name}" for name in ENTRY_PREFIXES)
        meanings = ", ".join(f"`{name}" for name in COMPILED_MEANINGS)
        source = ("".join(f"import {name}\n" for name in imports) + "import Zkc.Executable.Cleanup\n\n"
                  + CLASSIFICATION_CONTROL
                  + "".join(f"#print axioms {name}\n" for name in chain)
                  + RECEIPT_WALK.replace("MEANINGS", meanings).replace("PREFIXES", prefixes)
                  + "".join(f"#eval do IO.println s!\"reaches {root} {name}: {{← reaches `{root} `{name}}}\"\n"
                            for root, name in reaches)
                  + "\nopen Lean Meta in\n#eval show MetaM Unit from do\n"
                  + "".join(f"  for (name, evaluated, compiled) in ← processEquations `{theorem} do\n"
                            f"    IO.println s!\"process-equation {theorem} {{name}} evaluated={{evaluated}} "
                            "compiled={compiled}\"\n"
                            for theorem in [subject.get("receipt", "theorem") for subject in receipts])
                  + (f"  for (name, evaluated, compiled) in ← processEquations `{control} do\n"
                     "    IO.println s!\"control-equation {name} evaluated={evaluated} compiled={compiled}\"\n"
                     if control else "  pure ()\n"))
        result = self.evaluate(self.output / "ReceiptAxioms.lean", source, cwd=LEAN / "integrations/arklib",
                               name="receipt-axioms")
        found = printed_axioms(result.stdout)
        for name in chain:
            self.check(f"axioms:{name}", name in found and set(found[name]) <= ALLOWED_AXIOMS,
                       json.dumps(found.get(name)))
        reached = {(root, name): value for root, name, value in
                   re.findall(r"^reaches (\S+) (\S+): (true|false)$", result.stdout, re.M)}
        if control:
            controls_found = re.findall(r"^control-equation (\S+) evaluated=(true|false) compiled=(true|false)$",
                                        result.stdout, re.M)
            self.check("process-equation-classifier", (control, "true", "true") in controls_found,
                       json.dumps(controls_found))
        dependencies = {}
        for subject in receipts:
            theorem = subject.get("receipt", "theorem")
            for name in subject.get("receipt", "used", []):
                value = reached.get((theorem, name))
                self.check(f"{subject.name}:proof-uses:{name}", value == "true", json.dumps(value))
            for name in subject.get("receipt", "unused", []):
                value = reached.get((theorem, name))
                self.check(f"{subject.name}:proof-avoids:{name}", value == "false", json.dumps(value))
            equations = re.findall(rf"^process-equation {re.escape(theorem)} (\S+) "
                                   r"evaluated=(true|false) compiled=(true|false)$", result.stdout, re.M)
            # Proof syntax is attribution only. A reflexive equation is valid
            # evidence when it proves the fixed statement; required links and
            # standard axioms are checked independently of this classifier.
            evaluated_compiled = [name for name, evaluated, compiled in equations
                                  if evaluated == "true" and compiled == "true"]
            dependencies[subject.name] = dict(
                uses=subject.get("receipt", "used", []), avoids=subject.get("receipt", "unused", []),
                original_stage_equations=dict(
                    evaluated=[name for name, evaluated, compiled in equations
                               if evaluated == "true" and compiled == "false"],
                    derived=[name for name, evaluated, compiled in equations
                             if evaluated == "false" and compiled == "false"]),
                compiled_stage_equations=[name for name, _, compiled in equations if compiled == "true"],
                evaluated_compiled_stage_equations=evaluated_compiled,
                axioms={name: found.get(name) for name in subject.get("receipt", "chain", [])})
        return dependencies

    @staticmethod
    def repackage(artifacts, change, *, keep_inner_digest=False):
        package = copy.deepcopy(artifacts["package"])
        deployment = copy.deepcopy(artifacts["deployment"])
        program = json.loads(deployment[4])
        changed = change(program, deployment)
        deployment[4] = json.dumps(program, separators=(",", ":"))
        if not keep_inner_digest:
            deployment[5] = digest(deployment[4].encode())
        package["artifact"] = json.dumps(deployment, separators=(",", ":"))
        return json.dumps(package, separators=(",", ":")).encode(), deployment, changed

    def binding(self, subject, artifacts, run, record):
        """The runtime executes exactly the program the record names."""
        prefix = subject.name
        directory = self.directory(subject, "proof")
        output = self.directory(subject, "runtime")
        package = directory / "package.zkpkg"
        named = json.loads(json.loads(package.read_bytes())["artifact"])[4].encode()
        program_digest = digest(artifacts["program"])
        self.check(f"{prefix}:record-program", digest(named) == program_digest)
        self.check(f"{prefix}:record-package", digest(package.read_bytes()) == run["pin"])
        honest = (output / "proof.bin").read_bytes()
        wrong = run["wrong"]
        exit_code, report = self.verify(subject, package, run["pin"], honest, "record-honest", run["public"])
        self.check(f"{prefix}:runtime-runs-record-package", exit_code == 0 and report.get("status") == "accepted"
                   and report.get("package_sha256") == run["pin"], json.dumps(report)[-400:])
        exit_code, report = self.verify(subject, package, run["pin"], wrong, "record-wrong", run["public"])
        self.check(f"{prefix}:record-package-rejects-wrong-proof", exit_code > 0, json.dumps(report)[-400:])
        results = {}
        mutated, deployment, changed = self.repackage(artifacts, mutations.accept_any)
        self.check(f"{prefix}:accept-any-applicable", changed)
        path = output / "package-mutated.zkpkg"
        path.write_bytes(mutated)
        exit_code, report = self.verify(subject, path, run["pin"], wrong, "mutated-same-pin", run["public"])
        results["same-pin"] = report.get("code")
        self.check(f"{prefix}:runtime-refuses-other-package",
                   exit_code > 0 and report.get("code") == "entry-package-identity", json.dumps(report)[-400:])
        exit_code, report = self.verify(subject, path, digest(mutated), wrong, "mutated-repinned", run["public"])
        results["repinned-wrong-proof"] = report.get("status")
        self.check(f"{prefix}:mutated-program-changes-acceptance",
                   exit_code == 0 and report.get("status") == "accepted", json.dumps(report)[-400:])
        self.check(f"{prefix}:record-refuses-mutated-program", digest(deployment[4].encode()) != program_digest)
        stale, _, _ = self.repackage(artifacts, mutations.accept_any, keep_inner_digest=True)
        path = output / "package-stale-digest.zkpkg"
        path.write_bytes(stale)
        exit_code, report = self.verify(subject, path, digest(stale), honest, "stale-inner-digest", run["public"])
        results["stale-inner-digest"] = report.get("code")
        self.check(f"{prefix}:runtime-refuses-stale-program-digest",
                   exit_code > 0 and report.get("code") == "native-proof-candidate-binding", json.dumps(report)[-400:])
        record["binding"] = results
        record_accepted(record, "record-binding")

    # The claim's generated modules in the security integration.

    def claim_inventory(self, record, exports, selected_claims=()):
        """Inventory all source nodes independently of receipt generation."""
        inventory = {}
        for export in exports:
            for item in export["source_claim_inventory"]:
                key = canonical(item["node"])
                require(key not in inventory or inventory[key] == item,
                        "conflicting source claim inventory")
                inventory[key] = item
        selected_nodes = {canonical(claim["attachment"]["node"]) for claim in selected_claims}
        require(selected_nodes <= inventory.keys(), "selected claim absent from source inventory")
        record["source_claim_inventory"] = [dict(item, selection=(
            "selected" if key in selected_nodes else "unselected-subject"))
            for key, item in inventory.items()]

    def claims(self, subject, artifacts, entry, record, interactive=None):
        """Fresh source requests, typed resolution/evaluation and genuine proofs."""
        bound = copy.deepcopy(artifacts["source_claims"])
        groups = {bound.get("entry"): bound["claims"][:]}
        if interactive is not None:
            bound["entries"] = [bound["entry"], interactive["source_claims"]["entry"]]
            bound["claims"].extend(interactive["source_claims"]["claims"])
            groups[interactive["source_claims"]["entry"]] = interactive["source_claims"]["claims"]
            artifacts["interactive"] = interactive
        selected = getattr(self.args, "claim_entry", None) or [bound.get("entry")]
        require(all(name in groups for name in selected), "claim Entry was not compiled for this subject")
        selected_claims = [claim for name in selected for claim in groups[name]]
        self.claim_inventory(record, [artifacts, *([interactive] if interactive is not None else [])],
                             selected_claims)
        record["source_claims"] = dict(bound, entries=selected, claims=selected_claims)
        record["source_claim_scope"] = dict(entries=selected,
                                            selection="explicit" if getattr(self.args, "claim_entry", None)
                                            else "proof-entry")
        # Whole other Entries remain visible as trials, with their actual generated
        # declarations. A separately selected report audits them independently.
        trials = {name: dict(entry=name, claims=claims, claim_receipts=[])
                  for name, claims in groups.items() if name not in selected and claims}
        record["source_claim_trials"] = list(trials.values())
        claim_entries = [name for name, claims in groups.items() for _ in claims]
        if not subject.get("lean", "namespace"):
            record["claim_receipts"] = [dict(
                node=claim["attachment"]["node"], request_digest=claim["request_digest"],
                request_declaration=None, receipt_declaration=None,
                resolution=dict(status="open", definitions=[],
                                diagnostic="no configured Lean registration module"),
                attempts=[dict(status="unsupported", reason="no physical Lean generation configuration")])
                for claim in selected_claims]
            return
        executable_namespace = subject.get("executable", "namespace") if subject.profile("executable") else None
        sources = {
            "artifacts": evidence.artifacts_module(subject, entry, subject.construction_namespace,
                                                   executable_namespace, artifacts),
            "claims": evidence.claims_module(subject, bound),
        }
        if executable_namespace:
            sources["lowering"] = evidence.lowering_module(subject, entry, executable_namespace)
        for key, source in sources.items():
            path = subject.generated(key)
            expected = subject.generated("claims").with_name(key.capitalize() + ".lean")
            self.check(f"{subject.name}:claims-path:{key}", path == expected,
                       f"[generated] {key} must be beside the subject's Claims module")
            self.generated(subject, key, source, record)
        module = subject.module_name("claims")
        built = self.lake("build", module, cwd=subject.generated_package("claims"),
                          name=f"{subject.name}:claims-build")
        results = {}
        for line in built.stdout.splitlines():
            marker = "SOURCE_CLAIM_RESULT "
            if marker in line:
                value = json.loads(line.split(marker, 1)[1])
                results[value["request"]] = value
        record["claim_receipts"] = []
        namespace = subject.get("lean", "namespace")
        for index, claim in enumerate(bound["claims"]):
            request = f"{namespace}.request{index}Data"
            result = results.get(request)
            self.check(f"{subject.name}:claim-result:{index}", result is not None,
                       "fresh generated claim command did not emit its resolution/attempt result")
            receipt = result.get("receipt")
            item = dict(node=claim["attachment"]["node"], request_digest=claim["request_digest"],
                        request_declaration=request, receipt_declaration=receipt,
                        attempts=result.get("attempts", []))
            if result.get("resolution"):
                item["resolution"] = result["resolution"]
            claim_entry = claim_entries[index]
            if claim_entry in selected:
                record["claim_receipts"].append(item)
            elif claim_entry in trials:
                trials[claim_entry]["claim_receipts"].append(item)
            if receipt:
                record_accepted(record, "claim-receipt", module=module, request=request, receipt=receipt)

    # Normal forms and the record.

    def normal_forms(self, subject, record):
        request = subject.get("normal_forms", "request")
        if not request:
            return
        self.run([sys.executable, NORMAL_FORMS, ROOT / request, *([] if self.args.write else ["--check"])],
                 name=f"{subject.name}:normal-forms")
        output = (ROOT / tomllib.loads((ROOT / request).read_text())["output"]).resolve()
        module = ".".join(output.relative_to(LEAN).with_suffix("").parts)
        # The generator can rewrite a module already imported earlier in this
        # run. Build it before recording success, even if its text matches.
        self.built.clear()
        self.build(module)
        record["generated"][str(output.relative_to(ROOT))] = dict(
            sha256=file_digest(output), role="normal-forms")
        record["normal_forms"] = dict(request=request, module=module)
        record_accepted(record, "normal-forms", request=request, module=module)

    def subject(self, subject):
        record = dict(format="zkc.subject-evidence/0", subject=subject.name,
                      manifest_sha256=file_digest(subject.path), artifacts={}, generated={}, checks=[],
                      manifest=str(subject.path.relative_to(ROOT)),
                      profiles=sorted(name for name in ("structured", "construction", "executable", "scalar")
                                      if subject.profile(name)),
                      sources={name: file_digest(path) for name, path in sorted(subject.modules.items())},
                      lean=subject.table("lean"))
        self.evidence[subject.name] = record
        requested = subject.get("assumptions", "requested", [])
        if requested:
            optional = any(subject.generated_package(key) == LEAN / "integrations/arklib"
                           for key in subject.table("generated")
                           if subject.generated(key).suffix == ".lean") or subject.get(
                               "receipt", "security_module", "").startswith("ZkcArkLib.")
            registry = self.registry("arklib" if optional else "security")
            unknown = [name for name in requested if name not in registry]
            self.check(f"{subject.name}:assumptions-registered", not unknown, json.dumps(unknown))
            record["requested_assumptions"] = {name: registry[name] for name in requested}
        interactive = None
        if subject.profile("structured"):
            interactive = self.interactive(subject, record)
            self.claim_inventory(record, [interactive])
        self.normal_forms(subject, record)
        run = None
        if subject.profile("construction"):
            artifacts, entry = self.proof(subject, record)
            if subject.profile("executable"):
                facts = self.executable(subject, artifacts, entry, record)
                if self.args.runtime:
                    run = (artifacts, self.runtime(subject, artifacts, entry, facts, record))
            self.claims(subject, artifacts, entry, record, interactive)
        if subject.profile("scalar"):
            record["scalar"] = dict(contract=subject.get("scalar", "contract"),
                                    properties=sorted(subject.get("scalar", "properties", {})))
        self.write_evidence(subject.name)
        return run

    def write_evidence(self, name):
        """The subject's evidence, `<output>/evidence/<name>.json`, for the records pipeline."""
        path = self.output / "evidence" / f"{name}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(self.evidence[name], indent=2) + "\n")
        return path


CLASSIFICATION_CONTROL = r"""
namespace ZkcExamples.ClassificationControl
open Zkc.Source Zkc.Source.Structured Zkc.Construction
/-- Classifier control only; this reflexive equation proves no source connection. -/
theorem compiled {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G]
    [Module F G] [DecidableEq G] (program : Structured.Program) (context : Context)
    (artifact : Participant) (inputs : Domain.Environment (uniformCarriers F G)) :
    Domain.participant (ringModel F G) program context artifact inputs =
      Domain.participant (ringModel F G) program context artifact inputs := rfl
end ZkcExamples.ClassificationControl
"""

RECEIPT_WALK = r"""
open Lean in
/-- The transitive constant dependencies of `root`, `root` included. -/
def dependencyClosure (root : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut order : Array Name := #[]
  let mut pending : List Name := [root]
  repeat
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      unless visited.contains name do
        visited := visited.insert name
        order := order.push name
        if let some info := env.find? name then
          pending := info.type.getUsedConstants.toList ++ pending
          if let some value := info.value? true then
            pending := value.getUsedConstants.toList ++ pending
          if let .recInfo recursor := info then
            pending := recursor.all ++ pending
            for rule in recursor.rules do
              pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
  return order

open Lean in
/-- Whether `target` occurs in the transitive constant dependencies of `root`. -/
def reaches (root target : Name) : CoreM Bool :=
  return (← dependencyClosure root).contains target

open Lean in
/-- Follow definitions in a statement, so a wrapper cannot hide compiled execution.
Opaque theorem bodies are audited separately by the full proof-dependency walk. -/
def mentionsCompiled (meanings : List Name) (expression : Expr) : CoreM Bool := do
  let env ← getEnv
  let mut pending := expression.getUsedConstants.toList
  let mut visited : NameSet := {}
  repeat
    match pending with
    | [] => return false
    | name :: rest =>
      pending := rest
      if meanings.contains name then return true
      if visited.contains name then continue
      visited := visited.insert name
      if let some (.defnInfo info) := env.find? name then
        pending := info.value.getUsedConstants.toList ++ pending

open Lean Meta in
/-- Entry-specific theorems in the closure of `root` whose statement is an
equation between processes: whether the kernel checks each by evaluation
(its proof is `rfl`) and whether its statement names a compiled meaning.
Equation lemmas generated for definitions are unfoldings and are skipped. -/
def processEquations (root : Name) : MetaM (Array (Name × Bool × Bool)) := do
  let env ← getEnv
  let meanings : List Name := [MEANINGS]
  -- Retired meanings remain syntactic markers even after their declarations
  -- leave the environment. The actual compiled control below must still pass.
  let mut found := #[]
  for name in (← dependencyClosure root).qsort Name.lt do
    unless [PREFIXES].any (·.isPrefixOf name) do continue
    if let .str _ last := name then
      if last.startsWith "eq_" then continue
    let some (.thmInfo info) := env.find? name | continue
    let isProcess ← forallTelescope info.type fun _ body => do
      let body ← whnfR body
      if body.isAppOfArity ``Eq 3 then
        return (← whnfR (body.getArg! 0)).isAppOf ``PIR.Process
      return false
    unless isProcess do continue
    let evaluated ← lambdaTelescope info.value fun _ proof =>
      return proof.isAppOf ``Eq.refl || proof.isAppOf ``rfl
    let compiled ← mentionsCompiled meanings info.type
    found := found.push (name, evaluated, compiled)
  return found

"""


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="compare generated modules (the default)")
    mode.add_argument("--write", action="store_true", help="rewrite the generated modules the manifests own")
    parser.add_argument("--subject", action="append", help="process only the named subjects (default: all)")
    parser.add_argument("--claim-entry", action="append",
                        help="report whole source Entries explicitly (default: the proof Entry); "
                             "other compiled Entries remain visible as separately scoped trials")
    parser.add_argument("--runtime", action="store_true",
                        help="run the runtime differential and record binding of executable subjects")
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--native", type=Path, default=ROOT / "target/release/zkc", help="the runtime CLI")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--fresh-bodies", action="store_true", help="elaborate body printers without Lake replay")
    parser.add_argument("--output", type=Path, help="new or empty evidence directory")
    parser.add_argument("--list-mutations", action="store_true", help="list the generic mutation kinds and exit")
    args = parser.parse_args()
    if args.list_mutations:
        print(json.dumps(mutations.listing(), indent=2))
        return
    if args.output is None:
        from workspace import reports_root
        from reporting import new_directory
        args.output = new_directory(reports_root() / "lean", "subjects")
    args.output = args.output.resolve()
    args.compiler = args.compiler.resolve()
    args.native = args.native.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error("--output must be a new or empty directory")
    driver = Driver(args)
    report = dict(format="zkc.subject-check/0", started=now(), status="failed",
                  mode="write" if args.write else "check", runtime=args.runtime, subjects={})
    try:
        subjects = manifest.load_all(args.subject)
        bound = []
        for subject in subjects:
            result = driver.subject(subject)
            if result:
                bound.append((subject, *result))
        if args.runtime:
            dependencies = driver.receipt_axioms([subject for subject in subjects if subject.profile("executable")])
            for subject, artifacts, run in bound:
                record = driver.evidence[subject.name]
                record["proof_dependencies"] = dependencies.get(subject.name)
                if dependencies.get(subject.name):
                    record_accepted(record, "receipt-axioms-and-dependencies")
                driver.binding(subject, artifacts, run, record)
                driver.write_evidence(subject.name)
        for name in driver.evidence:
            report["subjects"][name] = f"evidence/{name}.json"
        report["status"] = "pass"
    except Exception as error:  # every failure is reported; the exit status stays nonzero
        report["error"] = f"{type(error).__name__}: {error}"
    report.update(finished=now(), commands=driver.commands, checks=driver.checks)
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(status=report["status"], checks=len(driver.checks), output=str(args.output),
                          error=report.get("error"))))
    sys.exit(0 if report["status"] == "pass" else 1)


if __name__ == "__main__":
    main()
