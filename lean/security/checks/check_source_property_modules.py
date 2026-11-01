#!/usr/bin/env python3
"""Check the six source-property module boundaries in a private Lean overlay."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
SECURITY = ROOT / "lean/security"
PREFIX = "ZkcSecurityExamples.Sumcheck.Source"
NAMESPACE = "ZkcSecurity.Realizations.Sumcheck.Source"
PROPERTIES = {
    "Pair": [("small", "honest-pair"), ("two", "honest-pair")],
    "Public": [("small_no", "public-rejection"), ("two_no", "public-rejection"),
               ("small_cost", "public-cost"), ("two_cost", "public-cost")],
}
CAPTURE = r'''
import ZkcSecurityExamples.Sumcheck.SourcePairInstallations
import ZkcSecurityExamples.Sumcheck.SourcePublicInstallations
open Lean Meta Elab Command
-- Bound names and source metadata do not change a Lean type. Retain every
-- constant, universe, binder kind, dependent index, hypothesis and let value.
private partial def alphaType : Expr → Expr
  | .forallE _ type body binder => .forallE .anonymous (alphaType type) (alphaType body) binder
  | .lam _ type body binder => .lam .anonymous (alphaType type) (alphaType body) binder
  | .letE _ type value body nondep =>
      .letE .anonymous (alphaType type) (alphaType value) (alphaType body) nondep
  | .app function argument => .app (alphaType function) (alphaType argument)
  | .mdata _ body => alphaType body
  | .proj typeName index body => .proj typeName index (alphaType body)
  | expression => expression
run_cmd do
  let mut rows := #[]
  for name in [``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.one,
      ``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.small,
      ``ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations.two,
      ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_no,
      ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_no,
      ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.small_cost,
      ``ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost] do
    let info ← getConstInfo name
    let axioms ← liftTermElabM <| collectAxioms name
    let mut binders := #[]
    let mut type := info.type
    while let .forallE name _ body binder := type do
      binders := binders.push (name.toString, toString (repr binder))
      type := body
    rows := rows.push (Json.mkObj [
      ("declaration", toJson name.toString), ("type", toJson (reprStr (alphaType info.type))),
      ("binders", toJson binders), ("levels", toJson (info.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.toList.map Name.toString))])
  logInfo (Json.arr rows).compress
'''


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "build/experiments/source-authoring/modules")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    library = output / "private-lib"
    generated = output / "generated"
    checks: list[dict] = []

    def run(label: str, command: list[str], *, env=None, cwd=SECURITY,
            expected=0, timeout=180) -> str:
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
        log = output / (label + ".log")
        log.write_text(result.stdout)
        checks.append(dict(gate=label, command=command, cwd=str(cwd), exit_code=result.returncode,
                           expected_exit_code=expected, elapsed_seconds=round(time.monotonic()-started, 3),
                           timeout_seconds=timeout, log=str(log), log_sha256=sha(log)))
        print(f"{label}: exit {result.returncode}", flush=True)
        if expected is not None and result.returncode != expected:
            raise RuntimeError(f"{label} failed; see {log}\n{result.stdout[-6000:]}")
        return result.stdout

    lean = run("lean-path", ["lake", "env", "which", "lean"]).strip()
    search = run("dependency-path", ["lake", "env", "printenv", "LEAN_PATH"]).strip()
    baseline_env = dict(os.environ, LEAN_PATH=search)
    environment = dict(os.environ, LEAN_PATH=str(library) + os.pathsep + search)
    protected = [ROOT / "lean/ZkcTools/Companions.lean",
                 ROOT / "lean/ZkcTools/Companions/Assembly.lean",
                 SECURITY / "ZkcSecurityTools/SourceProperties/Builder.lean"]
    protected_before = {str(path.relative_to(ROOT)): sha(path) for path in protected}
    # Mirror only this worktree's existing objects. Every changed object is
    # unlinked from this overlay before compilation; shared deps are read only.
    for original_root in [ROOT / "lean/.lake/build/lib/lean", SECURITY / ".lake/build/lib/lean"]:
        for original in original_root.rglob("*"):
            if original.is_file():
                target = library / original.relative_to(original_root)
                if not target.exists():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.symlink_to(original)

    def compile_module(module: str, source: Path, label: str | None = None) -> str:
        target = library / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        for artifact in target.parent.glob(target.stem + ".*"):
            if artifact.is_symlink():
                artifact.unlink()
        root = ROOT / "lean" if source.is_relative_to(ROOT / "lean/ZkcTools") else SECURITY
        if source.is_relative_to(output):
            root = generated
        return run(label or module, [lean, "--threads=2", "-DwarningAsError=true",
                   "--root=" + str(root), "-o", str(target), str(source)], env=environment)

    capture = output / "Capture.lean"
    capture.write_text(CAPTURE)
    capture_command = [lean, "--threads=2", "-DwarningAsError=true", "--root=" + str(output), str(capture)]
    baseline = json.loads(run("baseline-types", capture_command, env=baseline_env))
    (output / "baseline-types.json").write_text(json.dumps(baseline, indent=2) + "\n")
    modules = ["ZkcTools.Companions.Goals", "ZkcTools.Companions.Report",
               "ZkcSecurityTools.SourceProperties.Assembly", "ZkcSecurityTools.SourceProperties.Builder"]
    modules += [PREFIX + family + "Goals" for family in PROPERTIES]
    modules += [PREFIX + family + "Companions" for family in PROPERTIES]
    for module in modules:
        owner = ROOT / "lean" if module.startswith("ZkcTools.") else SECURITY
        compile_module(module, owner / (module.replace(".", "/") + ".lean"))

    generator = [lean, "--threads=2", "-DwarningAsError=true", "--run",
                 "checks/GenerateSourcePropertyModules.lean", str(generated)]
    run("generate", generator, env=environment)
    for path in (generated / "CompanionStubs").glob("*.lean"):
        marker = "-- Existing author text retained during regeneration.\n"
        if marker not in path.read_text():
            path.write_text(path.read_text() + marker)
    before_regeneration = {str(path.relative_to(generated)): sha(path) for path in generated.rglob("*.lean")}
    run("regenerate", generator, env=environment)
    after_regeneration = {str(path.relative_to(generated)): sha(path) for path in generated.rglob("*.lean")}
    if before_regeneration != after_regeneration:
        raise RuntimeError("regeneration changed generated sources or existing author scaffolds")
    for family in PROPERTIES:
        module = PREFIX + family + "Installations"
        path = Path(module.replace(".", "/") + ".lean")
        if (generated / path).read_bytes() != (SECURITY / path).read_bytes():
            raise RuntimeError(f"regenerate {path}")
        compile_module(module, SECURITY / path)
    compile_module("TestsSecurity.SourcePropertyCompanions", SECURITY / "TestsSecurity/SourcePropertyCompanions.lean")
    run("consumer-controls", [lean, "--threads=2", "-DwarningAsError=true",
        "TestsSecurity/SourcePropertyConsumers.lean"], env=environment)
    run("report-controls", [lean, "--threads=2", "-DwarningAsError=true",
        "Tests/CompanionReport.lean"], cwd=ROOT / "lean", env=environment)
    current = json.loads(run("current-types", capture_command, env=environment))
    (output / "current-types.json").write_text(json.dumps(current, indent=2) + "\n")
    type_evidence = []
    for prior, now in zip(baseline, current, strict=True):
        for key in ["declaration", "type", "levels", "binders"]:
            if prior[key] != now[key]:
                raise RuntimeError(f"changed {key}: {now['declaration']}")
        if not (set(now["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}):
            raise RuntimeError(f"nonstandard axiom in {now['declaration']}")
        if set(prior["axioms"]) != set(now["axioms"]):
            raise RuntimeError(f"changed axiom set in {now['declaration']}")
        type_evidence.append(dict(declaration=now["declaration"], unchanged=True,
            type_sha256=hashlib.sha256(now["type"].encode()).hexdigest(), axioms=now["axioms"]))

    controls: dict[str, list[dict]] = {}
    for case in ["missing", "stub", "wrong"]:
        rows = []
        for family, properties in PROPERTIES.items():
            companion_module = "SourcePropertyControls." + case.capitalize() + family + "Companions"
            companion_source = generated / (companion_module.replace(".", "/") + ".lean")
            companion_source.parent.mkdir(parents=True, exist_ok=True)
            if case == "stub":
                text = (generated / ("CompanionStubs/Source" + family + "Companions.lean")).read_text()
            else:
                text = "module\npublic import " + PREFIX + family + "Goals\n"
                text += "public meta import ZkcTools.Companions.Report\npublic section\n"
            if case == "wrong":
                opposite = "Public" if family == "Pair" else "Pair"
                text = text.replace("public section\n", "public import " + PREFIX + opposite + "Companions\npublic section\n")
                scaffold = (generated / ("CompanionStubs/Source" + family + "Companions.lean")).read_text()
                identities = re.findall(r"-- zkc companion (\".*\")", scaffold)
                for (name, _), identity in zip(properties, identities, strict=True):
                    other = "two" if name.startswith("two") else "small"
                    if opposite == "Public":
                        other += "_no"
                    other_namespace = NAMESPACE + opposite + "Installations"
                    kind = "noncomputable def " if opposite == "Public" else "theorem "
                    text += ("@[zkc " + identity + "]\n" + kind + NAMESPACE + family +
                             "Installations.Companions." + name + " : " + other_namespace + "." + other +
                             "_goal := @" + other_namespace + ".Companions." + other + "\n")
            companion_source.write_text(text)
            compile_module(companion_module, companion_source, f"{case}-{family}-companion")
            consumer = (generated / (PREFIX.replace(".", "/") + family + "Installations.lean")).read_text()
            consumer = consumer.replace("public import " + PREFIX + family + "Companions",
                                        "public import " + companion_module)
            consumer_source = generated / ("SourcePropertyControls/" + case.capitalize() + family + "Consumer.lean")
            consumer_source.write_text(consumer)
            log = run(f"{case}-{family}-consumer", [lean, "--threads=2", "-DwarningAsError=true",
                      "--root=" + str(generated), str(consumer_source)], env=environment, expected=1)
            found = [json.loads(value) for value in re.findall(r"source property obligation: (\{[^\n]+\})", log)]
            if len(found) != len(properties):
                raise RuntimeError(f"missing named-root diagnostics in {case}/{family}")
            for row in found:
                if row["status"] != ("refused" if case == "wrong" else "open"):
                    raise RuntimeError(f"wrong status in {case}/{family}: {row['status']}")
                if not (row["source_span"] is None and row["goal_module"].endswith("Goals")):
                    raise RuntimeError("report invented a source span or omitted the goal module")
                if row["goal_declaration"].rsplit(".", 1)[-1] not in row["stub_text"]:
                    raise RuntimeError("reported scaffold does not use the fixed goal declaration")
                if "sorry" in row["stub_text"]:
                    raise RuntimeError("reported scaffold contains sorry")
                if case == "wrong":
                    if len(row["default_attempts"]) != 1:
                        raise RuntimeError("wrong companion silently tried another method")
                    reason = row["reason"].lower()
                    if not ("type mismatch" in reason and "heartbeat" not in reason and "interrupt" not in reason):
                        raise RuntimeError(f"wrong companion failed for an unexpected reason: {reason}")
                if case == "missing":
                    # Compile the actual diagnostic's scaffold with its stated
                    # import, independently of every consumer and author file.
                    stub_module = "SourcePropertyControls.ReportStub" + str(len(rows))
                    stub_source = generated / (stub_module.replace(".", "/") + ".lean")
                    stub_source.write_text("import " + row["goal_module"] +
                        "\nimport ZkcTools.Companions.Report\nset_option maxHeartbeats 2000000\n" + row["stub_text"])
                    compile_module(stub_module, stub_source, "report-stub-" + str(len(rows)))
                rows.append(row)
        controls[case] = rows
    for missing, wanted, wrong in zip(controls["missing"], controls["stub"], controls["wrong"], strict=True):
        for key in ["identity", "goal_declaration", "closed_expected_type"]:
            if not (missing[key] == wanted[key] == wrong[key]):
                raise RuntimeError(f"candidate changed fixed {key}")
    (output / "control-reports.json").write_text(json.dumps(controls, indent=2) + "\n")
    run("diff-check", ["git", "diff", "--check"], cwd=ROOT)
    run("python-syntax", ["python3", "-m", "py_compile", str(Path(__file__))], cwd=ROOT)
    documentation = json.loads(run("documentation", ["python3", "common/tests/check_docs.py",
        "--output", str(output / "docs.json")], cwd=ROOT, expected=None))
    if protected_before != {str(path.relative_to(ROOT)): sha(path) for path in protected}:
        raise RuntimeError("module checks modified shared proof lookup or assembly sources")
    sources = [ROOT / "lean/ZkcTools/Companions/Goals.lean", ROOT / "lean/ZkcTools/Companions/Report.lean",
               SECURITY / "ZkcSecurityTools/SourceProperties/Assembly.lean",
               SECURITY / "TestsSecurity/SourcePropertyCompanions.lean", SECURITY / "TestsSecurity/SourcePropertyConsumers.lean",
               ROOT / "lean/docs/development/component-authoring.md", Path(__file__),
               SECURITY / "checks/GenerateSourcePropertyModules.lean"]
    sources += [SECURITY / ((PREFIX + family + suffix).replace(".", "/") + ".lean")
                for family in PROPERTIES for suffix in ["Goals", "Companions", "Installations"]]
    report = dict(scope="Six actual SmallSumcheck/TwoSums Pair, No and Cost module boundaries",
        head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        toolchain=run("toolchain", [lean, "--version"]).strip(),
        reproduction=["python3", "lean/security/checks/check_source_property_modules.py", "--output", str(output)],
        source_sha256={str(path.relative_to(ROOT)): sha(path) for path in sources},
        protected_unchanged_sha256=protected_before, checks=checks, declaration_types=type_evidence,
        documentation=documentation,
        gates=dict(import_cycle_free=True, generated_consumer_reproduction=True,
                   regeneration_preserves_scaffolds=True, external_companions=6, missing_roots=6,
                   wanted_or_missing_value_stubs=6, wrong_companions_refused=6, compiled_report_stubs=6,
                   same_expected_type_in_all_controls=True, standard_axioms_only=True),
        generated="Closed goal declarations, complete consumer headers and lookup terms, initial stub text and identity attributes",
        authored="One explicit root signature in each goal command; ordinary companion mathematics and existing helper laws",
        limits=["Named root obligations only; no intermediate tactic-seam or frontend source-span generation",
                "Existing imported dependency objects are read only; not a fresh whole-package/native/receipt audit",
                "Type comparison removes bound names and source metadata, then compares all constants, universes, dependent binders and values; public telescope names and binder kinds are compared separately"],
        artifacts={path.name: sha(path) for path in [output / "baseline-types.json", output / "current-types.json", output / "control-reports.json"]})
    report["generated_source_sha256"] = {
        str(path.relative_to(generated)): sha(path) for path in generated.rglob("*.lean")}
    (output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n")
    print(output / "REPORT.json")


if __name__ == "__main__":
    main()
