#!/usr/bin/env python3
"""Check the records of what is proved and render tables and assurance reports.

1. Emit one declaration record per owned declaration of the selected packages
   (`DeclarationRecords.lean`), and require every axiom closure to stay within
   `propext`, `Classical.choice` and `Quot.sound`.
2. Check the claims ledger (`claims.toml`) against the records and the lock
   (`claims.lock.json`): stale theorem names, changed statement hashes and
   theorems with forbidden axioms fail. Qualified Lean names cited in
   `docs/status.md` and the formal documents must still exist.
3. Render the "What is proved" table and, from bound source requests and typed
   receipts, one `zkc.assurance-report/0` per configured subject and the subject rows; compare each
   rendering with the generated region of its document when the document has
   one. A report is established only with the pipeline's evidence, so the
   subject rows are compared only by a run given `--evidence`.
4. Run the negative controls of the ledger check and the report generator in
   complete runs. `--subject` reports retain every live receipt check but omit
   this global regression suite; the result records that partial test coverage.

Without `--integration`, only the main package is emitted; a ledger row whose
theorem lives in an unselected package is skipped and counted. `--write`
rewrites the lock and the generated regions instead of failing on them.
"""

import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402
from records import controls, ledger, reports  # noqa: E402
from records.declarations import Records, emit, forbidden_axioms  # noqa: E402
from support.packages import selected as select_packages  # noqa: E402

LEAN = HERE.parent
ROOT = LEAN.parent
SUBJECTS = LEAN / "subjects"
FIXTURES = HERE / "fixtures/subjects"
README = LEAN / "README.md"
SUPPORT = LEAN / "docs/support.md"


def manifests(directory):
    """Subject manifests are TOML files with a name and entries."""
    import tomllib
    found = []
    for path in sorted(Path(directory).glob("*.toml")) if Path(directory).is_dir() else []:
        data = tomllib.loads(path.read_text())
        if "name" in data and "entries" in data:
            found.append(path)
    return found


def compare(document, region, rendered, write, failures, notes, subjects=None):
    text = document.read_text()
    current = ledger.region(text, region)
    if current is not None and subjects is not None:
        lines = current.splitlines()
        current = "\n".join(lines[:2] + [line for line in lines[2:]
                            if any(line.startswith(f"| {name} |") for name in subjects)]) + "\n"
    label = f"{document.relative_to(ROOT)}#{region}"
    if current is None:
        notes.append(f"{label}: no generated region; rendering kept under the output directory")
    elif current != rendered:
        if write:
            document.write_text(ledger.replace_region(text, region, rendered))
            notes.append(f"{label}: rewritten")
        else:
            failures.append(f"{label} is stale; run {ledger.COMMAND}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--integration", action="append", choices=["security", "arklib", "clean"], default=[])
    parser.add_argument("--records", type=Path, help="reuse emitted records from this directory")
    parser.add_argument("--output", type=Path, default=support.evidence.records("records", ""))
    parser.add_argument("--manifests", type=Path, help="subject manifests (default: lean/subjects)")
    parser.add_argument("--subject", action="append", help="render only named subjects; skip the complete subject table and global regression controls")
    parser.add_argument("--evidence", type=Path, help="per-subject pipeline evidence directory")
    parser.add_argument("--requirements", type=Path,
                        help="independent consumer requests; requires exactly one --subject")
    parser.add_argument("--write", action="store_true", help="rewrite the lock and generated regions")
    parser.add_argument("--determinism", action="store_true",
                        help="emit every package twice and require identical output")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--preflight", action="store_true",
                        help="check dependency sources before expensive validation; emit no claims")
    args = parser.parse_args()
    if args.subject and args.write:
        parser.error("--write requires the complete subject selection")
    consumer_requirements = None
    if args.requirements:
        if not args.subject or len(args.subject) != 1:
            parser.error("--requirements requires exactly one --subject")
        try:
            consumer_requirements = reports.read_consumer_requirements(args.requirements)
        except (OSError, ValueError) as error:
            parser.error(str(error))
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    packages = select_packages(list(dict.fromkeys(args.integration)))
    # Catch an unprepared or changed dependency before generating subjects or
    # traversing declarations. The report still verifies it at the final join.
    dependencies = []
    if args.preflight or not args.records:
        from support.packages import PACKAGES, check_closure
        for package in packages:
            directory = PACKAGES[package][0]
            check_closure(package, directory)
            if (directory / "lean-toolchain").read_bytes() != (LEAN / "lean-toolchain").read_bytes():
                raise SystemExit(f"dependency preflight failed: {package} toolchain mismatch")
        dependencies, dependency_reasons = reports.verified_dependencies(packages)
        if dependency_reasons:
            raise SystemExit("dependency preflight failed:\n" + "\n".join(dependency_reasons))
    if args.preflight:
        print(json.dumps(dict(status="pass", packages=packages, verified_dependencies=len(dependencies))))
        return
    subject_manifests = manifests(args.manifests or SUBJECTS)
    if args.subject:
        wanted = set(args.subject)
        known = {reports.load_manifest(path)["name"] for path in subject_manifests}
        if missing := wanted - known:
            parser.error(f"unknown subjects: {', '.join(sorted(missing))}")
        subject_manifests = [path for path in subject_manifests if reports.load_manifest(path)["name"] in wanted]
    samples = [] if subject_manifests or args.manifests else manifests(FIXTURES)
    details = [*controls.EMITTED_APPLICATIONS, *controls.EMITTED_HYPOTHESES] if "arklib" in packages else []
    for path in subject_manifests + samples:
        manifest = reports.load_manifest(path)
        evidence = reports.load_evidence(args.evidence, manifest["name"])
        details.extend(reports.claim_details(evidence))
    failures, notes = [], []

    paths = {}
    if args.records:
        for package in packages:
            paths[package] = args.records / f"{package}.jsonl"
    else:
        lake = str(Path(support.lake.resolve(args.lake)).absolute())
        for package in packages:
            target = output / "declarations" / f"{package}.jsonl"
            selected = details if package in {"security", "arklib"} else []
            with (output / f"emit-{package}.log").open("w") as log:
                result = emit(package, target, lake=lake, details=selected, log=log)
            # A signal death is a failure too, so success is the only accepted status.
            emitted = result.returncode == 0
            if not emitted:
                raise SystemExit(f"declaration records of {package} failed; see {output / f'emit-{package}.log'}")
            if args.determinism:
                again = output / "declarations" / f"{package}.again.jsonl"
                with (output / f"emit-{package}-again.log").open("w") as log:
                    result = emit(package, again, lake=lake, baseline=target, details=selected, log=log)
                if result.returncode == 0:
                    notes.append(f"declaration records of {package} are identical across two runs")
                else:
                    failures.append(f"declaration records of {package} are not deterministic")
            paths[package] = target
    records = Records.load(paths)

    forbidden = [f"{r['name']} ({r['module']}): {', '.join(forbidden_axioms(r))}"
                 for r in records.declarations if forbidden_axioms(r)]
    failures += [f"forbidden axioms: {line}" for line in forbidden]

    claims = ledger.load_ledger()
    lock = ledger.load_lock()
    if args.write:
        lock = ledger.write_lock(claims, lock, records)
        ledger.LOCK.write_text(json.dumps(lock, indent=2, ensure_ascii=False) + "\n")
    findings, checked, skipped = ledger.check(claims, lock, records)
    failures += findings
    cited, cited_checked, cited_skipped = ledger.check_documents(records)
    failures += cited

    table = ledger.render_proved(claims)
    (output / "what-is-proved.md").write_text(table)
    compare(README, "what-is-proved", table, args.write, failures, notes)

    built = []
    report_directory = output / "reports"
    report_directory.mkdir(exist_ok=True)
    for path in subject_manifests + samples:
        report = reports.build(path, records, claims, args.evidence, reused_records=args.records,
                               consumer_requirements=consumer_requirements)
        name = ("sample-" if path in samples else "") + report["subject"]
        (report_directory / f"{name}.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        if path in subject_manifests:
            built.append(report)
        if args.requirements and (report.get("requirements") or {}).get("status") != "certified":
            failures.append(f"{report['subject']}: consumer requirements remain unresolved")
    rows = reports.render_subjects(built)
    (output / "support-subjects.md").write_text(rows)
    if subject_manifests and "arklib" in packages and args.evidence is not None:
        compare(SUPPORT, "subject-rows", rows, args.write, failures, notes,
                subjects=set(args.subject) if args.subject else None)
        if args.subject:
            notes.append(f"subject table checked for: {', '.join(sorted(set(args.subject)))}")
    elif subject_manifests and "arklib" in packages:
        # A report is established only with the pipeline's evidence, so the rows a
        # run without it renders are not the subjects' outcomes; only a run with
        # evidence is compared.
        notes.append(f"{SUPPORT.relative_to(ROOT)}#subject-rows: not compared without --evidence")
    elif subject_manifests:
        # Without the security package the registry and endpoints are absent, so the
        # rows are incomplete; only a run that emits them is compared.
        notes.append(f"{SUPPORT.relative_to(ROOT)}#subject-rows: not compared without --integration arklib")
    if samples:
        notes.append(f"no subject manifests under {SUBJECTS.relative_to(ROOT)}; "
                     f"rendered sample reports from {FIXTURES.relative_to(ROOT)}")

    control_rows = []
    # Subject selection is a focused report run. Receipt validity is still
    # checked by reports.build above; these are the global regression tests.
    if not args.subject:
        control_rows = controls.run()
        receipt_rows, receipt_failures = controls.run_emitted_receipts(records)
        control_rows += receipt_rows
        failures += receipt_failures
        if "arklib" in packages:
            emitted_rows, emitted_failures = controls.run_emitted(records)
            control_rows += emitted_rows
            failures += emitted_failures
    summary = {
        "status": "fail" if failures else "pass",
        "packages": {package: records.headers[package].get("declarations") for package in packages},
        "ledger": {"rows": len(claims.get("proved", [])), "checked": len(checked), "skipped": len(skipped)},
        "document_names": {"checked": cited_checked, "skipped": cited_skipped},
        "reports": {report["subject"]: report["outcome"] for report in built},
        "control_coverage": "not-run-subject-selection" if args.subject else "all",
        "controls": control_rows,
        "failures": failures,
        "notes": notes,
    }
    (output / "result.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
