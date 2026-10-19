#!/usr/bin/env python3
"""Check the records of what is proved and render tables and assurance reports.

1. Emit one declaration record per owned declaration of the selected packages
   (`DeclarationRecords.lean`), and require every axiom closure to stay within
   `propext`, `Classical.choice` and `Quot.sound`.
2. Check the claims ledger (`claims.toml`) against the records and the lock
   (`claims.lock.json`): stale theorem names, changed statement hashes and
   theorems with forbidden axioms fail. Qualified Lean names cited in
   `docs/status.md` and the formal documents must still exist.
3. Render the "What is proved" table and, from subject manifests, one
   `zkc.assurance-report/0` per subject and the subject rows; compare each
   rendering with the generated region of its document when the document has
   one.
4. Run the negative controls of the ledger check and the report generator.

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

LEAN = HERE.parent
ROOT = LEAN.parent
SUBJECTS = LEAN / "subjects"
FIXTURES = HERE / "fixtures/subjects"
README = LEAN / "README.md"
SUPPORT = LEAN / "docs/support.md"


def manifests(directory):
    """Subject manifests: TOML files with a name and entries (other TOML files,
    such as normal-form requests, are ignored)."""
    import tomllib
    found = []
    for path in sorted(Path(directory).glob("*.toml")) if Path(directory).is_dir() else []:
        data = tomllib.loads(path.read_text())
        if "name" in data and "entries" in data:
            found.append(path)
    return found


def compare(document, region, rendered, write, failures, notes):
    text = document.read_text()
    current = ledger.region(text, region)
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
    parser.add_argument("--integration", action="append", choices=["arklib", "clean"], default=[])
    parser.add_argument("--records", type=Path, help="reuse emitted records from this directory")
    parser.add_argument("--output", type=Path, default=support.evidence.records("records", ""))
    parser.add_argument("--manifests", type=Path, help="subject manifests (default: lean/subjects)")
    parser.add_argument("--evidence", type=Path, help="per-subject pipeline evidence directory")
    parser.add_argument("--write", action="store_true", help="rewrite the lock and generated regions")
    parser.add_argument("--determinism", action="store_true",
                        help="emit every package twice and require identical output")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    packages = ["main", *dict.fromkeys(args.integration)]
    subject_manifests = manifests(args.manifests or SUBJECTS)
    samples = [] if subject_manifests or args.manifests else manifests(FIXTURES)
    details = []
    for path in subject_manifests + samples:
        instance = (reports.load_manifest(path).get("family") or {}).get("instance")
        if instance:
            details.append(instance)
    failures, notes = [], []

    paths = {}
    if args.records:
        for package in packages:
            paths[package] = args.records / f"{package}.jsonl"
    else:
        lake = str(Path(support.lake.resolve(args.lake)).absolute())
        for package in packages:
            target = output / "declarations" / f"{package}.jsonl"
            selected = [name for name in details if package == "arklib"]
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
        report = reports.build(path, records, claims, args.evidence)
        name = ("sample-" if path in samples else "") + report["subject"]
        (report_directory / f"{name}.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        if path in subject_manifests:
            built.append(report)
    rows = reports.render_subjects(built)
    (output / "support-subjects.md").write_text(rows)
    if subject_manifests:
        compare(SUPPORT, "subject-rows", rows, args.write, failures, notes)
    if samples:
        notes.append(f"no subject manifests under {SUBJECTS.relative_to(ROOT)}; "
                     f"rendered sample reports from {FIXTURES.relative_to(ROOT)}")

    control_rows = controls.run()
    summary = {
        "status": "fail" if failures else "pass",
        "packages": {package: records.headers[package].get("declarations") for package in packages},
        "ledger": {"rows": len(claims.get("proved", [])), "checked": len(checked), "skipped": len(skipped)},
        "document_names": {"checked": cited_checked, "skipped": cited_skipped},
        "reports": {report["subject"]: report["outcome"] for report in built},
        "controls": control_rows,
        "failures": failures,
        "notes": notes,
    }
    (output / "result.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
