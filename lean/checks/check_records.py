#!/usr/bin/env python3
"""Audit fresh stored declarations, allowed axioms, theorem locks and documentation.

This command reports the maintained formal scope. It does not certify native
subjects or turn declaration metadata into a source/security connection.
"""

import argparse
import json
from pathlib import Path
import sys
import subprocess

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402
from records import controls, ledger  # noqa: E402
from records.declarations import Records, emit, forbidden_axioms  # noqa: E402
from support.packages import PACKAGES, add_selection, selection, check_closure  # noqa: E402
from reproduce import build_inputs  # noqa: E402

LEAN = HERE.parent
README = LEAN / "README.md"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_selection(parser)
    parser.add_argument("--records", type=Path, help="reuse records with an exact current input receipt")
    parser.add_argument("--output", type=Path, default=support.evidence.records("records", ""))
    parser.add_argument("--write", action="store_true", help="update reviewed theorem locks and table")
    parser.add_argument("--determinism", action="store_true", help="compare two fresh emissions")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--preflight", action="store_true", help="check dependencies without emitting claims")
    args = parser.parse_args()
    packages = selection(args)
    if not packages:
        parser.error("no maintained packages selected")
    for package in packages:
        directory = PACKAGES[package][0]
        check_closure(package, directory)
        if (directory / "lean-toolchain").read_bytes() != (LEAN / "lean-toolchain").read_bytes():
            raise ValueError(f"toolchain mismatch: {package}")
    if args.preflight:
        print(json.dumps({"status": "pass", "packages": packages, "coverage": "dependency-only"}))
        return
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    inputs = build_inputs(LEAN, packages)
    paths = {}
    if args.records:
        receipt = args.records.parent / "inputs.json"
        if not receipt.is_file() or json.loads(receipt.read_text()) != inputs:
            raise ValueError("declaration records have missing or stale source/dependency inputs")
        paths = {package: args.records / f"{package}.jsonl" for package in packages}
    else:
        lake = str(Path(support.lake.resolve(args.lake)).absolute())
        for package in packages:
            target = output / "declarations" / f"{package}.jsonl"
            log_path = output / f"emit-{package}.log"
            with log_path.open("w") as log:
                result = emit(package, target, lake=lake, log=log)
            try:
                result.check_returncode()
            except subprocess.CalledProcessError as error:
                raise RuntimeError(f"declaration emission failed for {package}: {log_path}") from error
            if args.determinism:
                again = target.with_suffix(".again.jsonl")
                with (output / f"emit-{package}-again.log").open("w") as log:
                    result = emit(package, again, lake=lake, baseline=target, log=log)
                try:
                    result.check_returncode()
                except subprocess.CalledProcessError as error:
                    raise RuntimeError(f"declaration determinism failed for {package}") from error
            paths[package] = target
    records = Records.load(paths)
    failures = [f"forbidden axioms: {row['name']} ({row['module']}): {forbidden_axioms(row)}"
                for row in records.declarations if forbidden_axioms(row)]
    claims = ledger.load_ledger()
    lock = ledger.load_lock()
    if args.write:
        lock = ledger.write_lock(claims, lock, records)
        ledger.LOCK.write_text(json.dumps(lock, indent=2, ensure_ascii=False) + "\n")
    findings, checked, skipped = ledger.check(claims, lock, records)
    failures += findings
    findings, cited_checked, cited_skipped = ledger.check_documents(records)
    failures += findings
    table = ledger.render_proved(claims)
    current = README.read_text()
    if ledger.region(current, "what-is-proved") != table:
        if args.write:
            README.write_text(ledger.replace_region(current, "what-is-proved", table))
        else:
            failures.append("lean/README.md#what-is-proved is missing or stale")
    rows = controls.run()
    failures += [f"control failed: {row['name']}" for row in rows if row['status'] != 'pass']
    # Updating locks/docs is intentional; proof inputs may not drift during extraction.
    final_inputs = build_inputs(LEAN, packages)
    if final_inputs != inputs:
        failures.append("source or checking dependencies changed during declaration extraction")
    (output / "inputs.json").write_text(json.dumps(inputs, sort_keys=True, indent=2) + "\n")
    summary = {"status": "fail" if failures else "pass",
               "packages": {name: records.headers[name]['declarations'] for name in packages},
               "ledger": {"rows": len(claims['proved']), "checked": len(checked), "skipped": len(skipped)},
               "document_names": {"checked": cited_checked, "skipped": cited_skipped},
               "controls": rows, "failures": failures,
               "coverage": "maintained-declarations-and-ledger"}
    (output / "result.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key != 'controls'}, indent=2))
    raise SystemExit(bool(failures))


if __name__ == '__main__':
    main()
