#!/usr/bin/env python3
"""Generate and independently check the bounded F1-R mutation corpus."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any


HERE = Path(__file__).resolve().parent
CASES_PATH = HERE / "cases.json"
EXPECTED_AGREEMENTS_PATH = HERE / "expected-agreements.json"
EXPORTER = HERE / "exporter.py"
PYTHON_CHECKER = HERE / "python_checker.py"
RUST_CHECKER = HERE / "rust_checker.rs"


class GateFailure(RuntimeError):
    pass


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise GateFailure(f"duplicate JSON field {key!r}")
        result[key] = value
    return result


def load_json_text(text: str, label: str) -> Any:
    try:
        return json.loads(text, object_pairs_hook=strict_object)
    except (json.JSONDecodeError, GateFailure) as error:
        raise GateFailure(f"{label} is not strict JSON: {error}") from error


def load_cases() -> list[dict[str, str]]:
    try:
        raw = CASES_PATH.read_text(encoding="utf-8")
    except OSError as error:
        raise GateFailure(f"cannot read {CASES_PATH}: {error}") from error
    value = load_json_text(raw, "case ledger")
    if type(value) is not list or not value:
        raise GateFailure("case ledger is not a nonempty array")
    cases: list[dict[str, str]] = []
    names: set[str] = set()
    for ordinal, item in enumerate(value):
        if type(item) is not dict or set(item) != {
            "expected_class",
            "expected_code",
            "name",
        }:
            raise GateFailure(f"case row {ordinal} has the wrong shape")
        if any(type(item[key]) is not str or not item[key] for key in item):
            raise GateFailure(f"case row {ordinal} has a non-text field")
        if item["name"] in names:
            raise GateFailure(f"case ledger repeats {item['name']!r}")
        names.add(item["name"])
        cases.append(item)
    return cases


def load_expected_agreements() -> dict[str, dict[str, str]]:
    try:
        raw = EXPECTED_AGREEMENTS_PATH.read_text(encoding="utf-8")
    except OSError as error:
        raise GateFailure(
            f"cannot read {EXPECTED_AGREEMENTS_PATH}: {error}"
        ) from error
    value = load_json_text(raw, "expected agreement ledger")
    if type(value) is not dict or not value:
        raise GateFailure("expected agreement ledger is not a nonempty object")
    fields = {
        "contract_id",
        "manifest_id",
        "package_id",
        "proposition_id",
        "result_id",
    }
    for name, row in value.items():
        if type(name) is not str or type(row) is not dict or set(row) != fields:
            raise GateFailure("expected agreement ledger has a malformed row")
        for key, digest in row.items():
            if (
                type(digest) is not str
                or not digest.startswith("sha256:")
                or len(digest) != 71
            ):
                raise GateFailure(f"expected agreement {name} has malformed {key}")
    return value


def run_command(command: list[str], label: str) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        command,
        cwd=HERE.parents[1],
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise GateFailure(f"{label} failed with exit {completed.returncode}: {detail}")
    return completed


def compile_rust(output: Path) -> None:
    run_command(
        [
            "rustc",
            "--edition=2021",
            "-D",
            "warnings",
            str(RUST_CHECKER),
            "-o",
            str(output),
        ],
        "standalone Rust checker build",
    )


def expected_exit(outcome_class: str) -> int:
    if outcome_class == "Affirmative":
        return 0
    if outcome_class == "Negative":
        return 1
    return 2


def invoke_checker(
    command: list[str],
    package: Path,
    expected_checker: str,
) -> tuple[dict[str, Any], int, str]:
    completed = subprocess.run(
        [*command, str(package)],
        cwd=HERE.parents[1],
        check=False,
        capture_output=True,
        text=True,
    )
    envelope = load_json_text(completed.stdout, f"{expected_checker} output")
    if type(envelope) is not dict or set(envelope) != {"checker", "outcome"}:
        raise GateFailure(f"{expected_checker} emitted the wrong envelope")
    if envelope["checker"] != expected_checker:
        raise GateFailure(
            f"checker identity mismatch: expected {expected_checker!r}, "
            f"got {envelope['checker']!r}"
        )
    outcome = envelope["outcome"]
    if type(outcome) is not dict:
        raise GateFailure(f"{expected_checker} outcome is not an object")
    if type(outcome.get("class")) is not str or type(outcome.get("code")) is not str:
        raise GateFailure(f"{expected_checker} outcome lacks class/code")
    return outcome, completed.returncode, completed.stderr.strip()


def check_affirmative_shape(outcome: dict[str, Any], label: str) -> None:
    expected = {
        "class",
        "code",
        "contract_id",
        "manifest_id",
        "package_id",
        "proposition_id",
        "required_reads",
        "result_id",
        "root_ids",
    }
    if set(outcome) != expected:
        raise GateFailure(f"{label} affirmative result has the wrong fields")
    for key in (
        "contract_id",
        "manifest_id",
        "package_id",
        "proposition_id",
        "result_id",
    ):
        value = outcome[key]
        if (
            type(value) is not str
            or not value.startswith("sha256:")
            or len(value) != 71
        ):
            raise GateFailure(f"{label} has malformed {key}")
    reads = outcome["required_reads"]
    if type(reads) is not list or reads != sorted(set(reads)) or not reads:
        raise GateFailure(f"{label} has a noncanonical required-read set")
    roots = outcome["root_ids"]
    if type(roots) is not list or not roots:
        raise GateFailure(f"{label} has no root IDs")
    coordinates = []
    for row in roots:
        if type(row) is not dict or set(row) != {"coordinate", "id"}:
            raise GateFailure(f"{label} has a malformed root-ID row")
        coordinates.append(row["coordinate"])
    if coordinates != sorted(set(coordinates)):
        raise GateFailure(f"{label} root IDs are not coordinate-sorted-unique")


def run_gate() -> dict[str, Any]:
    cases = load_cases()
    expected_agreements = load_expected_agreements()
    with tempfile.TemporaryDirectory(prefix="zkc-f1r-") as raw_temp:
        temp = Path(raw_temp)
        corpus = temp / "corpus"
        rust_binary = temp / "rust-checker"
        run_command(
            [sys.executable, "-B", str(EXPORTER), "--output", str(corpus)],
            "untrusted exporter",
        )
        compile_rust(rust_binary)

        expected_files = {f"{case['name']}.json" for case in cases}
        actual_files = {path.name for path in corpus.iterdir() if path.is_file()}
        if actual_files != expected_files:
            raise GateFailure(
                "exporter corpus differs from the case ledger: "
                f"missing={sorted(expected_files - actual_files)}, "
                f"extra={sorted(actual_files - expected_files)}"
            )
        fresh_wire = (corpus / "fresh-positive.json").read_text(encoding="ascii")
        authentication_at = fresh_wire.find('"authentication"')
        package_id_at = fresh_wire.find('"asserted_package_id"')
        if (
            authentication_at < 0
            or package_id_at < 0
            or authentication_at > package_id_at
        ):
            raise GateFailure(
                "producer no longer exercises noncanonical object-key order"
            )

        rows: list[dict[str, Any]] = []
        affirmative: dict[str, dict[str, Any]] = {}
        for case in cases:
            package = corpus / f"{case['name']}.json"
            python_outcome, python_exit, python_stderr = invoke_checker(
                [sys.executable, "-B", str(PYTHON_CHECKER)],
                package,
                "python-stdlib-v0",
            )
            rust_outcome, rust_exit, rust_stderr = invoke_checker(
                [str(rust_binary)],
                package,
                "rust-standalone-v0",
            )
            wanted = (case["expected_class"], case["expected_code"])
            for checker, outcome, exit_code, stderr in (
                ("python", python_outcome, python_exit, python_stderr),
                ("rust", rust_outcome, rust_exit, rust_stderr),
            ):
                observed = (outcome["class"], outcome["code"])
                if observed != wanted:
                    raise GateFailure(
                        f"{case['name']} {checker} outcome {observed!r} "
                        f"differs from {wanted!r}; diagnostic={stderr!r}"
                    )
                wanted_exit = expected_exit(case["expected_class"])
                if exit_code != wanted_exit:
                    raise GateFailure(
                        f"{case['name']} {checker} exit {exit_code} "
                        f"differs from {wanted_exit}"
                    )
            if (
                python_outcome["class"],
                python_outcome["code"],
            ) != (rust_outcome["class"], rust_outcome["code"]):
                raise GateFailure(f"checkers disagree on {case['name']}")
            if case["expected_class"] == "Affirmative":
                check_affirmative_shape(python_outcome, case["name"])
                if python_outcome != rust_outcome:
                    raise GateFailure(
                        f"checkers disagree on the full agreement for {case['name']}"
                    )
                affirmative[case["name"]] = python_outcome
            rows.append(
                {
                    "class": case["expected_class"],
                    "code": case["expected_code"],
                    "name": case["name"],
                }
            )

        positive_names = {
            "fresh-positive",
            "fs-positive",
            "shared-positive",
        }
        if set(affirmative) != positive_names:
            raise GateFailure("positive package set differs from the fixed discriminator set")
        if set(expected_agreements) != positive_names:
            raise GateFailure("expected agreement ledger names the wrong positive set")
        agreement_fields = tuple(next(iter(expected_agreements.values())))
        observed_agreements = {
            name: {key: outcome[key] for key in agreement_fields}
            for name, outcome in affirmative.items()
        }
        if observed_agreements != expected_agreements:
            raise GateFailure("positive agreement identities differ from frozen controls")
        package_ids = {outcome["package_id"] for outcome in affirmative.values()}
        proposition_ids = {
            outcome["proposition_id"] for outcome in affirmative.values()
        }
        if len(package_ids) != 3 or len(proposition_ids) != 3:
            raise GateFailure("distinct positive subjects alias an identity")

        return {
            "affirmative": len(affirmative),
            "cases": rows,
            "checkers": ["python-stdlib-v0", "rust-standalone-v0"],
            "fresh_agreement": {
                key: affirmative["fresh-positive"][key]
                for key in (
                    "contract_id",
                    "manifest_id",
                    "package_id",
                    "proposition_id",
                    "result_id",
                )
            },
            "mutations": len(cases) - len(affirmative),
            "total": len(cases),
        }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the focused F1-R feasibility gate",
    )
    args = parser.parse_args(argv)
    if not args.check:
        parser.error("the research runner currently supports only --check")
    try:
        report = run_gate()
    except (GateFailure, OSError) as error:
        print(f"F1-R source-package gate failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True))
    print(
        "F1-R source-package feasibility: "
        f"{report['total']}/{report['total']} cases passed "
        f"({report['affirmative']} affirmative, {report['mutations']} mutations; "
        "2 independent checkers)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
