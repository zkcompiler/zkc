"""A pinned Clean export against native finite-AIR and shared ring evaluation.

The control is the output of the Lean producer in lean/integrations/clean;
`just test-lean-clean` requires it to be byte-identical to a fresh run. Its
export residuals come from Clean's own expressions on each row and its mutant
residuals from the zkc AIR model. The C++ tool admits and evaluates every
relation with the native finite AIR and derives `AIR::expressionView` arenas;
the Rust driver admits every arena independently and evaluates it with the
KoalaBear/Ext8 ring provider. This file compares strings and computes no
field arithmetic. Agreement on these rows is evidence, not a proof that the
native readers or providers implement the Lean statements.
"""
from copy import deepcopy
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
CONTROL = ROOT / "common/tests/fixtures/clean/air-control.json"
MANIFEST = ROOT / "lean/integrations/clean/lake-manifest.json"

# Clean's verdicts, stated independently of the producer: generated rows inside
# toBits' prover assumption and the kernel control row `six` hold; generated
# rows for 16 and p - 1 and the constructed rows fail.
FAILING = {
    "to-bits-4": {"input-16", "input-2130706432", "wrong-bit", "non-boolean"},
    "is-equal-2": {"flipped-flag", "wrong-inverse"},
}
# The row on which each mutant disagrees with Clean is the row of its kernel
# refutation in lean/integrations/clean/TestsClean/Bits.lean.
DETECTED = {"altered-constant": "six", "altered-column": "six", "deleted-assertion": "non-boolean"}


def canonical(document):
    return json.dumps(document, separators=(",", ":"), sort_keys=True) + "\n"


def native_tool(toolchain):
    return toolchain.tool("compiler", "test/zkc-clean_air_conformance-test")


def test_clean_export_agrees_with_native_evaluation(toolchain, journal, directory):
    text = CONTROL.read_text()
    control = json.loads(text)
    assert canonical(control) == text, "the control is one canonical JSON line"
    pins = {package["name"]: package for package in json.loads(MANIFEST.read_text())["packages"]}
    assert control["source"] == {"repository": pins["Clean"]["url"], "revision": pins["Clean"]["rev"]}

    native_text = journal.run([native_tool(toolchain), CONTROL], keep="native")
    native = json.loads(native_text)
    report = directory / "native.json"
    report.write_text(native_text)
    ring = journal.json([toolchain.driver("clean_air_conformance"), CONTROL, report], keep="ring")
    assert native["status"] == ring["status"] == "pass"
    journal.check("provider packing width recorded", ring["packing_width"] >= 1, ring["packing_width"])

    for component, cpp, rust in zip(control["components"], native["components"], ring["components"]):
        name = component["name"]
        rows = [row["name"] for row in component["rows"]]
        assert cpp["rows"] == rows and cpp["width"] == len(component["rows"][0]["cells"])
        export = component["subjects"][0]
        expected = [row["name"] not in FAILING[name] for row in component["rows"]]
        journal.check(f"{name}: Clean verdicts", [row["holds"] for row in export["rows"]] == expected)
        for subject, cpp_subject, rust_subject in zip(component["subjects"], cpp["subjects"], rust["subjects"]):
            label = f"{name}/{subject['name']}"
            residuals = [row["residuals"] for row in subject["rows"]]
            journal.check(f"{label}: C++ finite AIR residuals", cpp_subject["residuals"] == residuals)
            journal.check(f"{label}: Rust relation-arena residuals", rust_subject["residuals"] == residuals)
            journal.check(f"{label}: one ring view per assertion",
                          len(cpp_subject["views"]) == rust_subject["views"] == len(residuals[0]))
            journal.check(f"{label}: arena identities agree",
                          cpp_subject["arena_identity"] == rust_subject["arena_identity"])
            if subject["name"] == "export":
                continue
            # Formation is not identity: an admitted mutant is a different artifact.
            journal.check(f"{label}: distinct relation identity",
                          cpp_subject["relation_identity"] != cpp["subjects"][0]["relation_identity"])
            journal.check(f"{label}: distinct arena identity",
                          cpp_subject["arena_identity"] != cpp["subjects"][0]["arena_identity"])
            row = rows.index(DETECTED[subject["name"]])
            journal.check(f"{label}: disagrees with Clean at {rows[row]}",
                          cpp_subject["holds"][row] != export["rows"][row]["holds"])


def edit(path, value):
    """Replace, or transform with a function, the value at a path of keys and indices."""
    def apply(document):
        target = document
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value(target[path[-1]]) if callable(value) else value
    return apply


EXPORT = ["components", 0, "subjects", 0]
NODES = [*EXPORT, "relation", "constraints", 4, "nodes"]


def residual_and_verdict(document):
    row = document["components"][0]["subjects"][0]["rows"][6]
    row["residuals"][4] = "1"
    row["holds"] = False


def mutant_is_export(document):
    subjects = document["components"][0]["subjects"]
    subjects[1] = {**deepcopy(subjects[0]), "name": "altered-constant", "reference": "model"}


def arena_differs_from_relation(document):
    # The weight 4 of bit three in the recomposition: only the arena changes.
    # (Weight 2 -> 3 would reproduce the altered-constant mutant's arena, which
    # the native side reports as a mutant equal to the export.)
    nodes = document["components"][0]["subjects"][0]["arena"][2]
    index = nodes.index(["constant", "koala-bear", "4"])
    nodes[index] = ["constant", "koala-bear", "5"]


# Each case changes a canonical control; the C++ tool must name the outcome.
NATIVE_CASES = {
    "altered-clean-residual": (residual_and_verdict, ["clean-residual", "clean-verdict"]),
    "inconsistent-verdict": (edit([*EXPORT, "rows", 6, "holds"], False), ["clean-control-holds"]),
    "presentation-modulus": (edit(["presentation", "modulus"], "2130706432"), ["clean-presentation"]),
    "presentation-field": (edit(["presentation", "field"], "bn254.fr"), ["clean-presentation"]),
    "noncanonical-constant": (edit([*NODES, 1, "value"], "2130706433"), ["relation-coefficient"]),
    "column-out-of-range": (edit([*NODES, 0, "column"], 5), ["air-column"]),
    "first-row-scope": (edit([*EXPORT, "relation", "constraints", 0, "scope", "kind"], "first"),
                        ["clean-relation-shape"]),
    "public-input": (edit([*EXPORT, "relation", "public_inputs"], 1), ["clean-relation-shape"]),
    "mutant-equals-export": (mutant_is_export, ["clean-mutant-identity"]),
    "row-limit": (edit(["components", 0, "rows"], lambda rows: (rows * 13)[:257]), ["clean-control-limit"]),
}


@pytest.mark.parametrize("case", sorted(NATIVE_CASES))
def test_native_side_names_each_refusal(toolchain, journal, directory, case):
    change, codes = NATIVE_CASES[case]
    document = json.loads(CONTROL.read_text())
    change(document)
    path = directory / "control.json"
    path.write_text(canonical(document))
    result = journal.parse(journal.attempt([native_tool(toolchain), path], keep="native"))
    assert journal.last.returncode == 1, result
    found = {result.get("code")} | {entry["code"] for entry in result.get("disagreements", [])}
    assert set(codes) <= found, (codes, result)


def test_native_side_refuses_noncanonical_and_oversized_controls(toolchain, journal, directory):
    text = CONTROL.read_text()
    spaced = directory / "spaced.json"
    spaced.write_text("{ " + text[1:])
    journal.run([native_tool(toolchain), spaced], refuses="clean-control-canonical")
    oversized = directory / "oversized.json"
    oversized.write_text(text[:-1] + " " * (1 << 20) + "\n")
    journal.run([native_tool(toolchain), oversized], refuses="clean-control-limit")


def native_report(toolchain, journal, directory, control):
    report = directory / "native.json"
    report.write_text(journal.run([native_tool(toolchain), control]))
    return report


def test_ring_side_detects_a_relation_arena_change(toolchain, journal, directory):
    document = json.loads(CONTROL.read_text())
    arena_differs_from_relation(document)
    control = directory / "control.json"
    control.write_text(canonical(document))
    # The C++ side evaluates the unchanged relation and still agrees.
    report = native_report(toolchain, journal, directory, control)
    result = journal.parse(journal.attempt([toolchain.driver("clean_air_conformance"), control, report]))
    assert journal.last.returncode == 1
    six = [row["name"] for row in document["components"][0]["rows"]].index("six")
    assert {"code": "clean-residual", "at": {"component": "to-bits-4", "subject": "export",
            "source": "relation-arena", "row": six, "constraint": 4}} in result["disagreements"]


def report_edit(report_path, change):
    report = json.loads(report_path.read_text())
    change(report)
    report_path.write_text(json.dumps(report))


def tamper_view(report):
    view = report["components"][0]["subjects"][0]["views"][4]
    nodes = view["arena"][2]
    index = next(i for i, node in enumerate(nodes) if node == ["constant", "koala-bear", "2"])
    nodes[index] = ["constant", "koala-bear", "3"]


RING_CASES = {
    "tampered-view-arena": (tamper_view, ["clean-view-identity", "clean-residual"]),
    "read-at-next-row": (edit(["components", 0, "subjects", 0, "views", 0, "reads", 0, 0], 1), ["clean-binding"]),
    "column-beyond-width": (edit(["components", 0, "subjects", 0, "views", 0, "reads", 0, 1], 5), ["clean-binding"]),
    "other-control": (edit(["control_sha256"], "0" * 64), ["clean-report-binding"]),
}


@pytest.mark.parametrize("case", sorted(RING_CASES))
def test_ring_side_names_each_refusal(toolchain, journal, directory, case):
    change, codes = RING_CASES[case]
    report = native_report(toolchain, journal, directory, CONTROL)
    report_edit(report, change)
    result = journal.parse(journal.attempt([toolchain.driver("clean_air_conformance"), CONTROL, report]))
    assert journal.last.returncode == 1, result
    found = {result.get("code")} | {entry["code"] for entry in result.get("disagreements", [])}
    assert set(codes) <= found, (codes, result)


def test_ring_side_refuses_another_presentation(toolchain, journal, directory):
    report = native_report(toolchain, journal, directory, CONTROL)
    document = json.loads(CONTROL.read_text())
    document["presentation"] = {"field": "bn254.fr", "modulus": document["presentation"]["modulus"]}
    control = directory / "other.json"
    control.write_text(canonical(document))
    journal.run([toolchain.driver("clean_air_conformance"), control, report], refuses="clean-presentation")
