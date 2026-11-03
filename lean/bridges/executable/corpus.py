#!/usr/bin/env python3
"""Run the shared program byte corpus through the native decoder, then the Lean
program reader, and compare their admission decisions.

This is differential coverage of the Lean reader of decoded programs, not an
independent Lean byte reader. The native decoder (`zkc-program_codec-test
--report`) parses and admits each case's exact bytes. For an admitted case, its
re-encoded program is decoded by the shared renderer (`render.render_program`)
and admitted by `Zkc.Executable.ProgramAdmission`. A natively refused case whose
wire is one JSON value is read the same way, with Python's JSON parser standing
in for the byte layer.

The comparison follows the profile Lean claims:

* a natively admitted case must be admitted, unless the renderer or Lean names
  it outside the profile (a type or instruction outside the Lean vocabulary);
* a natively refused case whose rule Lean claims (`CLAIMED`) must be refused,
  by the renderer or by Lean, and a Lean refusal must name the native class;
  a case outside the profile is not compared;
* a natively refused case whose rule Lean does not claim, such as a carrier
  bound, an installed contract or a local type, is recorded but not compared,
  and a case whose wire is not one JSON value is not reached.

A case whose rendered Lean term exceeds the elaboration budget is recorded as
not compared; the corpus's bound cases are the only ones that reach it.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.append(str(ROOT / "lean"))
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.executable import render  # noqa: E402

CORPUS = ROOT / "common/tests/fixtures/program/bytes.json"
CLASSES = {"syntax": "syntax", "namesAndSsa": "names-and-ssa", "types": "types", "affineUse": "affine-use",
           "unsupportedProfile": "unsupported-profile", "outside": "outside"}

# The native refusals (class, code) whose rule the Lean reader claims: record
# shapes the renderer decodes, and the declaration, lexical, capture, signature
# and terminator rules of `Zkc.Executable.ProgramAdmission`.
CLAIMED = {
    ("syntax", code) for code in (
        "interactive-record", "invalid-shape", "binding-logical-origin", "interactive-return",
        "interactive-instruction", "native-boolean-context", "interactive-loop-count", "interactive-entry-targets",
        "interactive-entry", "interactive-format", "interactive-shape", "interactive-if-shape", "interactive-body",
        "interactive-terminator", "service-port-index", "interactive-stop-reason", "local-terminal-context")
} | {
    ("names-and-ssa", code) for code in (
        "interactive-unavailable", "interactive-ssa", "interactive-argument", "interactive-duplicate-symbol",
        "interactive-local-symbol", "interactive-entry-role", "interactive-entry-instance", "interactive-entry-name",
        "interactive-binding", "interactive-site", "interactive-peer", "interactive-loop-input",
        "interactive-loop-capture", "interactive-loop-count", "interactive-branch-capture", "interactive-receive",
        "service-port-interface", "binding-reference", "interactive-participant-identity")
} | {
    ("types", code) for code in (
        "local-if-condition", "interactive-local-signature", "interactive-schema-type", "interactive-return",
        "interactive-loop-count", "interactive-receive", "local-if-yield", "local-yield-types",
        "function-return-types", "local-terminal-outputs")
} | {
    ("affine-use", code) for code in ("interactive-resource-reuse", "interactive-loop-capture",
                                      "local-control-capture")
}

PRELUDE = """import Zkc.Executable.ProgramAdmission

open Zkc.Construction Zkc.Executable

-- Bound cases carry lists of thousands of rows.
set_option maxRecDepth 65536

def verdict (name : String) : Admitting Unit → String
  | .ok () => s!"{name} admitted"
  | .error refusal => s!"{name} refused {reprStr refusal.kind} {refusal.reason}"

"""


def wire(value):
    """One string, or segments whose repeats write `{i}` as 0..count."""
    if isinstance(value, str):
        return value
    out = []
    for segment in value:
        if isinstance(segment, str):
            out.append(segment)
        else:
            out.append(segment["separator"].join(
                segment["repeat"].replace("{i}", str(i)) for i in range(segment["count"])))
    return "".join(out)


def native(codec, text):
    result = subprocess.run([str(codec), "--report"], input=text, capture_output=True, text=True, timeout=120)
    if result.returncode != 0:
        raise AssertionError(f"native decoder failed: {result.stderr}")
    return json.loads(result.stdout)


def lean_class(text):
    """The admission class a printed `AdmissionClass` names."""
    name = text.rsplit(".", 1)[-1]
    if name not in CLASSES:
        raise AssertionError(f"unknown Lean admission class {text!r}")
    return CLASSES[name]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--codec", type=Path, required=True, help="the native zkc-program_codec-test")
    parser.add_argument("--output", type=Path, required=True, help="directory for the Lean input and the report")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--elaboration-budget", type=int, default=1 << 18,
                        help="the largest rendered program term, in bytes, given to Lean")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    corpus = json.loads(CORPUS.read_text())
    if corpus["format"] != "zkc.program-byte-fixtures/0":
        raise AssertionError("unexpected corpus format")

    rows, terms = [], []
    for index, item in enumerate(corpus["cases"]):
        text = wire(item["wire"])
        expected = "admitted" if "admitted" in item else item["refused"]
        report = native(args.codec, text)
        decision = report[0] if report[0] == "admitted" else report[1]
        if decision != expected:
            raise AssertionError(f"{item['name']}: native decoder {report[:2]} differs from the corpus {expected}")
        row = {"name": item["name"], "native": decision, "code": report[2] if decision != "admitted" else None}
        rows.append(row)
        if decision == "admitted":
            value = report[1]
        else:
            try:
                value = json.loads(text)
            except ValueError:
                row["lean"] = "not-reached"
                continue
        try:
            term = render.render_program(value, "Corpus")
        except Refused as error:
            message = str(error)
            row["lean"] = "outside" if message.startswith("unsupported physical type") else "decoder-refused"
            row["reason"] = message[:200]
            continue
        except (UnicodeError, RecursionError, TypeError, ValueError) as error:
            row["lean"] = "decoder-refused"
            row["reason"] = f"{type(error).__name__}: {str(error)[:160]}"
            continue
        if len(term) > args.elaboration_budget:
            row["lean"] = "not-compared"
            row["reason"] = f"rendered term of {len(term)} bytes exceeds the elaboration budget"
            continue
        row["case"] = f"case{index}"
        terms.append((row["case"], term))

    source = PRELUDE + "".join(f"def {name} : ProgramArtifact :=\n  {term}\n\n" for name, term in terms) + "".join(
        f'#eval IO.println (verdict "{name}" (ProgramArtifact.admit {name}))\n' for name, _ in terms)
    lean_input = args.output / "Corpus.lean"
    lean_input.write_text(source)
    result = subprocess.run([args.lake, "env", "lean", str(lean_input)], cwd=ROOT / "lean", capture_output=True,
                            text=True, timeout=3600)
    if result.returncode != 0:
        raise AssertionError(f"Lean failed on {lean_input}:\n{result.stdout[-4000:]}\n{result.stderr[-4000:]}")
    verdicts = {}
    for line in result.stdout.splitlines():
        parts = line.split(" ", 3)
        if len(parts) >= 2 and parts[0].startswith("case"):
            verdicts[parts[0]] = parts[1:]
    for row in rows:
        if "case" not in row:
            continue
        verdict = verdicts.pop(row.pop("case"))
        if verdict[0] == "admitted":
            row["lean"] = "admitted"
        else:
            row["lean"] = lean_class(verdict[1])
            row["reason"] = verdict[2] if len(verdict) > 2 else ""
    if verdicts:
        raise AssertionError(f"unexpected Lean verdicts {sorted(verdicts)}")

    disagreements = []
    for row in rows:
        lean, native_class = row["lean"], row["native"]
        if lean in ("outside", "not-compared", "not-reached"):
            row["comparison"] = lean
        elif native_class == "admitted":
            row["comparison"] = "agree" if lean == "admitted" else "disagree"
        elif (native_class, row["code"]) not in CLAIMED:
            row["comparison"] = "unclaimed"
        elif lean == "decoder-refused" or lean == native_class:
            row["comparison"] = "agree"
        else:
            row["comparison"] = "disagree"
        if row["comparison"] == "disagree":
            disagreements.append(row)
    counts = {}
    for row in rows:
        key = f"{'admitted' if row['native'] == 'admitted' else 'refused'}:{row['comparison']}"
        counts[key] = counts.get(key, 0) + 1
    report = {"format": "zkc.lean-program-corpus/0", "codec": str(args.codec), "cases": len(rows),
              "counts": dict(sorted(counts.items())), "rows": rows}
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(rows), "counts": report["counts"]}))
    if disagreements:
        for row in disagreements:
            print("DISAGREE", json.dumps(row), file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
