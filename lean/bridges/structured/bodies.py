#!/usr/bin/env python3
"""Print literal typed bodies of an admitted structured unit as a Lean module.

The script writes a scratch Lean file that admits the snapshot with the checker
itself, materializes each checked helper body, protocol body and (for the
closed profile) the projected root with `region_view%`, and prints them. It then
rewrites the printed terms as `<|` chains in the style of the authored body
modules. The output is ordinary source: `structured_views` or
`structured_closed_views` must still admit the snapshot from it, so a printing
or formatting error is rejected by the kernel rather than trusted.

Usage, from the repository root inside the development shell, after building
the data module:
  python3 lean/bridges/structured/bodies.py \\
    --data ZkcExamples.Structured.SchnorrHelpersData \\
    --namespace ZkcExamples.Structured.SchnorrHelpersBodies \\
    [--closed] [--name DIGEST=localName ...] --output PATH
"""

import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"

PRINTER = r'''
import Zkc.Source.RegionView
import Zkc.Source.Structured.ClosedProfile
import {data}

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
noncomputable section

namespace Printed
open Zkc.Source Zkc.Source.Structured

def program : Program := (check {data}.snapshot).toOption.get (by decide +kernel)

def showTy : Ty → String
  | .boolean => ".boolean" | .index => ".index"
  | .field d => s!"(.field \"{{d}}\")" | .vector d => s!"(.vector \"{{d}}\")"
  | .group d => s!"(.group \"{{d}}\")" | .service c => s!"(.service \"{{c}}\")"

def showTys (types : List Ty) : String := "[" ++ ", ".intercalate (types.map showTy) ++ "]"

def showRoles (roles : List String) : String :=
  "[" ++ ", ".intercalate (roles.map fun role => "\"" ++ role ++ "\"") ++ "]"

#eval IO.println s!"HELPERS {{program.payload.definitions.length}}"
#eval for definition in program.payload.definitions do
  IO.println s!"HELPER\t{{definition.name}}\t{{match definition.kind with | .math => ".math" | .local => ".local"}}\t{{showTys definition.inputs}}\t{{showTys definition.outputs}}"
#eval for protocol in program.payload.protocols do
  IO.println s!"PROTOCOL\t{{protocol.name}}\t{{showRoles protocol.roles}}\t{{showTys protocol.inputs}}\t{{showTys protocol.outputs}}\t{{protocol.inputScopes}}\t{{protocol.outputScopes}}"
{views}
end Printed
'''


def tokens(text):
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c == '"':
            j = i + 1
            while text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c in "()[]{},":
            out.append(c)
            i += 1
        else:
            j = i
            while j < len(text) and not text[j].isspace() and text[j] not in "()[]{},\"":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(items, i=0):
    out = []
    while i < len(items) and items[i] not in ")]}":
        if items[i] in "([{":
            opening = items[i]
            inner, i = parse(items, i + 1)
            out.append((opening, inner))
            i += 1
        else:
            out.append(items[i])
            i += 1
    return out, i


def show(item):
    if isinstance(item, tuple):
        opening, inner = item
        return opening + flat(inner) + {"(": ")", "[": "]", "{": "}"}[opening]
    return item


def flat(items):
    text = ""
    for item in items:
        piece = show(item)
        if not text or text.endswith(("(", "[", "{")) or piece == ",":
            text += piece
        else:
            text += " " + piece
    return text.replace(" ,", ",")


SHORT = ["ProtocolOp.", "Region.", "Regions.", "Values.", "Var.", "Op.", "Ty.", "HelperKind.", "Primitive."]


def shorten(text):
    for long in SHORT:
        text = re.sub(r"(?<![\w.])" + re.escape(long), ".", text)

    def var(match):
        result = ".here"
        for _ in range(match.group(0).count(".there")):
            result = f"(.there {result})"
        return result
    return re.sub(r"\.here(?:\.there)+", var, text)


def chain(items, indent="  "):
    lines = []
    while True:
        if items and items[0] == "Region.letOp" and len(items) == 5 and isinstance(items[4], tuple):
            lines.append(indent + shorten(flat(items[:4])) + " <|")
            items = items[4][1]
            continue
        lines.append(indent + shorten(flat(items)))
        return "\n".join(lines)


def printed(output, name):
    start = output.index(f"def Printed.{name} :")
    body = output.index(":=\n", start) + 3
    end = output.find("\ndef Printed.", body)
    text = output[body:end if end != -1 else len(output)]
    text = text.replace("Zkc.Source.Structured.", "").replace("Zkc.Source.", "")
    items, _ = parse(tokens(text))
    return chain(items)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--data", required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--closed", action="store_true")
    parser.add_argument("--name", action="append", default=[], help="DIGEST=localName")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    names = dict(item.split("=", 1) for item in args.name)
    # First pass: inventory only, to know how many bodies to materialize.
    inventory = PRINTER.format(data=args.data, views="")
    (ROOT / "build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=ROOT / "build") as scratch:
        path = Path(scratch) / "Inventory.lean"
        path.write_text(inventory, encoding="utf-8")
        output = subprocess.run(["lake", "env", "lean", str(path)], cwd=LEAN, capture_output=True,
                                text=True, check=True).stdout
        helpers = [line.split("\t")[1:] for line in output.splitlines() if line.startswith("HELPER\t")]
        protocols = [line.split("\t")[1:] for line in output.splitlines() if line.startswith("PROTOCOL\t")]
        views = []
        for index in range(len(helpers)):
            views.append(f"def helper{index} := region_view% "
                         f"(program.payload.definitions[{index}]'(by decide)).body")
        for index in range(len(protocols)):
            views.append(f"def protocol{index} := region_view% "
                         f"(program.payload.protocols[{index}]'(by decide)).body")
        if args.closed:
            views.append(f"def root := region_view% "
                         f"((checkClosed {args.data}.snapshot).toOption.get (by decide +kernel)).payload.entry.body")
        views += [f"#print Printed.{view.split()[1]}" for view in list(views)]
        path = Path(scratch) / "Bodies.lean"
        path.write_text(PRINTER.format(data=args.data, views="\n".join(views)), encoding="utf-8")
        output = subprocess.run(["lake", "env", "lean", str(path)], cwd=LEAN, capture_output=True,
                                text=True, check=True).stdout
    parts = [f"module\n\npublic import Zkc.Source.Structured.ProtocolOperations\n\n@[expose] public section\n\n"
             f"/-! Literal typed bodies printed from the admitted snapshot of\n`{args.data}`. -/\n"
             f"namespace {args.namespace}\nopen Zkc.Source Zkc.Source.Structured\n"]
    for index, (name, kind, inputs, outputs) in enumerate(helpers):
        local = names.get(name, f"helper{index}")
        parts.append(f"abbrev {local}Helper : Helper :=\n  ⟨{json.dumps(name)}, {kind}, {inputs}, {outputs}⟩\n\n"
                     f"def {local}Body : Region dialect {local}Helper.inputs {local}Helper.outputs :=\n"
                     f"{printed(output, f'helper{index}')}\n")
    for index, (name, roles, inputs, outputs, input_scopes, output_scopes) in enumerate(protocols):
        local = names.get(name, f"protocol{index}")
        parts.append(f"def {local}Signature : ProtocolSignature where\n  name := {json.dumps(name)}\n"
                     f"  roles := {roles}\n  inputs := {inputs}\n  outputs := {outputs}\n"
                     f"  inputScopes := {input_scopes}\n  outputScopes := {output_scopes}\n\n"
                     f"def {local}Body : Region protocolDialect {local}Signature.inputs {local}Signature.outputs :=\n"
                     f"{printed(output, f'protocol{index}')}\n")
    if args.closed:
        entry = protocols[0]
        parts.append(f"def entryBody : Region dialect {entry[2]} {entry[3]} :=\n{printed(output, 'root')}\n")
    parts.append(f"end {args.namespace}\n")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(parts), encoding="utf-8")


if __name__ == "__main__":
    main()
