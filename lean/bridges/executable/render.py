#!/usr/bin/env python3
"""Render a native deployment's validator program as transparent Lean data.

The input is a `zkc.native-proof/0` deployment. The renderer selects, in its
exact `zkc.program/0` candidate, the participant that the program's entry map
assigns to the deployment policy's entry and validator role, and renders it
with the local functions it calls and the operation bindings they use, in
program order. Physical types are split into a logical sort and a
representation and re-encoded exactly. A transcript operation's single
parameter is decoded as an occurrence template by the construction bridge's
decoder, which re-encodes it exactly; other parameters stay text.
Instructions outside the admitted subset are kept as unsupported for the Lean
rule to refuse; a malformed record refuses the whole program. This is a tested
data boundary: no meaning is assigned here.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re


def _construction_renderer():
    """Load the construction bridge's renderer under its own module name."""
    path = Path(__file__).resolve().parents[1] / "construction/render.py"
    spec = importlib.util.spec_from_file_location("construction_render", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


construction = _construction_renderer()

PROGRAM = "zkc.program/0"
DEPLOYMENT = "zkc.native-proof/0"
TRANSCRIPT_CONTRACTS = {"transcript.native.indexed.observe.data", "transcript.native.indexed.challenge"}
text = construction.text
require = construction.require
record = construction.record
seq = construction.seq


def physical(value):
    """Return the Lean term of a physical type and its logical sort."""
    require(isinstance(value, str) and value.count("@") == 1, f"invalid physical type {value!r}")
    logical, representation = value.split("@")
    require(re.fullmatch(r"[A-Za-z0-9_.:/-]+", representation) is not None, "invalid representation")
    if logical == "bool":
        sort = ".data .boolean"
    elif re.fullmatch(r"(field|group):[A-Za-z0-9_.-]+", logical):
        kind, domain = logical.split(":")
        sort = f".data (.{kind} {text(domain)})"
    elif re.fullmatch(r"transcript:[A-Za-z0-9_.:/-]+", logical):
        sort = f".transcript {text(logical.split(':', 1)[1])}"
    else:
        raise construction.Refused(f"unsupported physical type {value!r}")
    term = f"⟨{sort}, {text(representation)}⟩"
    require(f"{logical}@{representation}" == value, "noncanonical physical type")
    return term


def names(values):
    require(isinstance(values, list) and all(isinstance(v, str) and v for v in values), "expected value names")
    return seq(values, text)


def ports(values):
    return seq(values, lambda port: (lambda pair: f"({text(pair[0])}, {physical(pair[1])})")(record(port, 2)))


def parameter(contract, value, count):
    if contract in TRANSCRIPT_CONTRACTS:
        require(count == 1, "a transcript operation carries exactly one occurrence")
        return f".template {construction.origin(value)}"
    require(isinstance(value, str), "parameters are strings")
    return f".text {text(value)}"


def step(item, bindings):
    require(isinstance(item, list) and item and isinstance(item[0], str), "local instruction")
    if item[0] == "op":
        _, site, binding, parameters, inputs, outputs = record(item, 6)
        require(binding in bindings, f"undeclared binding {binding!r}")
        contract = bindings[binding][1]
        require(isinstance(parameters, list), "parameters")
        rendered = seq(parameters, lambda value: parameter(contract, value, len(parameters)))
        return f".operation {text(site)} {text(binding)} {rendered} {names(inputs)} {names(outputs)}"
    if item[0] == "return":
        _, values = record(item, 2)
        return f".ret {names(values)}"
    return f".unsupported {text(item[0])}"


def action(item):
    require(isinstance(item, list) and item and isinstance(item[0], str), "participant instruction")
    if item[0] == "receive":
        _, site, schema, peer, output, ty = record(item, 6)
        return f".receive {text(site)} {text(schema)} {text(peer)} {text(output)} {physical(ty)}"
    if item[0] == "local":
        _, site, function, inputs, outputs = record(item, 5)
        return f".call {text(site)} {text(function)} {names(inputs)} {names(outputs)}"
    if item[0] == "return":
        _, values = record(item, 2)
        return f".ret {names(values)}"
    return f".unsupported {text(item[0])}"


def select(deployment):
    """The exact program bytes and the validator participant they select."""
    require(isinstance(deployment, list) and len(deployment) == 9 and deployment[0] == DEPLOYMENT,
            "expected a native proof deployment")
    candidate = deployment[4]
    require(isinstance(candidate, str), "candidate program")
    digest = hashlib.sha256(candidate.encode()).hexdigest()
    require(deployment[5] == digest, "candidate digest differs from the program bytes")
    policy = deployment[2][1]
    entry, validator_role = policy[1], policy[3]
    program = json.loads(candidate)
    tag, bindings, functions, participants, entries = record(program, 5)
    require(tag == PROGRAM, "expected zkc.program/0")
    roles = [roles for kind, name, roles in (record(e, 3) for e in entries) if kind == "entry" and name == entry]
    require(len(roles) == 1, "the deployment entry must be unique in the program")
    symbols = [symbol for role, symbol in (record(r, 2) for r in roles[0]) if role == validator_role]
    require(len(symbols) == 1, "the validator role must be unique in the entry")
    selected = [p for p in participants if record(p, 8)[1] == symbols[0]]
    require(len(selected) == 1, "the validator participant must be unique")
    return digest, entry, validator_role, selected[0], functions, bindings


def render(deployment, namespace):
    require(re.fullmatch(r"(?:[A-Za-z][A-Za-z0-9_]*\.)*[A-Za-z][A-Za-z0-9_]*", namespace) is not None,
            "invalid Lean namespace")
    digest, entry, role, participant, functions, bindings = select(deployment)
    _, symbol, instance, actual_role, inputs, results, body, services = record(participant, 8)
    require(actual_role == role and instance == entry, "participant role and instance")
    require(services == [], "the validator participant has no services")
    require(isinstance(body, list), "participant body")
    declared = {}
    for binding in bindings:
        name, contract, arguments, implementation = record(binding, 4)
        require(isinstance(name, str) and name not in declared, "duplicate binding")
        require(isinstance(contract, str) and isinstance(implementation, str)
                and isinstance(arguments, list) and all(isinstance(a, str) for a in arguments), "binding shape")
        declared[name] = (name, contract, arguments, implementation)
    called = {item[2] for item in body if isinstance(item, list) and item[:1] == ["local"] and len(item) == 5}
    selected_functions, used = [], set()
    for function in functions:
        kind, name, arguments, outputs, steps, _origin = record(function, 6)
        require(kind == "function" and isinstance(steps, list), "function shape")
        if name not in called:
            continue
        rendered_steps = [step(item, declared) for item in steps]
        used |= {item[2] for item in steps if isinstance(item, list) and item[:1] == ["op"] and len(item) == 6}
        selected_functions.append(f"⟨{text(name)}, {ports(arguments)}, {seq(outputs, physical)}, [\n"
                                  + ",\n".join(f"      {s}" for s in rendered_steps) + "]⟩")
    rendered_bindings = [f"⟨{text(name)}, {text(contract)}, {seq(arguments, text)}, {text(implementation)}⟩"
                         for name, contract, arguments, implementation in declared.values() if name in used]
    actions = ",\n    ".join(action(item) for item in body)
    function_text = ",\n    ".join(selected_functions)
    binding_text = ",\n    ".join(rendered_bindings)
    return f'''module

public import Zkc.Executable.Program

@[expose] public section

/-! Validator data from the retained `zkc.program/0` candidate of the native
deployment. Regenerate with bridges/executable/check.py --write; the Lean rule
and its proofs are separate. The bridge checks exact regeneration against the
compiler. -/

namespace {namespace}
open Zkc.Construction Zkc.Executable

/-- SHA-256 of the exact `zkc.program/0` bytes this data was read from. -/
def program : String := {text("sha256:" + digest)}

def validator : Validator where
  entry := {text(entry)}
  role := {text(role)}
  symbol := {text(symbol)}
  inputs := {ports(inputs)}
  results := {seq(results, physical)}
  body := [
    {actions}]
  functions := [
    {function_text}]
  bindings := [
    {binding_text}]

end {namespace}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="native proof deployment")
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", required=True)
    args = parser.parse_args()
    deployment = json.loads(args.input.read_text(encoding="utf-8"))
    args.output.write_text(render(deployment, args.namespace), encoding="utf-8")


if __name__ == "__main__":
    main()
