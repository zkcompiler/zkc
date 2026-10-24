#!/usr/bin/env python3
"""Render a native deployment's validator program as transparent Lean data.

The input is a `zkc.native-proof/0` deployment. The renderer selects, in its
exact `zkc.program/0` candidate, the participant that the program's entry map
assigns to the deployment policy's entry and validator role, and renders it
with the local functions it calls, including from loop bodies, and the
operation bindings they use, in program order. Participant loops and their
yields, and local conditionals, counted iterations, Boolean literals, stops and
yields are rendered with their nested bodies. Physical types are split into a
logical sort and a representation and re-encoded exactly. A transcript
operation's single parameter is decoded as an occurrence template by the
construction bridge's decoder, which re-encodes it exactly; other parameters
stay text. Instructions outside the admitted subset are kept as unsupported for
the Lean rule to refuse; a malformed record refuses the whole program. This is
a tested data boundary: no meaning is assigned here.
"""

import json
from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render  # noqa: E402
from bridges.common.lean_render import Refused, origin, record, require, seq, text  # noqa: E402

PROGRAM = "zkc.program/0"
DEPLOYMENT = "zkc.native-proof/0"
TRANSCRIPT_CONTRACTS = {"transcript.native.indexed.observe.data", "transcript.native.indexed.challenge"}


def physical(value):
    """Return the Lean term of a physical type and its logical sort."""
    require(isinstance(value, str) and value.count("@") == 1, f"invalid physical type {value!r}")
    logical, representation = value.split("@")
    require(re.fullmatch(r"[A-Za-z0-9_.:/-]+", representation) is not None, "invalid representation")
    if logical == "bool":
        sort = ".data .boolean"
    elif logical == "index":
        sort = ".data .index"
    elif re.fullmatch(r"(field|group|vector):[A-Za-z0-9_.-]+", logical):
        kind, domain = logical.split(":")
        sort = f".data (.{kind} {text(domain)})"
    elif re.fullmatch(r"transcript:[A-Za-z0-9_.:/-]+", logical):
        sort = f".transcript {text(logical.split(':', 1)[1])}"
    else:
        raise Refused(f"unsupported physical type {value!r}")
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
        return f".template {origin(value)}"
    require(isinstance(value, str), "parameters are strings")
    return f".text {text(value)}"


def pairs(values):
    """Carried values: `[name, initial]` pairs."""
    return seq(values, lambda pair: (lambda p: f"({text(p[0])}, {text(p[1])})")(record(pair, 2)))


def region(items, bindings):
    require(isinstance(items, list), "local region")
    return "[" + ", ".join(step(item, bindings) for item in items) + "]"


def step(item, bindings):
    require(isinstance(item, list) and item and isinstance(item[0], str), "local instruction")
    if item[0] == "op":
        _, site, binding, parameters, inputs, outputs = record(item, 6)
        require(binding in bindings, f"undeclared binding {binding!r}")
        contract = bindings[binding][1]
        require(isinstance(parameters, list), "parameters")
        rendered = seq(parameters, lambda value: parameter(contract, value, len(parameters)))
        return f".operation {text(site)} {text(binding)} {rendered} {names(inputs)} {names(outputs)}"
    if item[0] == "bool_constant":
        _, site, output, value = record(item, 4)
        require(isinstance(value, bool), "Boolean literal")
        return f".constant {text(site)} {text(output)} {'true' if value else 'false'}"
    if item[0] == "if":
        _, site, condition, captures, yes, no, outputs = record(item, 7)
        return (f".cond {text(site)} {text(condition)} {names(captures)} {region(yes, bindings)} "
                f"{region(no, bindings)} {names(outputs)}")
    if item[0] == "for":
        _, site, induction, lower, upper, carried, captures, body, outputs = record(item, 9)
        return (f".iterate {text(site)} {text(induction)} {text(lower)} {text(upper)} {pairs(carried)} "
                f"{names(captures)} {region(body, bindings)} {names(outputs)}")
    if item[0] == "stop":
        _, site, reason = record(item, 3)
        return f".stop {text(site)} {text(reason)}"
    if item[0] == "yield":
        _, values = record(item, 2)
        return f".yield {names(values)}"
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
    if item[0] == "loop":
        _, site, count, carried, captures, body, outputs = record(item, 7)
        kind, value, maximum, induction = record(count, 4)
        require(kind == "value", "loop count")
        require(isinstance(maximum, str) and re.fullmatch(r"0|[1-9][0-9]*", maximum) is not None
                and int(maximum) <= 1048576, "loop maximum")
        require(isinstance(body, list), "loop body")
        return (f".loop {text(site)} {text(value)} {int(maximum)} {text(induction)} {pairs(carried)} "
                f"{names(captures)} [" + ", ".join(action(inner) for inner in body) + f"] {names(outputs)}")
    if item[0] == "yield":
        _, values = record(item, 2)
        return f".yield {names(values)}"
    if item[0] == "return":
        _, values = record(item, 2)
        return f".ret {names(values)}"
    return f".unsupported {text(item[0])}"


def called(body):
    """The local functions a participant body calls, including from loop bodies."""
    found = set()
    for item in body:
        if isinstance(item, list) and item[:1] == ["local"] and len(item) == 5:
            found.add(item[2])
        if isinstance(item, list) and item[:1] == ["loop"] and len(item) == 7 and isinstance(item[5], list):
            found |= called(item[5])
    return found


def used_bindings(steps):
    """The operation bindings a local body uses, including inside its regions."""
    found = set()
    for item in steps:
        if not isinstance(item, list) or not item:
            continue
        if item[0] == "op" and len(item) == 6:
            found.add(item[2])
        elif item[0] == "if" and len(item) == 7:
            for nested in (item[4], item[5]):
                if isinstance(nested, list):
                    found |= used_bindings(nested)
        elif item[0] == "for" and len(item) == 9 and isinstance(item[7], list):
            found |= used_bindings(item[7])
    return found


def select(deployment):
    """The exact program bytes and the validator participant they select."""
    require(isinstance(deployment, list) and len(deployment) == 9 and deployment[0] == DEPLOYMENT,
            "expected a native proof deployment")
    candidate = deployment[4]
    require(isinstance(candidate, str), "candidate program")
    digest = lean_render.digest(candidate.encode())
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
    lean_render.namespace(namespace)
    digest, entry, role, participant, functions, bindings = select(deployment)
    _, symbol, instance, actual_role, inputs, results, body, services = record(participant, 8)
    require(actual_role == role and instance == entry, "participant role and instance")
    require(services == [], "the validator participant has no services")
    require(isinstance(body, list), "participant body")
    declared = {}
    for binding in bindings:
        name, contract, arguments, implementation, physical_arguments = record(binding, 5)
        require(isinstance(name, str) and name not in declared, "duplicate binding")
        require(isinstance(contract, str) and isinstance(implementation, str)
                and isinstance(arguments, list) and all(isinstance(a, str) for a in arguments), "binding shape")
        require(physical_arguments == [], "physical binding specialization is outside the executable bridge")
        declared[name] = (name, contract, arguments, implementation)
    reached = called(body)
    selected_functions, used = [], set()
    for function in functions:
        kind, name, arguments, outputs, steps, _origin = record(function, 6)
        require(kind == "function" and isinstance(steps, list), "function shape")
        if name not in reached:
            continue
        rendered_steps = [step(item, declared) for item in steps]
        used |= used_bindings(steps)
        selected_functions.append((name, f"⟨{text(name)}, {ports(arguments)}, {seq(outputs, physical)}, [\n"
                                  + ",\n".join(f"    {s}" for s in rendered_steps) + "]⟩"))
    rendered_bindings = [f"⟨{text(name)}, {text(contract)}, {seq(arguments, text)}, {text(implementation)}⟩"
                         for name, contract, arguments, implementation in declared.values() if name in used]
    actions = ",\n    ".join(action(item) for item in body)
    function_definitions = "".join(
        f"/-- The local function `{name}`. -/\ndef function{index} : Function :=\n  {literal}\n\n"
        for index, (name, literal) in enumerate(selected_functions))
    function_text = ", ".join(f"function{index}" for index in range(len(selected_functions)))
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

{function_definitions}def validator : Validator where
  entry := {text(entry)}
  role := {text(role)}
  symbol := {text(symbol)}
  inputs := {ports(inputs)}
  results := {seq(results, physical)}
  body := [
    {actions}]
  functions := [{function_text}]
  bindings := [
    {binding_text}]

end {namespace}
'''


if __name__ == "__main__":
    lean_render.render_main(render, __doc__)
