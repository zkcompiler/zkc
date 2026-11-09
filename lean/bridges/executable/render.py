#!/usr/bin/env python3
"""Render a native deployment's validator program as transparent Lean data.

The input is a `zkc.native-proof/0` deployment. The renderer selects, in its
exact `zkc.program/0` candidate, the participant that the program's entry map
assigns to the deployment policy's entry and validator role, and renders it
with the local functions it calls, including from loop bodies and from every
arm of a participant conditional or match, and the operation bindings they use,
in program order. `render_program` renders a whole program, every declaration
included, for the structural admission of `Zkc.Executable.ProgramAdmission`.

Participant loops, conditionals and matches, with their capture rows and
nested bodies, and local conditionals, counted iterations, Boolean literals,
stops and yields are rendered. Capture fields are decoded by body kind:
participant control carries `[formal, parent]` rows and local control carries
names, so a participant name list and a local row list both refuse. Physical
types are split into a logical sort and a representation and re-encoded
exactly. A transcript operation's single parameter is decoded as an occurrence
template by the construction bridge's decoder, which re-encodes it exactly;
other parameters stay text. Instructions outside the admitted subset are kept
as unsupported for the Lean rule to refuse; a malformed record refuses the
whole program. This is a tested data boundary: no meaning is assigned here.
"""

import json
from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render, policy as native_policy, schema  # noqa: E402
from bridges.common.lean_render import Refused, origin, record, require, seq, text  # noqa: E402

PROGRAM = "zkc.program/0"
DEPLOYMENT = "zkc.native-proof/0"
# The program carrier's ceilings (docs/spec/formats/program.md, "Carrier size"):
# an entry of an operation's parameter array, and every other decoded string.
PARAMETER_BYTES = 16384
STRING_BYTES = 4096
# The carrier's bound on the attributes of one operation (program-bytes.md,
# "Bounds and admission").
OPERATION_ATTRIBUTES = 16384
TRANSCRIPT_CONTRACTS = {"transcript.native.indexed.observe.data", "transcript.native.indexed.challenge"}


def string(value):
    """The Lean literal of a carrier string other than an operation parameter."""
    return text(value, STRING_BYTES)


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
        sort = f".data (.{kind} {string(domain)})"
    elif re.fullmatch(r"transcript:[A-Za-z0-9_.:/-]+", logical):
        sort = f".transcript {string(logical.split(':', 1)[1])}"
    elif re.fullmatch(r"resource_unit:[A-Za-z][A-Za-z0-9_.-]*", logical):
        # A custody permission of one exact slot; admission belongs to Lean.
        slot = logical.split(":", 1)[1]
        sort = f".data (.resourceUnit {string(schema.domain_identity(slot, slot=True))})"
    else:
        raise Refused(f"unsupported physical type {value!r}")
    term = f"⟨{sort}, {string(representation)}⟩"
    require(f"{logical}@{representation}" == value, "noncanonical physical type")
    return term


def names(values):
    require(isinstance(values, list) and all(isinstance(v, str) and v for v in values), "expected value names")
    return seq(values, string)


def captures(values):
    """Participant capture rows: `[formal, parent]` pairs of value names."""
    require(isinstance(values, list), "expected capture rows")

    def row(value):
        require(isinstance(value, list), "expected capture rows")
        formal, parent = record(value, 2)
        require(isinstance(formal, str) and formal and isinstance(parent, str) and parent,
                "expected capture rows")
        return f"⟨{string(formal)}, {string(parent)}⟩"
    return seq(values, row)


def ports(values):
    return seq(values, lambda port: (lambda pair: f"({string(pair[0])}, {physical(pair[1])})")(record(port, 2)))


def parameter(contract, value, count):
    if contract in TRANSCRIPT_CONTRACTS:
        require(count == 1, "a transcript operation carries exactly one occurrence")
        return f".template {origin(value)}"
    require(isinstance(value, str), "parameters are strings")
    return f".text {text(value, PARAMETER_BYTES)}"


def pairs(values):
    """Carried values: `[name, initial]` pairs."""
    return seq(values, lambda pair: (lambda p: f"({string(p[0])}, {string(p[1])})")(record(pair, 2)))


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
        rendered = seq(parameters, lambda value: parameter(contract, value, len(parameters)),
                       OPERATION_ATTRIBUTES)
        return f".operation {string(site)} {string(binding)} {rendered} {names(inputs)} {names(outputs)}"
    if item[0] == "bool_constant":
        _, site, output, value = record(item, 4)
        require(isinstance(value, bool), "Boolean literal")
        return f".constant {string(site)} {string(output)} {'true' if value else 'false'}"
    if item[0] == "if":
        _, site, condition, captures, yes, no, outputs = record(item, 7)
        return (f".cond {string(site)} {string(condition)} {names(captures)} {region(yes, bindings)} "
                f"{region(no, bindings)} {names(outputs)}")
    if item[0] == "for":
        _, site, induction, lower, upper, carried, captures, body, outputs = record(item, 9)
        return (f".iterate {string(site)} {string(induction)} {string(lower)} {string(upper)} {pairs(carried)} "
                f"{names(captures)} {region(body, bindings)} {names(outputs)}")
    if item[0] == "stop":
        _, site, reason = record(item, 3)
        return f".stop {string(site)} {string(reason)}"
    if item[0] == "yield":
        _, values = record(item, 2)
        return f".yield {names(values)}"
    if item[0] == "return":
        _, values = record(item, 2)
        return f".ret {names(values)}"
    return f".unsupported {string(item[0])}"


def participant_body(items):
    require(isinstance(items, list), "participant body")
    return "[" + ", ".join(action(item) for item in items) + "]"


def arm(value):
    """A participant match arm: `[alternative, payload bindings, body]`."""
    alternative, payload, body = record(value, 3)
    require(isinstance(alternative, str), "match alternative")
    return f"({string(alternative)}, {names(payload)}, {participant_body(body)})"


def action(item):
    require(isinstance(item, list) and item and isinstance(item[0], str), "participant instruction")
    if item[0] == "receive":
        _, site, schema, peer, output, ty = record(item, 6)
        return f".receive {string(site)} {string(schema)} {string(peer)} {string(output)} {physical(ty)}"
    if item[0] == "local":
        _, site, function, inputs, outputs = record(item, 5)
        return f".call {string(site)} {string(function)} {names(inputs)} {names(outputs)}"
    if item[0] == "loop":
        _, site, count, carried, rows, body, outputs = record(item, 7)
        kind, value, maximum, induction = record(count, 4)
        require(kind == "value", "loop count")
        require(isinstance(maximum, str) and re.fullmatch(r"0|[1-9][0-9]*", maximum) is not None
                and int(maximum) <= 1048576, "loop maximum")
        return (f".loop {string(site)} {string(value)} {int(maximum)} {string(induction)} {pairs(carried)} "
                f"{captures(rows)} {participant_body(body)} {names(outputs)}")
    if item[0] == "if":
        _, site, condition, rows, yes, no, outputs = record(item, 7)
        return (f".cond {string(site)} {string(condition)} {captures(rows)} {participant_body(yes)} "
                f"{participant_body(no)} {names(outputs)}")
    if item[0] == "match":
        _, site, selector, rows, arms, outputs = record(item, 6)
        require(isinstance(arms, list), "match arms")
        return (f".select {string(site)} {string(selector)} {captures(rows)} "
                f"[{', '.join(arm(value) for value in arms)}] {names(outputs)}")
    if item[0] == "yield":
        _, values = record(item, 2)
        return f".yield {names(values)}"
    if item[0] == "return":
        _, values = record(item, 2)
        return f".ret {names(values)}"
    return f".unsupported {string(item[0])}"


def nested_bodies(item):
    """The nested bodies of a participant instruction, in order: a loop body,
    both arms of a conditional, or every arm of a match."""
    if not isinstance(item, list) or not item:
        return []
    if item[0] == "loop" and len(item) == 7:
        return [item[5]]
    if item[0] == "if" and len(item) == 7:
        return [item[4], item[5]]
    if item[0] == "match" and len(item) == 6 and isinstance(item[4], list):
        return [value[2] for value in item[4] if isinstance(value, list) and len(value) == 3]
    return []


def called(body):
    """The local functions a participant body calls, including from loop bodies
    and from every arm of a conditional or match."""
    found = set()
    for item in body:
        if isinstance(item, list) and item[:1] == ["local"] and len(item) == 5:
            found.add(item[2])
        for nested in nested_bodies(item):
            if isinstance(nested, list):
                found |= called(nested)
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


# The byte language's element bound for one array (program-bytes.md, "Bounds and
# admission"). A whole program read here was already admitted by a decoder that
# enforces every bound of that table; the renderer only refuses to exceed it.
ARRAY_ELEMENTS = 32768


def origin_record(value):
    """A function origin: `[logical_definition, [[parameter, argument]...]]`."""
    definition, assignments = record(value, 2)
    require(isinstance(definition, str) and isinstance(assignments, list), "function origin")
    for assignment in assignments:
        parameter_name, argument = record(assignment, 2)
        require(isinstance(parameter_name, str) and isinstance(argument, str), "function origin")


def service(value):
    """A participant service port: `[name, contract, input_index]`."""
    name, contract, index = record(value, 3)
    require(isinstance(contract, str) and isinstance(index, str)
            and re.fullmatch(r"0|[1-9][0-9]*", index) is not None and len(index) <= 20, "service port")
    return f"⟨{string(name)}, {string(contract)}, {int(index)}⟩"


def render_program(program, namespace):
    """A whole `zkc.program/0` value as `ProgramArtifact` data.

    Every binding, function, participant and entry is rendered in program
    order, used or not, with the record decoding of `render`. Admission belongs
    to `Zkc.Executable.ProgramAdmission`: duplicate or unresolved names are
    kept for it to refuse.
    """
    lean_render.namespace(namespace)
    tag, bindings, functions, participants, entries = record(program, 5)
    require(tag == PROGRAM, "expected zkc.program/0")
    for value in (bindings, functions, participants, entries):
        require(isinstance(value, list) and len(value) <= ARRAY_ELEMENTS, "program declarations")
    declared = {}
    rendered_bindings = []
    for binding in bindings:
        name, contract, arguments, implementation, physical_arguments = record(binding, 5)
        require(isinstance(name, str) and isinstance(contract, str) and isinstance(implementation, str)
                and isinstance(arguments, list) and all(isinstance(a, str) for a in arguments)
                and isinstance(physical_arguments, list), "binding shape")
        declared.setdefault(name, (name, contract, arguments, implementation, physical_arguments))
        rendered_bindings.append(f"⟨{string(name)}, {string(contract)}, {seq(arguments, string)}, "
                                 f"{string(implementation)}, {seq(physical_arguments, physical)}⟩")
    rendered_functions = []
    for function in functions:
        kind, name, arguments, outputs, steps, origin_value = record(function, 6)
        require(kind == "function" and isinstance(steps, list) and len(steps) <= ARRAY_ELEMENTS, "function shape")
        origin_record(origin_value)
        rendered_functions.append(
            f"⟨{string(name)}, {ports(arguments)}, {seq(outputs, physical)}, "
            f"{seq(steps, lambda item: step(item, declared), ARRAY_ELEMENTS)}⟩")
    rendered_participants = []
    for participant in participants:
        kind, name, instance, role, inputs, results, body, services = record(participant, 8)
        require(kind == "participant" and isinstance(body, list) and len(body) <= ARRAY_ELEMENTS,
                "participant shape")
        rendered_participants.append(
            f"⟨{string(name)}, {string(instance)}, {string(role)}, {ports(inputs)}, {seq(results, physical)}, "
            f"{seq(body, action, ARRAY_ELEMENTS)}, {seq(services, service)}⟩")
    rendered_entries = []
    for entry in entries:
        kind, name, roles = record(entry, 3)
        require(kind == "entry", "entry shape")
        rendered_entries.append(f"⟨{string(name)}, {seq(roles, lambda pair: pair_text(record(pair, 2)))}⟩")
    return (f"⟨{seq(rendered_bindings, str, ARRAY_ELEMENTS)}, {seq(rendered_functions, str, ARRAY_ELEMENTS)}, "
            f"{seq(rendered_participants, str, ARRAY_ELEMENTS)}, {seq(rendered_entries, str, ARRAY_ELEMENTS)}⟩")


def pair_text(pair):
    first, second = pair
    return f"({string(first)}, {string(second)})"


def select(deployment):
    """The exact program bytes and the validator participant they select."""
    require(isinstance(deployment, list) and len(deployment) == 9 and deployment[0] == DEPLOYMENT,
            "expected a native proof deployment")
    candidate = deployment[4]
    require(isinstance(candidate, str), "candidate program")
    digest = lean_render.digest(candidate.encode())
    require(deployment[5] == digest, "candidate digest differs from the program bytes")
    policy = native_policy.decode(deployment[2][1])
    require(not policy.gates, "unsupported policy gates")
    require(policy.profile in (native_policy.AUTHORED, native_policy.NATIVE), "unsupported construction profile")
    entry, validator_role = policy.entry, policy.validator
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
        require(isinstance(physical_arguments, list), "physical binding arguments")
        # Keep specialization in the carrier; the Lean vocabulary decides
        # which exact implementation and physical arguments have a meaning.
        for argument in physical_arguments:
            physical(argument)
        declared[name] = (name, contract, arguments, implementation, physical_arguments)
    reached = called(body)
    selected_functions, used = [], set()
    for function in functions:
        kind, name, arguments, outputs, steps, _origin = record(function, 6)
        require(kind == "function" and isinstance(steps, list), "function shape")
        if name not in reached:
            continue
        rendered_steps = [step(item, declared) for item in steps]
        used |= used_bindings(steps)
        selected_functions.append((name, f"⟨{string(name)}, {ports(arguments)}, {seq(outputs, physical)}, [\n"
                                  + ",\n".join(f"    {s}" for s in rendered_steps) + "]⟩"))
    rendered_bindings = [f"⟨{string(name)}, {string(contract)}, {seq(arguments, string)}, {string(implementation)}, "
                         f"{seq(physical_arguments, physical)}⟩"
                         for name, contract, arguments, implementation, physical_arguments in declared.values()
                         if name in used]
    actions = ",\n    ".join(action(item) for item in body)
    function_definitions = "".join(
        f"/-- The local function `{name}`. -/\ndef function{index} : Function :=\n  {literal}\n\n"
        for index, (name, literal) in enumerate(selected_functions))
    function_text = ", ".join(f"function{index}" for index in range(len(selected_functions)))
    binding_text = ",\n    ".join(rendered_bindings)
    return f'''module

public import Zkc.IR.Executable.Program

@[expose] public section

/-! Validator data from the retained `zkc.program/0` candidate of the native
deployment. Regenerate with bridges/executable/check.py --write; the Lean rule
and its proofs are separate. The bridge checks exact regeneration against the
compiler. -/

namespace {namespace}
open Zkc.Construction Zkc.Executable

/-- SHA-256 of the exact `zkc.program/0` bytes this data was read from. -/
def program : String := {string("sha256:" + digest)}

{function_definitions}def validator : Validator where
  entry := {string(entry)}
  role := {string(role)}
  symbol := {string(symbol)}
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
