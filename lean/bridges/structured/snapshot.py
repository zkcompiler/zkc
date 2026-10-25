#!/usr/bin/env python3
"""Render a retained structured export as transparent Lean constructor data.

This is a tested data boundary. It generates no proof and never interprets a
helper name as a mathematical specification.
"""

from functools import partial
import re
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render  # noqa: E402
from bridges.common.lean_render import optional, record  # noqa: E402

# The structured source profile bounds strings at 512 bytes and references at 4096.
text = partial(lean_render.text, limit=512)
nat = lean_render.nat
seq = lean_render.seq
ty = lean_render.ty


def descriptor(value):
    if not isinstance(value, list) or not value:
        raise ValueError("invalid descriptor")
    tag, *args = value
    unary, nullary = lean_render.UNARY_OPERATIONS, lean_render.NULLARY_OPERATIONS
    if tag in unary:
        record(args, 1)
        return f".{unary[tag]} {text(args[0])}"
    if tag in nullary:
        record(args, 0)
        return "." + nullary[tag]
    if tag == "index.constant":
        record(args, 1)
        return f".indexConstant {text(args[0])}"
    if tag == "field.embed":
        extension, base = record(args, 2)
        return f".fieldEmbed {text(extension)} {text(base)}"
    if tag == "exec":
        operation, binding_name, parameters = record(args, 3)
        return f".exec {text(operation)} {text(binding_name)} {seq(parameters, text)}"
    if tag == "bool.constant":
        record(args, 1)
        if type(args[0]) is not bool:
            raise ValueError("invalid Boolean")
        return ".booleanConstant " + str(args[0]).lower()
    if tag == "select":
        record(args, 1)
        return f".select ({ty(args[0])})"
    if tag == "protocol_repeat":
        carried, maximum, roles, scopes = record(args, 4)
        return (f".protocolRepeat {nat(carried, 512)} {nat(maximum, 1048576)} "
                f"{seq(roles, text)} {seq(scopes, lambda scope: seq(scope, text))}")
    if tag == "protocol_apply":
        callee, roles = record(args, 2)
        return f".protocolApply {text(callee)} {seq(roles, text)}"
    if tag == "restrict":
        record(args, 1)
        return f".restrict {seq(args[0], text)}"
    if tag == "statement":
        relation_name, selectors, acceptance, target = record(args, 4)
        return (f".statement {text(relation_name)} {seq(selectors, text)} "
                f"{nat(acceptance)} ({optional(target, text)})")
    if tag in lean_render.BINARY_OPERATIONS or tag == "fold":
        record(args, 3 if tag == "fold" else 2)
        name = lean_render.BINARY_OPERATIONS.get(tag, "fold")
        return "." + name + " " + " ".join(text(arg) for arg in args)
    raise ValueError(f"unknown descriptor: {tag}")


def terminator(value):
    if not isinstance(value, list) or not value:
        raise ValueError("invalid terminator")
    if value[0] in ("return", "yield", "condition"):
        _, refs = record(value, 2)
        name = "ret" if value[0] == "return" else value[0]
        return f".{name} {seq(refs)}"
    tag, reason, site = record(value, 3)
    if tag != "stop" or reason not in ("reject", "abort", "exhausted", "incomplete", "refused"):
        raise ValueError("invalid stop")
    return f".stop .{reason} {text(site)}"


def block(value):
    tag, instructions, terminal = record(value, 3)
    if tag != "block":
        raise ValueError("invalid block")
    return f".block {seq(instructions, instruction)} ({terminator(terminal)})"


def region(value):
    inputs, outputs, body = record(value, 3)
    return f".region {seq(inputs, ty)} {seq(outputs, ty)} ({block(body)})"


def instruction(value):
    op, operands, results, regions, site = record(value, 5)
    return (f".instruction ({descriptor(op)}) {seq(operands)} {seq(results, ty)} "
            f"{seq(regions, region)} {text(site)}")


def bound(value):
    tag, index, container, axis = record(value, 4)
    if tag != "index_bound":
        raise ValueError("invalid precondition")
    return "⟨" + ", ".join(map(nat, (index, container, axis))) + "⟩"


def domain(value):
    tag, name, inputs, constructor = record(value, 4)
    if tag != "domain":
        raise ValueError("invalid domain")
    if constructor[0] == "elements":
        _, index = record(constructor, 2)
        operation = ".elements " + nat(index)
    elif constructor[0] == "indices":
        _, index, axis = record(constructor, 3)
        operation = f".indices {nat(index)} {nat(axis)}"
    else:
        raise ValueError("unsupported domain constructor")
    return f"⟨{text(name)}, {seq(inputs, ty)}, {operation}⟩"


def protocol_interface(value):
    if value == []:
        return "none"
    tag, roles, inputs, outputs = record(value, 4)
    if tag != "protocol":
        raise ValueError("invalid protocol interface")
    return f"some ⟨{seq(roles, text)}, {seq(inputs, lambda x: seq(x, text))}, {seq(outputs, lambda x: seq(x, text))}⟩"


def relation(value):
    tag, name, visibility, kind, key, revision, inputs, outputs, purposes, formula = record(value, 10)
    if tag != "relation" or visibility not in ("public", "private"):
        raise ValueError("invalid relation")
    return (f"⟨{text(name)}, .{visibility}Def, {text(kind)}, {text(key)}, {text(revision)}, "
            f"{seq(inputs, ty)}, {seq(outputs, ty)}, {seq(purposes, text)}, "
            f"{optional(formula, text)}⟩")


def contract_selector(value):
    direction, port, role = record(value, 3)
    if direction not in ("input", "output"):
        raise ValueError("invalid contract selector direction")
    return f"⟨.{direction}, {nat(port)}, {text(role)}⟩"


def relation_application(value):
    name, selectors = record(value, 2)
    return f"⟨{text(name)}, {seq(selectors, contract_selector)}⟩"


def contract_clause(value):
    kind, name, subject, residual, decision = record(value, 5)
    if kind not in ("target", "input", "output", "continuation"):
        raise ValueError("invalid contract clause kind")
    return (f"⟨.{kind}, {text(name)}, {relation_application(subject)}, "
            f"{optional(residual, relation_application)}, "
            f"{optional(decision, contract_selector)}⟩")


def protocol_contract(value):
    owner, clauses = record(value, 2)
    return f"⟨{text(owner)}, {seq(clauses, contract_clause)}⟩"


def primitive_binding(value):
    tag, name, contract, arguments, implementation = record(value, 5)
    if tag != "binding":
        raise ValueError("invalid binding")
    return (f"⟨{text(name)}, {text(contract)}, {seq(arguments, text)}, "
            f"{text(implementation)}⟩")


def definition(value):
    if value[0] == "realize":
        _, name, inputs, outputs, helper = record(value, 5)
        return (f".realization ⟨{text(name)}, {seq(inputs, ty)}, {seq(outputs, ty)}, "
                f"{text(helper)}⟩")
    if value[0] == "map":
        _, name, inputs, outputs, helper, rowwise = record(value, 6)
        def boolean(value):
            if type(value) is not bool:
                raise ValueError("invalid map row mask Boolean")
            return str(value).lower()
        return (f".map ⟨{text(name)}, {seq(inputs, ty)}, {seq(outputs, ty)}, "
                f"{text(helper)}, {seq(rowwise, boolean)}⟩")
    if value[0] == "finite":
        _, name, visibility, inputs, outputs, domain_name, step, predicate = record(value, 8)
        if visibility not in ("public", "private"):
            raise ValueError("invalid visibility")
        return (f".finite ⟨{text(name)}, .{visibility}Def, {seq(inputs, ty)}, {seq(outputs, ty)}, "
                f"{text(domain_name)}, {text(step)}, {text(predicate)}⟩")
    tag, name, kind, visibility, inputs, outputs, interface, premises, origin, body = record(value, 10)
    if tag != "function" or kind not in ("protocol", "math", "local") or visibility not in ("public", "private"):
        raise ValueError("invalid function header")
    if origin == []:
        origin_text = "none"
    else:
        origin_name, bindings = record(origin, 2)
        def binding(pair):
            key, value = record(pair, 2)
            return f"({text(key)}, {text(value)})"
        origin_text = f"some ({text(origin_name)}, {seq(bindings, binding)})"
    return (f".function ⟨{text(name)}, .{kind}, .{visibility}Def, {seq(inputs, ty)}, "
            f"{seq(outputs, ty)}, {protocol_interface(interface)}, {seq(premises, bound)}, {origin_text}, ({block(body)})⟩")


SORTS = {"Field": ".field", "Group": ".group", "Commitment": ".commitment",
         "Transcript": ".transcript"}


def modulus(value):
    if value is None:
        return "none"
    if not isinstance(value, str) or not re.fullmatch(r"[1-9][0-9]{0,1023}", value):
        raise ValueError("invalid catalogue modulus")
    return f"(some {value})"


def nominal(value):
    tag, identity, sort, members, capabilities, characteristic = record(value, 6)
    if tag != "nominal" or sort not in SORTS:
        raise ValueError("invalid nominal catalogue row")
    def member(pair):
        name, target = record(pair, 2)
        return f"({text(name)}, {text(target)})"
    return (f"⟨{text(identity)}, {SORTS[sort]}, {seq(members, member)}, "
            f"{seq(capabilities, text)}, {modulus(characteristic)}⟩")


def service_row(value):
    tag, contract, sampled, methods = record(value, 4)
    if tag != "service":
        raise ValueError("invalid service catalogue row")
    return f"⟨{text(contract)}, {text(sampled)}, {seq(methods, text)}⟩"


def catalogue(value):
    nominals, services = record(value, 2)
    return f"{{ nominals := {seq(nominals, nominal)}, services := {seq(services, service_row)} }}"


def render(data, namespace):
    version, stage, source, entry, domains, relations, bindings, definitions, contracts, rows = record(data, 10)
    if version != "zkc.structured-source/0" or stage != "original":
        raise ValueError("wrong version or stage")
    lean_render.namespace(namespace)
    return f'''module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace {namespace}
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := {text(source)}
  entry := {text(entry)}
  domains := {seq(domains, domain)}
  relations := {seq(relations, relation)}
  bindings := {seq(bindings, primitive_binding)}
  definitions := {seq(definitions, definition)}
  contracts := {seq(contracts, protocol_contract)}
  catalogue := {catalogue(rows)}

end {namespace}
'''


if __name__ == "__main__":
    lean_render.render_main(render, __doc__)
