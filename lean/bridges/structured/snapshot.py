#!/usr/bin/env python3
"""Render a retained structured export as transparent Lean constructor data.

This is a tested data boundary. It generates no proof and never interprets a
helper name as a mathematical specification.
"""

import argparse
import json
from pathlib import Path
import re


def record(value, size):
    if not isinstance(value, list) or len(value) != size:
        raise ValueError(f"expected array of size {size}")
    return value


def text(value):
    if not isinstance(value, str) or len(value.encode("utf-8")) > 512:
        raise ValueError("expected a UTF-8 string of at most 512 bytes")
    # JSON's backspace/form-feed escapes are not Lean escapes. Render each
    # character once, so literal backslashes cannot turn into escape prefixes.
    escapes = {'"': r'\"', '\\': r'\\', '\n': r'\n', '\r': r'\r', '\t': r'\t'}
    def character(char):
        if char in escapes:
            return escapes[char]
        if ord(char) < 32 or ord(char) == 127:
            return f"\\u{ord(char):04x}"
        return char
    return '"' + ''.join(character(char) for char in value) + '"'


def nat(value):
    if type(value) is not int or not 0 <= value <= 4096:
        raise ValueError("invalid bounded natural")
    return str(value)


def seq(values, render=nat):
    if not isinstance(values, list) or len(values) > 4096:
        raise ValueError("invalid bounded array")
    return "[" + ", ".join(render(value) for value in values) + "]"


def ty(value):
    if value == ["bool"]:
        return ".boolean"
    if value == ["index"]:
        return ".index"
    tag, domain = record(value, 2)
    if tag not in ("field", "vector", "group", "service"):
        raise ValueError("unsupported type")
    return f".{tag} {text(domain)}"


def descriptor(value):
    if not isinstance(value, list) or not value:
        raise ValueError("invalid descriptor")
    tag, *args = value
    unary = {"field.add": "fieldAdd", "field.subtract": "fieldSubtract",
             "field.multiply": "fieldMultiply", "field.equal": "fieldEqual",
             "group.identity": "groupIdentity", "group.add": "groupAdd",
             "group.equal": "groupEqual",
             "bounded_at": "boundedAt", "call": "call", "apply": "apply", "guard": "guard"}
    nullary = {"bool.and": "booleanAnd", "bool.or": "booleanOr", "bool.xor": "booleanXor",
               "bool.equal": "booleanEqual", "bool.not_equal": "booleanNotEqual",
               "if": "branch", "for": "loop", "for_condition": "loopCondition",
               "index.equal": "indexEqual"}
    if tag in unary:
        record(args, 1)
        return f".{unary[tag]} {text(args[0])}"
    if tag in nullary:
        record(args, 0)
        return "." + nullary[tag]
    if tag == "index.constant":
        record(args, 1)
        return f".indexConstant {text(args[0])}"
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
    if tag == "restrict":
        record(args, 1)
        return f".restrict {seq(args[0], text)}"
    if tag == "statement":
        relation_name, selectors, acceptance = record(args, 3)
        return f".statement {text(relation_name)} {seq(selectors, text)} {nat(acceptance)}"
    if tag in ("exchange", "draw", "group.scale"):
        record(args, 2)
        name = {"exchange": "exchange", "draw": "draw", "group.scale": "groupScale"}[tag]
        return "." + name + " " + " ".join(text(arg) for arg in args)
    if tag in ("field.constant", "local_call", "fold"):
        record(args, 3 if tag == "fold" else 2)
        name = {"field.constant": "fieldConstant", "local_call": "localCall", "fold": "fold"}[tag]
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
    tag, name, visibility, kind, key, revision, inputs, outputs, purposes = record(value, 9)
    if tag != "relation" or visibility not in ("public", "private"):
        raise ValueError("invalid relation")
    return (f"⟨{text(name)}, .{visibility}Def, {text(kind)}, {text(key)}, {text(revision)}, "
            f"{seq(inputs, ty)}, {seq(outputs, ty)}, {seq(purposes, text)}⟩")


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


def render(data, namespace):
    version, stage, source, entry, domains, relations, bindings, definitions = record(data, 8)
    if version != "zkc.structured-source/0" or stage != "original":
        raise ValueError("wrong version or stage")
    if not re.fullmatch(r"(?:[A-Za-z][A-Za-z0-9_]*\.)*[A-Za-z][A-Za-z0-9_]*", namespace):
        raise ValueError("invalid Lean namespace")
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

end {namespace}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", required=True)
    args = parser.parse_args()
    args.output.write_text(render(json.loads(args.input.read_text(encoding="utf-8")), args.namespace), encoding="utf-8")


if __name__ == "__main__":
    main()
