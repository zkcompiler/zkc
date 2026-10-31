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
from bridges.common import lean_render, schema  # noqa: E402
from bridges.common.lean_render import optional, record  # noqa: E402

# The structured source profile bounds strings at 512 bytes and references at 4096.
text = partial(lean_render.text, limit=512)
nat = lean_render.nat
seq = lean_render.seq


def ty(value, depth=0):
    return interpreted_ty(schema.interpreted_type(value), depth)


def interpreted_ty(value, depth=0):
    """Render only the admitted aggregate grammar, retaining nominal identity."""
    if depth >= 64 or not isinstance(value, list) or not value:
        raise ValueError("invalid structured type")
    if value == ["indices"]:
        return ".indices"
    if value[0] == "groups":
        _, domain = record(value, 2)
        return f".groups {text(domain)}"
    if value[0] == "oracle":
        _, kind = record(value, 2)
        return f".oracle ({interpreted_oracle_kind(kind, depth + 1)})"
    if value[0] == "oracle_sequence":
        _, kind, maximum = record(value, 3)
        return f".oracleSequence ({interpreted_oracle_kind(kind, depth + 1)}) {lean_render.decimal(maximum, 2**64)}"
    if value[0] == "sequence":
        _, element = record(value, 2)
        return f".sequence ({interpreted_ty(element, depth + 1)})"
    if value[0] == "product":
        _, identity, constructor, fields = record(value, 4)
        if not isinstance(fields, list) or len(fields) > 512:
            raise ValueError("invalid product fields")
        components = ".nil"
        for field in reversed(fields):
            components = f".cons ({interpreted_ty(field, depth + 1)}) ({components})"
        return f".product {text(identity)} {text(constructor)} ({components})"
    return lean_render.interpreted_ty(value)


def oracle_kind(value, depth=0):
    schema.oracle_kind(value)
    projected = [value[0], [["type", schema.interpreted_type(value[1][0][1])], *value[1][1:]]]
    return interpreted_oracle_kind(projected, depth)


def interpreted_oracle_kind(value, depth=0):
    if depth >= 64:
        raise ValueError("invalid oracle kind depth")
    tag, arguments = record(value, 2)
    if tag != "table" or not isinstance(arguments, list) or len(arguments) not in (1, 2):
        raise ValueError("invalid oracle kind")
    type_tag, row = record(arguments[0], 2)
    if type_tag != "type":
        raise ValueError("invalid oracle row")
    rows = "none"
    if len(arguments) == 2:
        nat_tag, count = record(arguments[1], 2)
        if nat_tag != "nat":
            raise ValueError("invalid oracle extent")
        rows = f"some {lean_render.decimal(count, 2**64)}"
    return f".table ({interpreted_ty(row, depth + 1)}) ({rows})"


def oracle_shape(kind, value):
    oracle_kind(kind)
    expected = ["rows"] if len(kind[1]) == 1 else []
    pairs = [record(pair, 2) for pair in record(value)]
    if [pair[0] for pair in pairs] != expected:
        raise ValueError("invalid named oracle shape")
    return seq(pairs, lambda pair: f"({text(pair[0])}, {lean_render.decimal(pair[1], 2**64)})", 16)


def oracle_descriptor(tag, args):
    """Render wire data only; no operation receives semantic admission here."""
    if tag in ("oracle_input", "oracle_components"):
        record(args, 4 if tag == "oracle_input" else 3)
        holder, receivers, sort = args[:3]
        projected = schema.interpreted_type(sort)
        if projected[0] not in ("oracle", "oracle_sequence"):
            raise ValueError("invalid oracle logical sort")
        # The complete sort retains the singleton/sequence distinction and capacity.
        rendered = interpreted_ty(projected)
        extra = ""
        if tag == "oracle_input":
            extra = " " + oracle_shape(sort[1:3], args[3])
        return (f".oracle (.{tag.removeprefix('oracle_')} {text(holder)} {seq(receivers, text, 16)} "
                f"({rendered}){extra})")
    if tag in ("oracle_send", "oracle_virtual"):
        size = {"oracle_send": 5, "oracle_virtual": 4}[tag]
        record(args, size)
        declaration = text(args[0]) + " " if tag == "oracle_virtual" else ""
        holder, receivers, kind = args[1:4] if declaration else args[:3]
        extra = ""
        if tag == "oracle_send":
            if args[3] != ["rows"]:
                raise ValueError("invalid oracle dimensions")
            extra = f" {seq(args[3], text, 16)} {oracle_shape(kind, args[4])}"
        constructor = tag.removeprefix("oracle_")
        return (f".oracle (.{constructor} {declaration}{text(holder)} {seq(receivers, text, 16)} "
                f"({oracle_kind(kind)}){extra})")
    if tag in ("oracle_query", "oracle_contents"):
        owner, kind = record(args, 2)
        owner_text = f"({optional(owner, text)})" if tag == "oracle_query" else text(owner)
        return f".oracle (.{tag.removeprefix('oracle_')} {owner_text} ({oracle_kind(kind)}))"
    if tag == "oracle_shape":
        kind, dimension = record(args, 2)
        if dimension != "rows":
            raise ValueError("invalid oracle dimension")
        return f".oracle (.shape ({oracle_kind(kind)}) {text(dimension)})"
    if tag == "oracle_forget_shape":
        source, target = record(args, 2)
        return f".oracle (.forgetShape ({oracle_kind(source)}) ({oracle_kind(target)}))"
    names = {"oracle_sequence_empty": "sequenceEmpty", "oracle_sequence_append": "sequenceAppend",
             "oracle_sequence_at": "sequenceAt", "oracle_sequence_length": "sequenceLength"}
    if tag in names:
        record(args, 3 if tag in ("oracle_sequence_append", "oracle_sequence_at") else 2)
        kind, maximum = args[:2]
        roles = " " + seq(args[2], text, 16) if len(args) == 3 else ""
        return f".oracle (.{names[tag]} ({oracle_kind(kind)}) {lean_render.decimal(maximum, 2**64)}{roles})"
    raise ValueError("unknown oracle descriptor")


def descriptor(value):
    if not isinstance(value, list) or not value:
        raise ValueError("invalid descriptor")
    tag, *args = value
    if tag.startswith("oracle_"):
        return oracle_descriptor(tag, args)
    if tag in ("index.less", "index.power_of_two"):
        record(args, 0)
        return ".indexLess" if tag == "index.less" else ".indexPowerOfTwo"
    if tag == "vector.length":
        record(args, 1)
        return f".vectorLength {text(args[0])}"
    if tag == "multilinear.restrict_prefix":
        record(args, 1)
        return f".multilinearRestrictPrefix {text(args[0])}"
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
    if tag == "product.make":
        record(args, 1)
        return f".makeProduct {text(args[0])}"
    if tag == "product.get":
        record(args, 1)
        return f".getProduct {nat(args[0], 511)}"
    if tag == "field.embed":
        extension, base = record(args, 2)
        return f".fieldEmbed {text(extension)} {text(base)}"
    if tag == "exec":
        operation, binding_name, parameters = record(args, 3)
        return f".exec {text(operation)} {text(binding_name)} {seq(parameters, render_parameter)}"
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
    if tag in ("restrict", "assemble"):
        record(args, 1)
        return f".{tag} {seq(args[0], text, 16)}"
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


def domain_constructor(value):
    if value[0] == "elements":
        _, index = record(value, 2)
        return ".elements " + nat(index)
    if value[0] in ("indices", "range"):
        tag, first, second = record(value, 3)
        return f".{tag} {nat(first)} {nat(second)}"
    if value[0] in ("zip", "product"):
        tag, operands = record(value, 2)
        return f".{tag} {seq(operands, nat)}"
    raise ValueError("unsupported domain constructor")


def domain(value):
    tag, name, inputs, constructors, result = record(value, 5)
    if tag != "domain":
        raise ValueError("invalid domain")
    return f"⟨{text(name)}, {seq(inputs, ty)}, {seq(constructors, domain_constructor)}, {nat(result)}⟩"


def protocol_interface(value):
    if value == []:
        return "none"
    tag, roles, inputs, outputs = record(value, 4)
    if tag != "protocol":
        raise ValueError("invalid protocol interface")
    return f"some ⟨{seq(roles, text)}, {seq(inputs, lambda x: seq(x, text))}, {seq(outputs, lambda x: seq(x, text))}⟩"


def relation(value):
    tag, name, visibility, kind, key, revision, statics, inputs, outputs, purposes, formula = record(value, 11)
    if tag != "relation" or visibility not in ("public", "private"):
        raise ValueError("invalid relation")
    if not isinstance(statics, list) or len(statics) > 128:
        raise ValueError("invalid relation static arguments")
    remaining = [4096]
    arguments = seq(statics, lambda term: origin_term(term, remaining=remaining))
    return (f"⟨{text(name)}, .{visibility}Def, {text(kind)}, {text(key)}, {text(revision)}, "
            f"{seq(inputs, ty)}, {seq(outputs, ty)}, {seq(purposes, text)}, "
            f"{optional(formula, text)}, {arguments}⟩")


def contract_selector(value):
    if isinstance(value, list) and len(value) == 3 and value[0] == "anchor":
        _, direction, port = value
        if direction not in ("input", "output"):
            raise ValueError("invalid anchor selector direction")
        return f'⟨.{direction}, {nat(port)}, "", true⟩'
    direction, port, role = record(value, 3)
    if direction not in ("input", "output"):
        raise ValueError("invalid contract selector direction")
    return f"⟨.{direction}, {nat(port)}, {text(role)}, false⟩"


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


# Independently selected interpreter vocabulary; catalog membership is data only.
SOURCE_PRIMITIVES = frozenset((
    "index.constant", "index.add", "index.sub", "index.mul", "index.div", "index.mod",
    "index.equal", "index.less", "vector.empty", "vector.length", "vector.sum",
    "vector.split", "vector.append", "vector.equal", "field.equal", "field.embed"))


def render_parameter(value):
    schema.parameter(value)
    if value[0] != "natural":
        raise ValueError("parameter has no installed source interpretation")
    return text(value[1])


def binding_argument(value):
    """Retain kinded actuals as data after the selected signature was checked."""
    schema.argument(value, mask=True)
    if value[0] == "domain":
        return f".domain {text(value[1])} {text(value[2])}"
    if value[0] == "type":
        return f".type ({ty(value[1])})"
    if value[0] == "nat":
        return f".natural {lean_render.decimal(value[1], 2**64)}"
    return f".mask {seq(value[1], lambda bit: str(bit).lower())}"


def primitive_binding(value, rows=None):
    actual = schema.binding(value, source=True)
    op, terms = schema.resolve_signature(actual, project=member_resolver(rows), allowed=SOURCE_PRIMITIVES)
    if actual[2] != "":
        raise ValueError("selected implementation outside source profile")
    nominals = {row[1]: row for row in rows[0]} if rows else {}
    for requirement in op["requirements"]:
        arguments = [terms[i] for i in requirement["arguments"]]
        if len(arguments) != 1 or arguments[0][0] != "domain":
            raise ValueError("unsupported source requirement")
        domain = nominals.get(arguments[0][2])
        if domain is None or requirement["capability"] not in domain[4]:
            raise ValueError("missing binding capability")
    # The installed source primitives have only Field roots. The neutral tree
    # and supplied ports were checked above before this semantic projection.
    arguments = [argument[2] for argument in actual[1]]
    return (f"⟨{text(value[1])}, {text(actual[0])}, {seq(arguments, text)}, "
            f"{text(actual[2])}, some ⟨{seq(actual[1], binding_argument)}, "
            f"{seq(actual[3], ty)}, {seq(actual[4], ty)}⟩⟩")


def member_resolver(rows):
    def project(parent, member):
        if rows is None or parent[0] != "domain":
            raise ValueError("missing associated domain catalogue")
        matches = [row for row in rows[0] if row[1] == parent[2] and row[2] == parent[1]]
        if len(matches) != 1:
            raise ValueError("unknown associated domain")
        members = dict(matches[0][3])
        if member not in members:
            raise ValueError("missing associated domain member")
        declarations = [row for row in schema.declarations()["members"]
                        if row["name"] == member and row["owner"]["sort"] == parent[1]]
        if len(declarations) != 1:
            raise ValueError("unknown associated member declaration")
        return ["domain", declarations[0]["result"]["sort"], members[member]]
    return project


def origin_string(value, limit=512):
    """Preserve exact bytes; NFC is checked by native frontend admission."""
    rendered = lean_render.text(value, limit=limit)
    if not value or "\0" in value:
        raise ValueError("empty origin string")
    return rendered


def origin_decimal(value):
    rendered = origin_string(value)
    if re.fullmatch(r"0|[1-9][0-9]*", value) is None:
        raise ValueError("noncanonical origin decimal")
    return rendered


def origin_path(value, limit=512):
    rendered = origin_string(value, limit)
    def initial(char):
        return ord(char) >= 128 or "a" <= char <= "z" or "A" <= char <= "Z" or char == "_"
    if not all(part and initial(part[0]) and all(initial(c) or "0" <= c <= "9" for c in part)
               for part in value.split("::")):
        raise ValueError("invalid origin path")
    return rendered


def origin_term(value, depth=0, remaining=None):
    if remaining is None:
        remaining = [4096]
    if remaining[0] == 0:
        raise ValueError("origin term count limit")
    remaining[0] -= 1
    if depth >= 64:
        raise ValueError("origin nesting limit")
    record(value)
    if not value:
        raise ValueError("empty origin term")
    tag, *args = value
    if tag == "nat":
        record(args, 1)
        return f"(.natural {origin_decimal(args[0])})"
    if tag in ("field", "group"):
        record(args, 1)
        return f"(.{tag} {origin_string(args[0])})"
    if tag in ("domain", "asset"):
        sort, identity = record(args, 2)
        return f"(.{tag} {origin_string(sort)} {origin_string(identity)})"
    if tag in ("bool", "index", "unit"):
        record(args, 0)
        return ".boolean" if tag == "bool" else f".{tag}"
    def child(term):
        return origin_term(term, depth + 1, remaining)
    if tag == "tuple":
        record(args, 1)
        return f"(.tuple {seq(args[0], child, limit=512)})"
    if tag == "array":
        element, length = record(args, 2)
        return f"(.array {child(element)} {origin_decimal(length)})"
    if tag == "nominal":
        kind, path, arguments = record(args, 3)
        if kind not in ("record", "logical_record", "variant", "associated", "module"):
            raise ValueError("invalid origin nominal kind")
        constructor = {"module": "moduleType", "logical_record": "logicalRecord"}.get(kind, kind)
        return (f"(.nominal .{constructor} {origin_path(path)} "
                f"{seq(arguments, child, limit=512)})")
    if tag in ("builtin", "formal"):
        name, arguments = record(args, 2)
        return f"(.{tag} {origin_string(name)} {seq(arguments, child, limit=512)})"
    raise ValueError("unknown origin term")


def function_origin(kind, value):
    if kind == "math":
        record(value, 0)
        return "none"
    if kind not in ("local", "protocol"):
        raise ValueError("invalid origin function kind")
    name, arguments = record(value, 2)
    keys = set()
    remaining = [4096]

    def argument(pair):
        key, term = record(pair, 2)
        rendered_key = origin_path(key) if kind == "protocol" else origin_string(key)
        if kind == "protocol" and "::" in key:
            raise ValueError("qualified origin parameter")
        if key in keys:
            raise ValueError("duplicate origin parameter")
        keys.add(key)
        rendered = origin_term(term, remaining=remaining) if kind == "protocol" else origin_string(term)
        return f"({rendered_key}, {rendered})"

    name = origin_path(name, 2048) if kind == "protocol" else origin_string(name)
    arguments = seq(arguments, argument, limit=128)
    if kind == "protocol":
        return f"some (.protocol ⟨{name}, {arguments}⟩)"
    return f"some (.local {name} {arguments})"


def definition(value):
    if value[0] == "oracle":
        _, name, inputs, kind, admissibility, shape, maximum, body = record(value, 8)
        return (f".oracle ⟨{text(name)}, {seq(inputs, ty)}, ({oracle_kind(kind)}), "
                f"{text(admissibility)}, {oracle_shape(kind, shape)}, {oracle_shape(kind, maximum)}, ({block(body)})⟩")
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
    if value[0] in ("finite", "collect"):
        _, name, visibility, inputs, outputs, domain_name, step, predicate = record(value, 8)
        if visibility not in ("public", "private"):
            raise ValueError("invalid visibility")
        return (f".{value[0]} ⟨{text(name)}, .{visibility}Def, {seq(inputs, ty)}, {seq(outputs, ty)}, "
                f"{text(domain_name)}, {text(step)}, {text(predicate)}⟩")
    tag, name, kind, visibility, inputs, outputs, interface, premises, origin, body = record(value, 10)
    if tag != "function" or kind not in ("protocol", "math", "local") or visibility not in ("public", "private"):
        raise ValueError("invalid function header")
    origin_text = function_origin(kind, origin)
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


def source_record(value):
    type_, resource, sealed, fields = record(value, 4)
    if resource not in ("ordinary", "affine", "linear") or type(sealed) is not bool:
        raise ValueError("invalid source record")

    def field(value):
        name, type_ = record(value, 2)
        return f"({text(name)}, {origin_term(type_)})"

    return (f"⟨{origin_term(type_)}, {text(resource)}, {str(sealed).lower()}, "
            f"{seq(fields, field)}⟩")


def source_port(value):
    name, type_, roles, offset, count = record(value, 5)
    return (f"⟨{text(name)}, {origin_term(type_)}, {seq(roles, text, limit=16)}, "
            f"{nat(offset)}, {nat(count, 512)}⟩")


def source_protocol(value):
    name, inputs, outputs = record(value, 3)
    return f"⟨{text(name)}, {seq(inputs, source_port)}, {seq(outputs, source_port)}⟩"


def source_declarations(value):
    records, protocols = record(value, 2)
    return (f"{{ records := {seq(records, source_record)}, "
            f"protocols := {seq(protocols, source_protocol)} }}")


def render(data, namespace):
    version, stage, source, entry, domains, relations, bindings, definitions, contracts, rows, declarations = record(data, 11)
    if version != "zkc.structured-source/0" or stage != "original":
        raise ValueError("wrong version or stage")
    lean_render.namespace(namespace)
    catalogue_term = catalogue(rows)
    installed = {}
    for value in bindings:
        primitive_binding(value, rows)
        if value[1] in installed:
            raise ValueError("duplicate source binding")
        installed[value[1]] = value[2:]

    def invocations(value):
        if not isinstance(value, list):
            return
        if value and value[0] == "exec":
            _, operation, name, parameters = record(value, 4)
            if operation != "exec.apply" or name not in installed:
                raise ValueError("unknown source primitive binding")
            op, _ = schema.resolve_signature(installed[name], member_resolver(rows), SOURCE_PRIMITIVES)
            schema.validate_parameters(parameters, op["parameters"])
        for child in value:
            invocations(child)
    invocations(definitions)
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
  bindings := {seq(bindings, lambda value: primitive_binding(value, rows))}
  definitions := {seq(definitions, definition)}
  contracts := {seq(contracts, protocol_contract)}
  catalogue := {catalogue_term}
  sourceDeclarations := {source_declarations(declarations)}

end {namespace}
'''


if __name__ == "__main__":
    lean_render.render_main(render, __doc__, read=lambda path: schema.loads(path.read_bytes()))
