#!/usr/bin/env python3
"""Render a `zkc.constructed-participant/0` export as transparent Lean data.

This is a tested data boundary. Operations are classified by exact name,
operation binding and attribute set. An unrecognized operation is retained as
unsupported for the Lean rules to refuse; a recognized operation with another
shape, an unknown type or a malformed origin refuses the whole export.
Occurrence templates are decoded from their canonical bytes and re-encoded
exactly. A loop's body is rendered in its own reference scope: the environment
at the loop, then the induction index, the carried values and the body's
results; after the loop its results take the place of the body's values. A
loop's captured block arguments (operands after the count and the carried
values) denote their capture operands, unchanged in every iteration, so the
rendered body refers to those operands directly and the rendered loop keeps
only the count and the carried values. No proof is generated here and no
meaning is assigned to any operation.
"""

from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render  # noqa: E402
from bridges.construction.types import data_type, render_type  # noqa: E402
from bridges.common.lean_render import Refused as Refused  # noqa: E402
from bridges.common.lean_render import (  # noqa: E402
    CALCULATIONS, FIELD_MODULUS, decimal, origin, record, require, seq, text)

FORMAT = "zkc.constructed-participant/0"


def nat(value, limit=1 << 20):
    return lean_render.nat(value, limit)


def sort(value):
    """Return (Lean term, logical kind) for an exported MLIR type string."""
    require(isinstance(value, str), "type must be a string")
    match = re.fullmatch(r'!local\.capability<"transcript:([^"\\]+)">', value)
    if match:
        return f".transcript {text(match[1])}", ("transcript", match[1])
    if value == "!algebra.indices":
        return ".indices", ("indices", None)
    data = data_type(value)
    if data[0] in ("bool", "index"):
        tag = "boolean" if data[0] == "bool" else "index"
        return f".data .{tag}", (tag, None)
    if data[0] in ("field", "group", "vector"):
        return f".data ({render_type(data)})", (data[0], data[1])
    return f".data ({render_type(data)})", ("data", data)


def data_ty(kind):
    tag, domain = kind
    if tag == "data":
        return f"({render_type(domain)})"
    require(tag in ("boolean", "index", "field", "vector", "group"), "expected data type")
    return ".boolean" if tag == "boolean" else ".index" if tag == "index" else f"(.{tag} {text(domain)})"


def attributes(value):
    require(isinstance(value, list), "attributes must be an array")
    result = {}
    for item in value:
        name, attribute = record(item, 2)
        require(isinstance(name, str) and name not in result, "duplicate or invalid attribute")
        kind, payload = record(attribute, 2)
        require(kind in ("string", "symbol", "integer", "bool", "strings", "text"),
                "unknown attribute kind")
        if kind == "bool":
            valid = type(payload) is bool
        elif kind == "strings":
            valid = isinstance(payload, list) and all(isinstance(item, str) for item in payload)
        elif kind == "integer":
            valid = isinstance(payload, str) and re.fullmatch(r"0|-?[1-9][0-9]*", payload) is not None
        else:
            valid = isinstance(payload, str)
        require(valid, "invalid attribute payload")
        result[name] = (kind, payload)
    return result


def binding_attributes(attrs):
    """The typed attribute roles shared by the admitted bound operations."""
    return (set(attrs) == {"binding", "parameters", "site"}
            and attrs["binding"][0] == "symbol" and attrs["parameters"][0] == "strings"
            and attrs["site"][0] == "string")


def string_attribute(attrs, name):
    kind, payload = attrs.get(name, (None, None))
    require(kind == "string" and isinstance(payload, str), f"missing string attribute {name}")
    return payload


def one_parameter(attrs):
    kind, payload = attrs.get("parameters", (None, None))
    require(kind == "strings" and isinstance(payload, list) and len(payload) == 1, "expected one parameter")
    return payload[0]


def operation(name, attrs, binding, operand_kinds, result_kinds):
    """Classify one exported operation strictly; return its Lean term."""
    boolean, index = ("boolean", None), ("index", None)
    if name == "data.index":
        require(set(attrs) == {"value"} and binding == [] and operand_kinds == [] and result_kinds == [index],
                "index constant shape")
        return f".calculate (.indexConstant {decimal(string_attribute(attrs, 'value'), 1 << 64)})"
    if name == "data.index_equal":
        require(not attrs and binding == [] and operand_kinds == [index, index] and result_kinds == [boolean],
                "index equality shape")
        return ".calculate .indexEqual"
    if name == "arith.constant":
        require(set(attrs) == {"value"} and binding == [] and not operand_kinds and result_kinds == [boolean]
                and attrs["value"][0] == "bool" and type(attrs["value"][1]) is bool,
                "Boolean constant shape")
        return f".calculate (.booleanConstant {str(attrs['value'][1]).lower()})"
    if name == "arith.cmpi":
        require(set(attrs) == {"predicate"} and binding == [] and operand_kinds == [boolean, boolean]
                and result_kinds == [boolean] and attrs["predicate"] in (("integer", "0"), ("integer", "1")),
                "Boolean comparison shape")
        return ".calculate .booleanEqual" if attrs["predicate"][1] == "0" else ".calculate .booleanNotEqual"
    if name == "protocol.receive" and set(attrs) == {"peer", "schema", "site"} and binding == []:
        require(not operand_kinds and len(result_kinds) == 1, "receive shape")
        return (f".receive {text(string_attribute(attrs, 'site'))} {text(string_attribute(attrs, 'schema'))} "
                f"{text(string_attribute(attrs, 'peer'))} {data_ty(result_kinds[0])}")
    if name == "protocol.send" and set(attrs) == {"peer", "schema", "site"} and binding == []:
        return (f".send {text(string_attribute(attrs, 'site'))} {text(string_attribute(attrs, 'schema'))} "
                f"{text(string_attribute(attrs, 'peer'))}")
    if name == "algebra.exec.indices_empty" and binding == ["indices.empty", [], ""] \
            and binding_attributes(attrs) and attrs["parameters"] == ("strings", []):
        return ".indicesEmpty"
    if name == "algebra.exec.indices_append" and binding == ["indices.append", [], ""] \
            and binding_attributes(attrs) and attrs["parameters"] == ("strings", []):
        require(len(operand_kinds) == 2 and operand_kinds[0][0] == "indices" and operand_kinds[1][0] == "index"
                and len(result_kinds) == 1 and result_kinds[0][0] == "indices", "indices append shape")
        return ".indicesAppend"
    # The kernel site is a diagnostic frame name; it never enters transcript identity.
    if name == "crypto.exec.indexed_transcript_observe_data" and binding_attributes(attrs) \
            and isinstance(binding, list) and len(binding) == 3 \
            and binding[0] == "transcript.native.indexed.observe.data" and binding[2] == "":
        suite, leaf = record(binding[1], 2)
        require(len(operand_kinds) == 3 and operand_kinds[1][0] in ("field", "group")
                and leaf == f"{operand_kinds[1][0]}:{operand_kinds[1][1]}", "observed leaf type")
        return f".observe {text(suite)} {origin(one_parameter(attrs))}"
    if name == "crypto.exec.indexed_transcript_challenge" and binding_attributes(attrs) \
            and isinstance(binding, list) and len(binding) == 3 \
            and binding[0] == "transcript.native.indexed.challenge" and binding[2] == "":
        (suite,) = record(binding[1], 1)
        require(len(result_kinds) == 2 and result_kinds[0][0] == "field", "challenge results")
        return f".challenge {text(suite)} {text(result_kinds[0][1])} {origin(one_parameter(attrs))}"
    if name == "algebra.exec.field_embed":
        require(binding_attributes(attrs)
                and attrs["parameters"] == ("strings", []), "field embedding attributes")
        require(len(operand_kinds) == 1 and operand_kinds[0][0] == "field"
                and len(result_kinds) == 1 and result_kinds[0][0] == "field", "field embedding ports")
        extension, base = result_kinds[0][1], operand_kinds[0][1]
        require(isinstance(binding, list) and len(binding) == 3 and binding[0] == "field.embed"
                and binding[1] == [extension] and binding[2] == "", "field embedding binding")
        return f".calculate (.fieldEmbed {text(extension)} {text(base)})"
    if name == "algebra.group_scale" and not attrs and binding == []:
        require(len(operand_kinds) == 2 and operand_kinds[0][0] == "group" and operand_kinds[1][0] == "field",
                "group scale operands")
        return f".calculate (.groupScale {text(operand_kinds[0][1])} {text(operand_kinds[1][1])})"
    if name in CALCULATIONS and not attrs and binding == []:
        constructor, kind = CALCULATIONS[name]
        require(len(operand_kinds) == 2 and operand_kinds[0] == operand_kinds[1] and operand_kinds[0][0] == kind,
                "calculation operands")
        return f".calculate (.{constructor} {text(operand_kinds[0][1])})"
    if name == "arith.andi" and not attrs and binding == []:
        require(operand_kinds == [("boolean", None), ("boolean", None)]
                and result_kinds == [("boolean", None)], "boolean conjunction shape")
        return ".calculate .booleanAnd"
    if name == "algebra.constant" and set(attrs) == {"value"} and binding == []:
        # The canonical bound below is the BLS12-381 scalar modulus.
        require(not operand_kinds and len(result_kinds) == 1 and result_kinds[0] == ("field", "bls12-381.fr"),
                "field constant shape")
        return (f".calculate (.fieldConstant {text(result_kinds[0][1])} "
                f"{decimal(string_attribute(attrs, 'value'), FIELD_MODULUS)})")
    if name == "local.call" and set(attrs) == {"callee", "site"} and binding == []:
        kind, callee = attrs["callee"]
        require(kind == "symbol" and isinstance(callee, str), "call callee")
        return f".call {text(callee)}"
    if name == "local.guard" and set(attrs) == {"site"} and binding == []:
        require(operand_kinds == [("boolean", None)] and not result_kinds, "guard shape")
        return f".guard {text(string_attribute(attrs, 'site'))}"
    return f".unsupported {text(name)}"


def policy(value):
    (version, entry, producer, validator, acceptance, suite, services, public, draws,
     framing, construction) = record(value, 11)
    require(version == "zkc.native-proof-policy/0", "wrong policy version")
    require(isinstance(services, list) and isinstance(public, list) and isinstance(draws, list),
            "invalid policy lists")
    require(producer != validator and construction == "", "unsupported construction profile")
    if suite == "":
        require(services == [] and draws == [], "plain policy has a challenge replacement")
    else:
        require(isinstance(suite, str) and len(services) == 1 and draws, "invalid Fiat-Shamir profile")
    pairs = [record(pair, 2) for pair in draws]
    return (f"⟨{text(entry)}, {text(producer)}, {text(validator)}, {decimal(acceptance)}, {text(suite)}, "
            f"{seq(services, decimal)}, {seq(public, decimal)}, "
            f"{seq(pairs, lambda pair: f'({text(pair[0])}, {text(pair[1])})')}, {text(framing)}, {text(construction)}⟩")


def service_port(value):
    name, owner, root, input_, contract = record(value, 5)
    for item in (name, owner, contract):
        text(item, printable_ascii=True)
    return (f"⟨{text(name)}, {text(owner)}, {decimal(root)}, "
            f"{decimal(input_)}, {text(contract)}⟩")


def local_service(attrs, binding, operands, result_kinds, retained, ports, places, kinds):
    require(set(attrs) == {"port", "method", "site"} and binding == [], "local service attributes")
    name, method, site = (string_attribute(attrs, key) for key in ("port", "method", "site"))
    require(name in ports, "undeclared local service port")
    port = ports[name]
    require(method == "draw" and not operands and len(result_kinds) == 1
            and result_kinds[0][0] == "field", "unsupported local service request")
    field = result_kinds[0][1]
    require(port[4] == f"random.{field}/0", "local service nominal domain")
    encoded, coordinates = record(retained, 2)
    template = origin(encoded)
    _, _, steps, _, event = lean_render.template(encoded)
    require(len(event) == 7 and event[0] == "query" and event[4] == port[4]
            and event[5] == method and event[6] == port[1], "local service occurrence")
    prefix = None
    for kind, _, application in steps:
        if kind == "apply":
            prefix = application if prefix is None else f"apply_{len(prefix.encode('utf-8'))}_{prefix}_{application}"
    qualified = event[2] if prefix is None else f"apply_{len(prefix.encode('utf-8'))}_{prefix}_{event[2]}"
    require(site == qualified, "local service source site")
    mapped = references(coordinates, places, "local service coordinates")
    require(all(kinds[index] == ("index", None) for index in mapped), "local service coordinate sort")
    # Source/path/owner/root association is checked independently in Lean.
    require(isinstance(site, str) and site, "missing local service site")
    return (f".localService ({service_port(port)}) (Request.draw {text(field)}) "
            f"{template} {seq(mapped, nat)}")


# Sorts a loop may capture: immutable data, never a transcript.
CAPTURED = {"boolean", "index", "field", "vector", "group", "data"}


def references(values, places, what):
    """Map exported references to rendered ones; `places[r]` renders reference r."""
    require(isinstance(values, list) and all(type(o) is int and 0 <= o < len(places) for o in values),
            f"{what} reference out of range")
    return [places[o] for o in values]


def block(instructions, kinds, places, indent, depth=0, ports=None):
    """Render one block. `kinds` are the sorts of the rendered environment and
    `places` maps every exported reference in scope to its rendered reference.
    Return the rendered instructions, the final kinds and the final map."""
    require(depth <= 64 and isinstance(instructions, list) and len(instructions) <= 4096, "invalid block")
    rendered = []
    for item in instructions:
        record(item)
        is_service = bool(item) and item[0] == "protocol.service_query"
        record(item, 7 if is_service else 6)
        name, attrs, binding, operands, results, regions = item[:6]
        require(isinstance(name, str) and isinstance(regions, list), "operation name")
        mapped = references(operands, places, "operand")
        result_kinds = [sort(value)[1] for value in results]
        result_terms = seq(results, lambda v: sort(v)[0])
        fresh = len(kinds)
        if name == "protocol.loop":
            attributes_ = attributes(attrs)
            carried = len(results)
            require(set(attributes_) == {"carried", "count", "maximum", "parameter", "site"} and binding == []
                    and attributes_["count"] == ("string", "") and attributes_["parameter"] == ("bool", False)
                    and attributes_["carried"] == ("integer", str(carried)), "loop attributes")
            require(len(regions) == 1 and len(operands) >= carried + 1, "loop shape")
            arguments, nested, yielded = record(regions[0], 3)
            argument_kinds = [sort(value)[1] for value in arguments]
            captured = mapped[1 + carried:]
            captured_kinds = [kinds[o] for o in captured]
            require(argument_kinds == [("index", None)] + result_kinds + captured_kinds, "loop block arguments")
            require(all(kind[0] in CAPTURED for kind in captured_kinds), "loop capture sort")
            inner, _, inner_places = block(
                nested, kinds + argument_kinds[:1 + carried],
                places + list(range(fresh, fresh + 1 + carried)) + captured, indent + "    ", depth + 1, ports)
            yielded = references(yielded, inner_places, "yielded")
            maximum = decimal(attributes_["maximum"][1], 1048577) if attributes_["maximum"][0] == "integer" \
                else None
            require(maximum is not None, "loop maximum")
            term = f".loop {text(string_attribute(attributes_, 'site'))} {maximum} {seq(yielded, nat)}"
            body = "[]" if not inner else "[\n" + ",\n".join(inner) + "]"
            rendered.append(f"{indent}⟨{term}, {seq(mapped[:1 + carried], nat)}, {result_terms}, {body}⟩")
        else:
            require(regions == [], "unexpected operation region")
            if is_service:
                term = local_service(attributes(attrs), binding, mapped, result_kinds,
                                     item[6], ports or {}, places, kinds)
            else:
                term = operation(name, attributes(attrs), binding, [kinds[o] for o in mapped], result_kinds)
            rendered.append(f"{indent}⟨{term}, {seq(mapped, nat)}, {result_terms}, []⟩")
        kinds = kinds + result_kinds
        places = places + list(range(fresh, fresh + len(result_kinds)))
    return rendered, kinds, places


def render_declaration(data, namespace):
    version, source, candidate, selected, symbol, inputs, outputs, instructions, returned, services = record(data, 10)
    require(version == FORMAT, "wrong participant export version")
    lean_render.namespace(namespace)
    policy_term = policy(selected)
    require(isinstance(services, list) and len(services) <= 512, "invalid service interface")
    ports = {}
    roots, positions = set(), set()
    for port in services:
        service_port(port)
        require(port[0] not in ports and port[2] not in roots and port[3] not in positions,
                "duplicate service interface")
        require(port[1] in (selected[2], selected[3]), "service interface owner")
        ports[port[0]] = port
        roots.add(port[2])
        positions.add(port[3])
    kinds = [sort(value)[1] for value in inputs]
    if selected[5] == "":
        require(all(kind[0] in CAPTURED for kind in kinds + [sort(value)[1] for value in outputs]),
                "plain-profile-abi")
    rendered, kinds, places = block(instructions, kinds, list(range(len(kinds))), "    ", ports=ports)
    returned = references(returned, places, "returned")
    body = ",\n".join(rendered)
    return f'''namespace {namespace}
open Zkc.Construction

def participant : Participant where
  source := {text(source)}
  candidate := {text(candidate)}
  policy := {policy_term}
  symbol := {text(symbol)}
  inputs := {seq(inputs, lambda v: sort(v)[0])}
  outputs := {seq(outputs, lambda v: sort(v)[0])}
  instructions := [
{body}]
  returned := {seq(returned, nat)}{chr(10) + '  servicePorts := ' + seq(services, service_port) if services else ''}

end {namespace}
'''


def render(data, namespace):
    return 'module\n\npublic import Zkc.Construction.Participant\n\n@[expose] public section\n\n/-! Constructor data from the retained `zkc.constructed-participant/0` export.\nRegenerate with bridges/construction/check.py --write; the Lean rule and its proofs are\nseparate. The bridge checks exact regeneration against the compiler. -/\n\n' + render_declaration(data, namespace)


if __name__ == "__main__":
    lean_render.render_main(render, __doc__)
