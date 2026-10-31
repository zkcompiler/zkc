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
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render, schema  # noqa: E402
from bridges.construction.types import data_type, render_type  # noqa: E402
from bridges.common.lean_render import Refused as Refused  # noqa: E402
from bridges.common.lean_render import (  # noqa: E402
    CALCULATIONS, FIELD_MODULUS, decimal, origin, record, require, seq, text)

FORMAT = "zkc.constructed-participant/0"


def nat(value, limit=1 << 20):
    return lean_render.nat(value, limit)


def sort(value):
    """Return (Lean term, interpreted kind) from a complete logical Type."""
    schema.logical_type(value)
    if value[0] == "apply" and value[1] == "transcript":
        suite = value[2][0][2]
        return f".transcript {text(suite)}", ("transcript", suite)
    if value == ["apply", "indices", []]:
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
    """Validate all semantic attributes before an operation can omit diagnostics."""
    decoded = schema.attributes(value)
    return {name: (attribute[0], attribute[1:] if attribute[0] == "integer" else attribute[1])
            for name, attribute in decoded.items()}


def binding_attributes(attrs):
    return (set(attrs) == {"binding", "parameters", "site"}
            and attrs["binding"][0] == "symbol" and len(attrs["binding"][1]) == 1
            and attrs["parameters"][0] == "array"
            and all(item[0] == "parameter" for item in attrs["parameters"][1])
            and attrs["site"][0] == "string")


def integer_attribute(attrs, name, *, signedness="signless", width="64"):
    kind, payload = attrs.get(name, (None, None))
    require(kind == "integer" and payload[:2] == [signedness, width],
            f"expected {signedness} i{width} attribute {name}")
    return payload[2]


def string_attribute(attrs, name):
    kind, payload = attrs.get(name, (None, None))
    require(kind == "string" and isinstance(payload, str), f"missing string attribute {name}")
    return payload


def one_parameter(attrs):
    kind, payload = attrs.get("parameters", (None, None))
    require(kind == "array" and isinstance(payload, list) and len(payload) == 1
            and payload[0][0] == "parameter", "expected one parameter")
    return schema.origin_hex(payload[0][1])


# This bounded interpretation's nominal associations are explicit. They are not
# inferred from supplied signature ports or parsed from a suite's display name.
CONSTRUCTION_PRIMITIVES = frozenset((
    "indices.empty", "indices.append", "transcript.native.indexed.observe.data",
    "transcript.native.indexed.challenge", "field.embed"))

CONSTRUCTION_MEMBERS = {
    ("Field", "koala-bear.ext8-binomial3", "BaseField"): ("Field", "koala-bear"),
    ("Field", "koala-bear.ext4-binomial3", "BaseField"): ("Field", "koala-bear"),
    ("Field", "baby-bear.ext4-binomial11", "BaseField"): ("Field", "baby-bear"),
    ("Field", "goldilocks.ext2-binomial7", "BaseField"): ("Field", "goldilocks"),
    ("Transcript", "merlin3.bls12-381.fr64be/0", "ChallengeField"): ("Field", "bls12-381.fr"),
    ("Transcript", "merlin3.ristretto255.scalar64le/0", "ChallengeField"): ("Field", "ristretto255.scalar"),
    ("Transcript", "spongefish0.8.0.keccak.bls12-381.fr64be/0", "ChallengeField"): ("Field", "bls12-381.fr"),
    ("Transcript", "merlin3.koala-bear.ext8-binomial3.rejection31le/0", "ChallengeField"):
        ("Field", "koala-bear.ext8-binomial3"),
    ("Transcript", "merlin3.baby-bear.ext4-binomial11.rejection31le/0", "ChallengeField"):
        ("Field", "baby-bear.ext4-binomial11"),
    ("Transcript", "merlin3.goldilocks.ext2-binomial7.rejection64le/0", "ChallengeField"):
        ("Field", "goldilocks.ext2-binomial7"),
}


def construction_member(parent, member):
    require(parent[0] == "domain", "associated member parent kind")
    key = (parent[1], parent[2], member)
    require(key in CONSTRUCTION_MEMBERS, "uninstalled construction associated member")
    return ["domain", *CONSTRUCTION_MEMBERS[key]]


def operation(name, attrs, binding, operand_kinds, result_kinds):
    """Classify one exported operation strictly; return its Lean term."""
    schema.binding(binding)
    boolean, index = ("boolean", None), ("index", None)
    if name == "data.index":
        require(set(attrs) == {"value"} and binding == [] and operand_kinds == [] and result_kinds == [index],
                "index constant shape")
        value = integer_attribute(attrs, "value", signedness="unsigned")
        return f".calculate (.indexConstant {decimal(value, 1 << 64)})"
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
                and result_kinds == [boolean] and integer_attribute(attrs, "predicate") in ("0", "1"),
                "Boolean comparison shape")
        return ".calculate .booleanEqual" if integer_attribute(attrs, "predicate") == "0" else ".calculate .booleanNotEqual"
    if name == "protocol.receive" and set(attrs) == {"peer", "schema", "site"} and binding == []:
        require(not operand_kinds and len(result_kinds) == 1, "receive shape")
        return (f".receive {text(string_attribute(attrs, 'site'))} {text(string_attribute(attrs, 'schema'))} "
                f"{text(string_attribute(attrs, 'peer'))} {data_ty(result_kinds[0])}")
    if name == "protocol.send" and set(attrs) == {"peer", "schema", "site"} and binding == []:
        return (f".send {text(string_attribute(attrs, 'site'))} {text(string_attribute(attrs, 'schema'))} "
                f"{text(string_attribute(attrs, 'peer'))}")
    if name == "exec.apply":
        require(binding_attributes(attrs), "execution binding attributes")
        contract, arguments, implementation, inputs, outputs = schema.binding(binding)
        require(implementation == "", "execution binding implementation")
        parameters = [value[1] for value in attrs["parameters"][1]]
        if contract not in CONSTRUCTION_PRIMITIVES:
            return f".unsupported {text(name + ':' + contract)}"
        declaration, _ = schema.resolve_signature(binding, construction_member, CONSTRUCTION_PRIMITIVES)
        schema.validate_parameters(parameters, declaration["parameters"])
        require([sort(value)[1] for value in inputs] == operand_kinds
                and [sort(value)[1] for value in outputs] == result_kinds,
                "execution binding actual ports")
        if contract == "indices.empty":
            require(not arguments and not parameters and not operand_kinds
                    and result_kinds == [("indices", None)], "indices empty shape")
            return ".indicesEmpty"
        if contract == "indices.append":
            require(not arguments and not parameters
                    and operand_kinds == [("indices", None), index]
                    and result_kinds == [("indices", None)], "indices append shape")
            return ".indicesAppend"
        # The execution site is a diagnostic frame name, separate from transcript identity.
        if contract == "transcript.native.indexed.observe.data":
            require(schema.origin_structure(parameters[0][1])[0] == "message", "observation origin event")
            suite_arg, leaf_arg = record(arguments, 2)
            suite, leaf = suite_arg[2], schema.interpreted_type(leaf_arg[1])
            require(len(operand_kinds) == 3 and operand_kinds[0] == ("transcript", suite)
                    and operand_kinds[1][0] in ("field", "group")
                    and operand_kinds[2] == ("indices", None)
                    and result_kinds == [("transcript", suite)]
                    and leaf == list(operand_kinds[1]), "observed leaf type")
            return f".observe {text(suite)} {origin(one_parameter(attrs))}"
        if contract == "transcript.native.indexed.challenge":
            event = schema.origin_structure(parameters[0][1])
            require(event[0] == "query" and event[5] == "draw", "challenge origin method")
            (suite_arg,) = record(arguments, 1)
            suite = suite_arg[2]
            require(operand_kinds == [("transcript", suite), ("indices", None)]
                    and len(result_kinds) == 2 and result_kinds[0][0] == "field"
                    and result_kinds[1] == ("transcript", suite), "challenge results")
            return f".challenge {text(suite)} {text(result_kinds[0][1])} {origin(one_parameter(attrs))}"
        if contract == "field.embed":
            require(not parameters, "field embedding attributes")
            require(len(operand_kinds) == 1 and operand_kinds[0][0] == "field"
                    and len(result_kinds) == 1 and result_kinds[0][0] == "field", "field embedding ports")
            extension, base = result_kinds[0][1], operand_kinds[0][1]
            require(arguments == [["domain", "Field", extension]], "field embedding binding")
            return f".calculate (.fieldEmbed {text(extension)} {text(base)})"
        return f".unsupported {text(name + ':' + contract)}"
    if name == "exec.boolean":
        require(set(attrs) == {"value", "site"} and binding == [] and not operand_kinds
                and result_kinds == [boolean] and attrs["value"][0] == "bool",
                "Boolean execution shape")
        string_attribute(attrs, "site")
        return f".calculate (.booleanConstant {str(attrs['value'][1]).lower()})"
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
        kind, literal = attrs["value"]
        require(kind == "parameter" and literal[:3] ==
                ["field_literal", result_kinds[0][1], "natural"], "field constant parameter")
        return (f".calculate (.fieldConstant {text(result_kinds[0][1])} "
                f"{decimal(literal[3], FIELD_MODULUS)})")
    if name in ("protocol.local_call", "func.call"):
        expected = {"callee", "site", "role"} if name == "protocol.local_call" else {"callee", "runtime.site"}
        require(set(attrs) == expected and binding == [], "call attributes")
        string_attribute(attrs, "site" if name == "protocol.local_call" else "runtime.site")
        if name == "protocol.local_call":
            require(bool(string_attribute(attrs, "role")), "call role")
        kind, callee = attrs["callee"]
        require(kind == "symbol" and isinstance(callee, list) and len(callee) == 1, "call callee")
        return f".call {text(callee[0])}"
    if name == "protocol.guard" and set(attrs) == {"site", "owner"} and binding == []:
        require(bool(string_attribute(attrs, "owner")), "guard owner")
        require(operand_kinds == [("boolean", None)] and not result_kinds, "guard shape")
        return f".guard {text(string_attribute(attrs, 'site'))}"
    return f".unsupported {text(name)}"


def policy(value):
    (version, entry, producer, validator, acceptance, suite, services, public, draws,
     framing, construction, gates) = record(value, 12)
    require(version == "zkc.native-proof-policy/0", "wrong policy version")
    require(gates == [], "unsupported policy gates")
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
        schema.binding(binding)
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
                    and integer_attribute(attributes_, "carried") == str(carried), "loop attributes")
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
            maximum = decimal(integer_attribute(attributes_, "maximum"), 1048577)
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
    lean_render.render_main(render, __doc__, read=lambda path: schema.loads(path.read_bytes()))
