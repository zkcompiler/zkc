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
only the count and the carried values. Associated members, binding capability
facts and the fields that random services sample are read from the export's
catalogue rows, which are rendered beside the participant for Lean to check
against its own catalogue. No proof is generated here and no meaning is
assigned to any operation.
"""

from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import catalogue, lean_render, policy as native_policy, schema  # noqa: E402
from bridges.structured.snapshot import product_fields
from bridges.construction.types import data_type, render_type  # noqa: E402
from bridges.common.lean_render import Refused as Refused  # noqa: E402
from bridges.common.lean_render import (  # noqa: E402
    CALCULATIONS, decimal, origin, record, require, seq, text)

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
        return ".data .indices", ("data", ["indices"])
    slot = schema.custody_slot(value)
    if slot is not None:
        # A custody permission: a sort of its own, never an ordinary payload.
        return f".data (.resourceUnit {text(slot)})", ("custody", slot)
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


def data_descriptor(kind):
    tag, domain = kind
    if tag == "data":
        return domain
    require(tag in ("boolean", "index", "field", "vector", "group"), "expected data type")
    if tag in ("boolean", "index"):
        return ["bool" if tag == "boolean" else "index"]
    return [tag, domain]


def nominal_product(kind):
    descriptor = data_descriptor(kind)
    require(len(descriptor) == 4 and descriptor[0] == "product", "expected nominal product")
    return descriptor[1:]


def product_parameters(identity, constructor, fields):
    return f"{text(identity)} {text(constructor)} ({product_fields(fields)})"


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


# The operations this bounded interpretation classifies. Their associated
# members are projected through the export's catalogue rows, never inferred
# from supplied signature ports or parsed from a suite's display name.
CONSTRUCTION_PRIMITIVES = frozenset((
    "index.constant", "indices.empty", "indices.append", "transcript.native.indexed.observe.data",
    "transcript.native.indexed.index", "transcript.native.indexed.indices",
    "transcript.native.indexed.challenge", "field.embed", "control.require", "index.equal", "index.less", "index.add", "bool.not", "vector.get", "vector.length",
    "sequence.empty", "sequence.append", "sequence.length", "sequence.at"))


def operation(name, attrs, binding, operand_kinds, result_kinds, rows, operand_values=None):
    """Classify one exported operation strictly; return its Lean term."""
    schema.binding(binding)
    boolean, index = ("boolean", None), ("index", None)
    if name == "exec.variant":
        require(set(attrs) == {"alternative", "site"} and binding == [] and len(result_kinds) == 1,
                "product construction shape")
        identity, constructor, fields = nominal_product(result_kinds[0])
        require(string_attribute(attrs, "alternative") == constructor
                and [data_descriptor(kind) for kind in operand_kinds] == fields,
                "product construction fields")
        string_attribute(attrs, "site")
        return f".calculate (.makeProduct {product_parameters(identity, constructor, fields)})"
    if name == "data.index":
        require(set(attrs) == {"value"} and binding == [] and operand_kinds == [] and result_kinds == [index],
                "index constant shape")
        value = integer_attribute(attrs, "value", signedness="unsigned")
        return f".calculate (.indexConstant {decimal(value, 1 << 64)})"
    if name in ("data.sequence_empty", "data.sequence_append", "data.sequence_length"):
        require(not attrs and not binding, "mathematical sequence metadata")
        empty = name == "data.sequence_empty"
        require(len(result_kinds) == 1 and (empty or operand_kinds), "mathematical sequence arity")
        container = data_descriptor(result_kinds[0] if empty else operand_kinds[0])
        require(len(container) == 2 and container[0] == "sequence", "mathematical sequence type")
        element = container[1]
        inputs = [] if empty else ([container, element] if name == "data.sequence_append" else [container])
        output = ["index"] if name == "data.sequence_length" else container
        require([data_descriptor(kind) for kind in operand_kinds] == inputs and
                data_descriptor(result_kinds[0]) == output, "mathematical sequence ports")
        constructor = {"data.sequence_empty": "sequenceEmpty", "data.sequence_append": "sequenceAppend",
                       "data.sequence_length": "sequenceLength"}[name]
        return f".calculate (.{constructor} ({render_type(element)}))"
    if name == "data.index_equal":
        require(not attrs and binding == [] and operand_kinds == [index, index] and result_kinds == [boolean],
                "index equality shape")
        return ".calculate .indexEqual"
    index_words = {
        "data.index_wrapping_add": "indexWrappingAdd",
        "data.index_wrapping_subtract": "indexWrappingSubtract",
        "data.index_bit_and": "indexBitAnd",
        "data.index_logical_shift_right": "indexLogicalShiftRight",
    }
    if name in index_words:
        require(not attrs and binding == [] and operand_kinds == [index, index]
                and result_kinds == [index], "index word shape")
        return f".calculate .{index_words[name]}"
    if name == "arith.select":
        require(not attrs and binding == [] and len(operand_kinds) == 3
                and operand_kinds[0] == boolean and operand_kinds[1] == operand_kinds[2]
                and result_kinds == [operand_kinds[1]] and operand_kinds[1][0] in CAPTURED,
                "data select shape")
        return f".calculate (.select {data_ty(operand_kinds[1])})"
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
        declaration, terms = schema.resolve_signature(binding, catalogue.member_resolver(rows),
                                                      CONSTRUCTION_PRIMITIVES)
        catalogue.require_capabilities(declaration, terms, rows)
        schema.validate_parameters(parameters, declaration["parameters"])
        def logical_kind(kind):
            return ("data", ["indices"]) if kind == ("indices", None) else kind
        require([sort(value)[1] for value in inputs] == [logical_kind(k) for k in operand_kinds]
                and [sort(value)[1] for value in outputs] == [logical_kind(k) for k in result_kinds],
                "execution binding actual ports")
        if contract in ("sequence.empty", "sequence.append", "sequence.length", "sequence.at"):
            require(not parameters and len(arguments) == 1 and arguments[0][0] == "type",
                    "sequence static element type")
            element = data_type(arguments[0][1])
            constructor = {"sequence.empty": "sequenceEmpty", "sequence.append": "sequenceAppend",
                           "sequence.length": "sequenceLength", "sequence.at": "sequenceAt"}[contract]
            return f".execute (.{constructor} ({render_type(element)}))"
        if contract in ("index.equal", "index.less", "index.add"):
            result = index if contract == "index.add" else boolean
            require(not arguments and not parameters and operand_kinds == [index, index]
                    and result_kinds == [result], "checked index ports")
            constructor = {"index.equal": "indexEqual", "index.less": "indexLess", "index.add": "indexAdd"}[contract]
            return f".execute .{constructor}"
        if contract == "bool.not":
            require(not arguments and not parameters and operand_kinds == [boolean]
                    and result_kinds == [boolean], "Boolean negation ports")
            return ".execute .booleanNot"
        if contract == "vector.length":
            require(not parameters and len(operand_kinds) == 1 and operand_kinds[0][0] == "vector"
                    and result_kinds == [index], "checked vector length ports")
            return f".execute (.vectorLength {text(operand_kinds[0][1])})"
        if contract == "vector.get":
            require(not parameters and len(operand_kinds) == 2 and operand_kinds[0][0] == "vector"
                    and operand_kinds[1] == index and result_kinds == [("field", operand_kinds[0][1])],
                    "checked vector read ports")
            return f".calculate (.boundedAt {text(operand_kinds[0][1])})"
        if contract == "control.require":
            require(not arguments and not parameters and operand_kinds == [boolean] and not result_kinds,
                    "local guard shape")
            return f".require {text(string_attribute(attrs, 'site'))}"
        if contract == "index.constant":
            require(not arguments and not operand_kinds and result_kinds == [index]
                    and len(parameters) == 1, "index constant shape")
            value = int(parameters[0][1])
            return f".calculate (.indexConstant {value})"
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
                    and operand_kinds[1][0] in ("boolean", "index", "field", "group", "vector", "data")
                    and operand_kinds[2] == ("indices", None)
                    and result_kinds == [("transcript", suite)]
                    and leaf == (operand_kinds[1][1] if operand_kinds[1][0] == "data"
                                 else [operand_kinds[1][0]] if operand_kinds[1][0] in ("boolean", "index")
                                 else list(operand_kinds[1])), "observed leaf type")
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
        if contract == "transcript.native.indexed.index":
            event = schema.origin_structure(parameters[0][1])
            require(event[0] == "query" and event[5] == "index", "index challenge origin method")
            (suite_arg,) = record(arguments, 1)
            suite = suite_arg[2]
            require(operand_kinds == [("transcript", suite), index, ("indices", None)]
                    and result_kinds == [index, ("transcript", suite)], "index challenge ports")
            require(operand_values is not None and type(operand_values[1]) is int
                    and 0 < operand_values[1] < 1 << 64, "index challenge constant bound")
            bound = operand_values[1]
            require(bound <= 1 << 63 and bound & (bound - 1) == 0,
                    "index challenge provider bound")
            return (f".indexChallenge {text(suite)} {operand_values[1]} "
                    f"{origin(one_parameter(attrs))}")
        if contract == "transcript.native.indexed.indices":
            event = schema.origin_structure(parameters[0][1])
            require(event[0] == "query" and event[5] == "indices", "block challenge origin method")
            (suite_arg,) = record(arguments, 1)
            suite = suite_arg[2]
            require(operand_kinds == [("transcript", suite), ("indices", None)]
                    and result_kinds == [("data", ["indices"]), ("transcript", suite)],
                    "block challenge ports")
            bound, count = (int(parameter[1]) for parameter in parameters[1:])
            return (f".blockChallenge {text(suite)} {bound} {count} "
                    f"{origin(schema.origin_hex(parameters[0]))}")
        if contract == "field.embed":
            require(not parameters, "field embedding attributes")
            require(len(operand_kinds) == 1 and operand_kinds[0][0] == "field"
                    and len(result_kinds) == 1 and result_kinds[0][0] == "field", "field embedding ports")
            extension, base = result_kinds[0][1], operand_kinds[0][1]
            require(arguments == [["domain", "Field", extension]], "field embedding binding")
            return f".calculate (.fieldEmbed {text(extension)} {text(base)})"
        return f".unsupported {text(name + ':' + contract)}"
    if name == "data.finite_fold":
        require(set(attrs) in ({"domain", "step"}, {"domain", "step", "predicate"}) and binding == [],
                "finite fold attributes")
        require(all(kind[0] in CAPTURED for kind in operand_kinds + result_kinds), "finite fold sorts")
        names = []
        for key in ("domain", "step", "predicate"):
            if key not in attrs:
                names.append("")
                continue
            kind, symbol = attrs[key]
            require(kind == "symbol" and isinstance(symbol, list) and len(symbol) == 1
                    and isinstance(symbol[0], str) and symbol[0], "finite fold symbol")
            names.append(symbol[0])
        return ".finiteFold " + " ".join(text(name) for name in names)
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
        require(not operand_kinds and len(result_kinds) == 1 and result_kinds[0][0] == "field",
                "field constant shape")
        kind, literal = attrs["value"]
        require(kind == "parameter" and literal[:3] ==
                ["field_literal", result_kinds[0][1], "natural"], "field constant parameter")
        return (f".calculate (.fieldConstant {text(result_kinds[0][1])} "
                f"{decimal(literal[3], catalogue.field_modulus(rows, result_kinds[0][1]))})")
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
    """The participant policy literal. The construction rule reads the authored
    and native profiles without gates; other profiles refuse."""
    decoded = native_policy.decode(value)
    require(not decoded.gates, "unsupported policy gates")
    require(decoded.profile in (native_policy.AUTHORED, native_policy.NATIVE)
            and decoded.producer != decoded.validator, "unsupported construction profile")
    return (f"⟨{text(decoded.entry)}, {text(decoded.producer)}, {text(decoded.validator)}, {decoded.acceptance}, "
            f"{text(decoded.suite)}, {seq(list(decoded.services))}, {seq(list(decoded.public))}, "
            f"{seq(list(decoded.draws), lambda pair: f'({text(pair[0])}, {text(pair[1])})')}, "
            f"{text(decoded.format)}, {text(decoded.construction)}⟩")


def service_port(value):
    name, owner, root, input_, contract = record(value, 5)
    for item in (name, owner, contract):
        text(item, printable_ascii=True)
    return (f"⟨{text(name)}, {text(owner)}, {decimal(root)}, "
            f"{decimal(input_)}, {text(contract)}⟩")


def local_service(attrs, binding, operands, result_kinds, retained, ports, places, kinds, rows, constants):
    require(set(attrs) == {"port", "method", "site"} and binding == [], "local service attributes")
    name, method, site = (string_attribute(attrs, key) for key in ("port", "method", "site"))
    require(name in ports, "undeclared local service port")
    port = ports[name]
    service = catalogue.service(rows, port[4])
    require(method in service[3], "local service method")
    if method == "draw":
        require(not operands and len(result_kinds) == 1 and result_kinds[0][0] == "field",
                "local draw shape")
        field = result_kinds[0][1]
        require(service[2] == field and port[4] == f"random.{field}/0", "local service nominal domain")
        request = f"Request.draw {text(field)}"
    elif method in ("index", "indices"):
        arity = 1 if method == "index" else 2
        expected = [("index", None)] if method == "index" else [("data", ["indices"])]
        require(len(operands) == arity and result_kinds == expected
                and all(kinds[reference] == ("index", None) for reference in operands),
                "local index service shape")
        values = [constants.get(reference) for reference in operands]
        require(all(type(value) is int and 0 < value < 1 << 64 for value in values),
                "local index service constant operands")
        constructor = "sampleIndex" if method == "index" else "sampleIndices"
        request = "Request." + constructor + " " + " ".join(str(value) for value in values)
    else:
        raise Refused("unsupported local service request")
    encoded, coordinates = record(retained, 2)
    template = origin(encoded)
    _, _, steps, _, event = lean_render.template(encoded)
    require(len(event) == 7 and event[0] == "query" and event[4] == port[4]
            and event[5] == method and event[6] == port[1], "local service occurrence")
    prefix = None
    for step in steps:
        if step[0] == "apply":
            application = step[2]
            prefix = application if prefix is None else f"apply_{len(prefix.encode('utf-8'))}_{prefix}_{application}"
    qualified = event[2] if prefix is None else f"apply_{len(prefix.encode('utf-8'))}_{prefix}_{event[2]}"
    require(site == qualified, "local service source site")
    mapped = references(coordinates, places, "local service coordinates")
    require(all(kinds[index] == ("index", None) for index in mapped), "local service coordinate sort")
    # Source/path/owner/root association is checked independently in Lean.
    require(isinstance(site, str) and site, "missing local service site")
    return (f".localService ({service_port(port)}) ({request}) "
            f"{template} {seq(mapped, nat)}")


# Sorts a loop may capture: immutable data, never a transcript.
CAPTURED = {"boolean", "index", "field", "vector", "group", "data"}


def references(values, places, what):
    """Map exported references to rendered ones; `places[r]` renders reference r."""
    require(isinstance(values, list) and all(type(o) is int and 0 <= o < len(places) for o in values),
            f"{what} reference out of range")
    return [places[o] for o in values]


def block(instructions, kinds, places, indent, rows, depth=0, ports=None, constants=None):
    """Render one block. `kinds` are the sorts of the rendered environment and
    `places` maps every exported reference in scope to its rendered reference.
    Return the rendered instructions, the final kinds and the final map."""
    require(depth <= 64 and isinstance(instructions, list) and len(instructions) <= 4096, "invalid block")
    rendered = []
    constants = dict(constants or {})
    for item in instructions:
        record(item)
        is_service = bool(item) and item[0] == "protocol.service_query"
        record(item, 7 if is_service else 6)
        name, attrs, binding, operands, results, regions = item[:6]
        schema.binding(binding)
        require(isinstance(name, str) and isinstance(regions, list), "operation name")
        mapped = references(operands, places, "operand")
        result_kinds = [sort(value)[1] for value in results]
        coordinate_result = (name == "exec.apply" and len(binding) > 0
                             and binding[0] in ("indices.empty", "indices.append"))
        if coordinate_result:
            require(results == [["apply", "indices", []]], "coordinate result shape")
            result_kinds = [("indices", None)]
        result_terms = "[.indices]" if coordinate_result else seq(results, lambda v: sort(v)[0])
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
                places + list(range(fresh, fresh + 1 + carried)) + captured, indent + "    ", rows, depth + 1,
                ports, constants)
            yielded = references(yielded, inner_places, "yielded")
            maximum = decimal(integer_attribute(attributes_, "maximum"), 1048577)
            require(maximum is not None, "loop maximum")
            term = f".loop {text(string_attribute(attributes_, 'site'))} {maximum}"
            body = "[]" if not inner else "[\n" + ",\n".join(inner) + "]"
            inputs = seq(arguments[:1 + carried], lambda v: sort(v)[0])
            region = f"⟨{inputs}, {body}, {seq(yielded, nat)}⟩"
            rendered.append(f"{indent}⟨{term}, {seq(mapped[:1 + carried], nat)}, {result_terms}, [{region}]⟩")
        elif name == "exec.compute":
            decoded = attributes(attrs)
            require(set(decoded) == {"callee", "site"} and binding == [] and len(regions) == 1,
                    "Math computation attributes")
            string_attribute(decoded, "site")
            kind, callee = decoded["callee"]
            require(kind == "symbol" and isinstance(callee, list) and len(callee) == 1
                    and isinstance(callee[0], str) and callee[0], "Math computation callee")
            arguments, nested, terminal = record(regions[0], 3)
            require(record(terminal, 2)[0] == "func.return", "Math computation terminal")
            argument_kinds = [sort(value)[1] for value in arguments]
            require(argument_kinds == [kinds[o] for o in mapped] and
                    all(kind[0] in CAPTURED for kind in argument_kinds + result_kinds),
                    "Math computation arguments")
            inner, inner_kinds, inner_places = block(
                nested, argument_kinds, list(range(len(arguments))), indent + "    ", rows, depth + 1, {})
            yielded = references(terminal[1], inner_places, "Math computation yielded")
            require([inner_kinds[o] for o in yielded] == result_kinds, "Math computation result sorts")
            body = "[]" if not inner else "[\n" + ",\n".join(inner) + "]"
            inputs = seq(arguments, lambda v: sort(v)[0])
            region = f"⟨{inputs}, {body}, {seq(yielded, nat)}⟩"
            rendered.append(f"{indent}⟨.mathCompute, {seq(mapped, nat)}, {result_terms}, [{region}]⟩")
        elif name == "exec.range":
            decoded = attributes(attrs)
            require(set(decoded) == {"site"} and binding == [], "local range attributes")
            string_attribute(decoded, "site")
            require(len(regions) == 1 and len(mapped) >= 2 + len(results), "local range shape")
            require([kinds[o] for o in mapped[:2]] == [("index", None)] * 2,
                    "local range bounds")
            carried = len(results)
            require([kinds[o] for o in mapped[2:2 + carried]] == result_kinds,
                    "local range initial state")
            capture_kinds = [kinds[o] for o in mapped[2 + carried:]]
            require(all(kind[0] in CAPTURED for kind in result_kinds + capture_kinds),
                    "local range sorts")
            arguments, nested, terminal, conditional = record(regions[0], 4)
            require(type(conditional) is bool and record(terminal, 2)[0] == "exec.complete",
                    "local range terminal")
            argument_kinds = [sort(value)[1] for value in arguments]
            require(argument_kinds == [("index", None)] + result_kinds + capture_kinds,
                    "local range arguments")
            inner, inner_kinds, inner_places = block(
                nested, argument_kinds, list(range(len(arguments))), indent + "    ", rows, depth + 1, {})
            yielded = references(terminal[1], inner_places, "local range yielded")
            require([inner_kinds[o] for o in yielded] ==
                    ([("boolean", None)] if conditional else []) + result_kinds,
                    "local range yield sorts")
            body = "[]" if not inner else "[\n" + ",\n".join(inner) + "]"
            inputs = seq(arguments, lambda v: sort(v)[0])
            region = f"⟨{inputs}, {body}, {seq(yielded, nat)}⟩"
            term = f".localRange {'true' if conditional else 'false'}"
            rendered.append(f"{indent}⟨{term}, {seq(mapped, nat)}, {result_terms}, [{region}]⟩")
        elif name == "exec.match":
            decoded = attributes(attrs)
            require(set(decoded) == {"alternatives", "site"} and binding == []
                    and len(regions) == 1 and mapped, "product projection shape")
            identity, constructor, fields = nominal_product(kinds[mapped[0]])
            require(decoded["alternatives"] == ("array", [["string", constructor]]),
                    "product projection alternative")
            string_attribute(decoded, "site")
            arguments, nested, terminal, alternative, payload = record(regions[0], 5)
            require(alternative == constructor and [data_type(value) for value in payload] == fields,
                    "product projection payload")
            capture_kinds = [kinds[reference] for reference in mapped[1:]]
            argument_kinds = [sort(value)[1] for value in arguments]
            require([data_descriptor(kind) for kind in argument_kinds]
                    == fields + [data_descriptor(kind) for kind in capture_kinds],
                    "product projection arguments")
            require(nested == [] and record(terminal, 2)[0] == "exec.complete",
                    "product projection body")
            yielded = references(terminal[1], list(range(len(arguments))), "product projection yield")
            require([argument_kinds[index] for index in yielded] == result_kinds,
                    "product projection result sorts")
            # A one-constructor, empty-body match only projects fields or aliases
            # captures. Expand typed projections and retain exact outer aliases.
            result_places = []
            for index, kind in zip(yielded, result_kinds):
                if index >= len(fields):
                    result_places.append(mapped[1 + index - len(fields)])
                    continue
                field = ".here"
                for _ in range(index):
                    field = f".there ({field})"
                calculation = (f".getProduct {product_parameters(identity, constructor, fields)} "
                               f"({render_type(fields[index])}) ({field})")
                result_places.append(len(kinds))
                rendered.append(f"{indent}⟨.calculate ({calculation}), [{mapped[0]}], "
                                f"[.data ({render_type(fields[index])})], []⟩")
                kinds = kinds + [kind]
            places = places + result_places
            continue
        elif name in ("data.branch", "exec.test"):
            decoded = attributes(attrs)
            local = name == "exec.test"
            if local:
                require(set(decoded) == {"site"}, "local branch attributes")
                string_attribute(decoded, "site")
            else:
                require(decoded == {"alternatives": ("array", [["string", "then"], ["string", "else"]])},
                        "Math branch attributes")
            require(binding == [] and len(regions) == 2 and len(mapped) >= 1, "closed branch shape")
            require(kinds[mapped[0]] == ("boolean", None), "Math branch selector")
            capture_kinds = [kinds[o] for o in mapped[1:]]
            require(all(kind[0] in CAPTURED for kind in capture_kinds)
                    and all(kind[0] in CAPTURED for kind in result_kinds), "Math branch sorts")
            arms = []
            for label, region in zip(("then", "else"), regions):
                arguments, nested, terminal, alternative, payload = record(region, 5)
                require(alternative == label and payload == [] and record(terminal, 2)[0] == ("exec.complete" if local else "data.yield"),
                        "Math branch arm")
                argument_kinds = [sort(value)[1] for value in arguments]
                require(argument_kinds == capture_kinds, "Math branch captures")
                inner, inner_kinds, inner_places = block(
                    nested, argument_kinds, list(range(len(arguments))), indent + "    ", rows, depth + 1, {})
                yielded = references(terminal[1], inner_places, "Math yielded")
                require([inner_kinds[o] for o in yielded] == result_kinds, "Math branch yield sorts")
                body = "[]" if not inner else "[\n" + ",\n".join(inner) + "]"
                inputs = seq(arguments, lambda v: sort(v)[0])
                arms.append(f"⟨{inputs}, {body}, {seq(yielded, nat)}⟩")
            branch = ".localBranch" if local else ".mathBranch"
            rendered.append(f"{indent}⟨{branch}, {seq(mapped, nat)}, {result_terms}, [{', '.join(arms)}]⟩")
        else:
            require(regions == [], f"unexpected operation region: {name}")
            if is_service:
                term = local_service(attributes(attrs), binding, mapped, result_kinds,
                                     item[6], ports or {}, places, kinds, rows, constants)
            else:
                term = operation(name, attributes(attrs), binding, [kinds[o] for o in mapped], result_kinds,
                                 rows, [constants.get(reference) for reference in mapped])
            rendered.append(f"{indent}⟨{term}, {seq(mapped, nat)}, {result_terms}, []⟩")
        if name == "exec.apply" and binding and binding[0] == "index.constant":
            constants[fresh] = int(attributes(attrs)["parameters"][1][0][1][1])
        if name == "data.index":
            constants[fresh] = int(integer_attribute(attributes(attrs), "value", signedness="unsigned"))
        kinds = kinds + result_kinds
        places = places + list(range(fresh, fresh + len(result_kinds)))
    return rendered, kinds, places


def render_declaration(data, namespace):
    (version, source, candidate, selected, symbol, inputs, outputs, instructions, returned, services,
     rows) = record(data, 11)
    require(version == FORMAT, "wrong participant export version")
    lean_render.namespace(namespace)
    policy_term = policy(selected)
    catalogue_term = catalogue.catalogue(rows)
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
    rendered, kinds, places = block(instructions, kinds, list(range(len(kinds))), "    ", rows, ports=ports)
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

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  {catalogue_term}

end {namespace}
'''


def render(data, namespace):
    return 'module\n\npublic import Zkc.Construction.Participant\n\n@[expose] public section\n\n/-! Constructor data from the retained `zkc.constructed-participant/0` export.\nRegenerate with bridges/construction/check.py --write; the Lean rule and its proofs are\nseparate. The bridge checks exact regeneration against the compiler. -/\n\n' + render_declaration(data, namespace)


if __name__ == "__main__":
    lean_render.render_main(render, __doc__, read=lambda path: schema.loads(path.read_bytes()))
