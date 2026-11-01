"""Strict neutral foundation data, separate from consumer interpretations.

The catalog supplies formation/signature data only. An interpreter must choose
its own profile and supply its own mathematics; decoding never installs either.
Executable program bytes deliberately do not use this module.
"""

from functools import lru_cache
import json
from pathlib import Path
import re

from bridges.common.lean_render import record, require

U64 = 1 << 64


def string(value, limit=1 << 20, nonempty=True):
    require(isinstance(value, str), "expected schema string")
    try:
        size = len(value.encode("utf-8"))
    except UnicodeError as error:
        raise ValueError("invalid schema Unicode") from error
    require(size <= limit and (bool(value) or not nonempty), "invalid schema string")
    return value



def variant_label(value):
    """The native variant-label grammar, before any constructor projection."""
    string(value, 128)
    require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.-]*", value) is not None,
            "invalid variant label")
    return value


def domain_identity(value, *, slot=False):
    """Nominal identities and resource slots have distinct owning grammars."""
    string(value, 128 if slot else 256)
    grammar = r"[A-Za-z][A-Za-z0-9_.-]*" if slot else r"[A-Za-z_][A-Za-z0-9_./-]*"
    require(re.fullmatch(grammar, value) is not None, "invalid domain identity")
    return value


def natural(value, limit=U64):
    require(isinstance(value, str) and len(value) <= 4096
            and re.fullmatch(r"0|[1-9][0-9]*", value) is not None
            and int(value) < limit, "invalid schema natural")
    return value


def compact(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), allow_nan=False)


def loads(encoded):
    """Read bounded JSON without duplicate members, nonfinite numbers or surrogates."""
    if isinstance(encoded, bytes):
        encoded = encoded.decode("utf-8")
    string(encoded, 64 << 20, nonempty=False)
    depth, quoted, escaped = 0, False, False
    for char in encoded:
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char in "[{":
            depth += 1
            require(depth <= 64, "JSON depth limit")
        elif char in "]}":
            depth -= 1

    def object_(pairs):
        value = {}
        for key, child in pairs:
            require(key not in value, "duplicate JSON member")
            value[key] = child
        return value

    def constant(_):
        raise ValueError("invalid JSON constant")

    value = json.loads(encoded, object_pairs_hook=object_, parse_constant=constant)
    json_value(value)
    return value


class Budget:
    """Count expanded work, including repeated in-memory subtrees."""

    def __init__(self, nodes=200000, bytes_=64 << 20):
        self.nodes, self.bytes = nodes, bytes_

    def visit(self, value, depth):
        require(depth <= 64, "schema depth limit")
        self.nodes -= 1
        require(self.nodes >= 0, "schema node limit")
        if isinstance(value, str):
            string(value, nonempty=False)
            self.bytes -= len(value.encode("utf-8"))
        else:
            self.bytes -= 8
        require(self.bytes >= 0, "schema metadata limit")


@lru_cache(maxsize=1)
def declarations():
    """Read the owning neutral inventory, never a generated interpretation."""
    path = Path(__file__).resolve().parents[3] / "common/catalog/declarations.json"
    value = json.loads(path.read_text(encoding="utf-8"))
    require(value["format"] == "zkc.contract-declarations/0", "catalog format")
    return value


def identity(value, depth=0, budget=None):
    budget = budget or Budget()
    budget.visit(value, depth)
    tag, payload = record(value, 2)
    if tag == "atom":
        budget.visit(string(payload), depth + 1)
    elif tag == "tuple":
        require(isinstance(payload, list), "invalid identity tuple")
        for child in payload:
            identity(child, depth + 1, budget)
    else:
        raise ValueError("unknown identity tag")
    return value


def interpreted_identity(value):
    """Injective JSON string/array encoding used by the formal nominal type.

    Wire tags are validated first. Distinct atom/tuple constructors remain
    distinct JSON kinds, without normalizing Unicode or losing phantom actuals.
    """
    identity(value)

    def lower(node):
        return node[1] if node[0] == "atom" else [lower(child) for child in node[1]]

    return compact(lower(value))


def argument(value, depth=0, budget=None, mask=False):
    budget = budget or Budget()
    budget.visit(value, depth)
    record(value)
    require(bool(value), "empty static argument")
    if value[0] == "domain":
        _, sort, name = record(value, 3)
        require(sort in declarations()["sorts"], "unknown domain sort")
        budget.visit(domain_identity(name, slot=sort == "Slot"), depth + 1)
    elif value[0] == "type":
        _, child = record(value, 2)
        logical_type(child, depth + 1, budget)
    elif value[0] == "nat":
        _, number = record(value, 2)
        budget.visit(natural(number), depth + 1)
    elif value[0] == "mask" and mask:
        _, bits = record(value, 2)
        require(isinstance(bits, list) and len(bits) <= 1023
                and all(type(bit) is bool for bit in bits), "invalid numerical mask")
        for bit in bits:
            budget.visit(bit, depth + 1)
    else:
        raise ValueError("unknown static argument tag")
    return value


def kind_matches(value, kind):
    return (value[0] == {"Domain": "domain", "Type": "type", "Nat": "nat"}[kind["kind"]]
            and (value[0] != "domain" or value[1] == kind["sort"]))


def logical_type(value, depth=0, budget=None):
    budget = budget or Budget()
    budget.visit(value, depth)
    record(value)
    require(bool(value), "empty logical type")
    tag = value[0]
    if tag == "apply":
        _, name, arguments = record(value, 3)
        constructors = {row["name"]: row for row in declarations()["types"]}
        require(isinstance(name, str) and name in constructors, "unknown type constructor")
        kinds = constructors[name]["parameters"]
        require(isinstance(arguments, list) and len(arguments) == len(kinds), "type argument arity")
        for actual, kind in zip(arguments, kinds):
            argument(actual, depth + 1, budget)
            require(kind_matches(actual, kind), "type argument kind")
    elif tag == "variant":
        _, nominal, alternatives = record(value, 3)
        identity(nominal, depth + 1, budget)
        require(isinstance(alternatives, list) and 0 < len(alternatives) <= 512,
                "invalid variant alternatives")
        names = set()
        for alternative in alternatives:
            name, payloads = record(alternative, 2)
            budget.visit(variant_label(name), depth + 1)
            require(name not in names and isinstance(payloads, list) and len(payloads) <= 512,
                    "duplicate alternative or invalid payloads")
            names.add(name)
            for child in payloads:
                logical_type(child, depth + 1, budget)
    elif tag in ("oracle", "oracle_sequence"):
        record(value, 3 if tag == "oracle" else 4)
        oracle_kind(value[1:3], depth + 1, budget)
        if tag == "oracle_sequence":
            budget.visit(natural(value[3]), depth + 1)
    elif tag == "service":
        _, contract = record(value, 2)
        budget.visit(string(contract), depth + 1)
    else:
        raise ValueError("unknown logical type tag")
    return value


def oracle_kind(value, depth=0, budget=None):
    budget = budget or Budget()
    budget.visit(value, depth)
    name, arguments = record(value, 2)
    require(name == "table" and isinstance(arguments, list) and len(arguments) in (1, 2),
            "unsupported oracle kind")
    for actual in arguments:
        argument(actual, depth + 1, budget)
    require(arguments[0][0] == "type" and (len(arguments) == 1 or arguments[1][0] == "nat"),
            "oracle argument kind")
    return value


def is_handle(value):
    logical_type(value)
    if value[0] in ("oracle", "oracle_sequence", "service"):
        return True
    if value[0] == "variant":
        return any(is_handle(child) for _, payloads in value[2] for child in payloads)
    row = next(row for row in declarations()["types"] if row["name"] == value[1])
    return row["custody"] == "Affine" or any(
        is_handle(actual[1]) for actual in value[2] if actual[0] == "type")


def interpreted_type(value, payload=False):
    """Project only the existing formal vocabulary after neutral validation."""
    logical_type(value)
    if payload:
        require(not is_handle(value), "logical handle is not an ordinary payload")
    tag = value[0]
    if tag == "service":
        return value
    if tag in ("oracle", "oracle_sequence"):
        kind = [value[1], [["type", interpreted_type(value[2][0][1])], *value[2][1:]]]
        return [tag, kind, *value[3:]]
    if tag == "variant":
        require(len(value[2]) == 1, "unsupported multi-alternative formal type")
        name, fields = value[2][0]
        return ["product", interpreted_identity(value[1]), name,
                [interpreted_type(child, payload) for child in fields]]
    _, name, arguments = value
    if name in ("bool", "index", "indices"):
        return [name]
    if name in ("field", "vector", "group", "groups"):
        return [name, arguments[0][2]]
    if name == "sequence":
        return [name, interpreted_type(arguments[0][1], payload)]
    raise ValueError("logical type has no installed formal interpretation")


def json_value(value, depth=0, budget=None):
    """Bound opaque structured expression/origin data, without granting meaning."""
    budget = budget or Budget()
    budget.visit(value, depth)
    require(value is None or type(value) in (bool, int, str, list, dict), "invalid structured JSON")
    if isinstance(value, list):
        for child in value:
            json_value(child, depth + 1, budget)
    if isinstance(value, dict):
        for key, child in value.items():
            budget.visit(string(key), depth + 1)
            json_value(child, depth + 1, budget)


def parameter(value, depth=0, budget=None):
    budget = budget or Budget()
    budget.visit(value, depth)
    record(value)
    require(bool(value), "empty parameter")
    tag = value[0]
    if tag == "natural":
        _, number = record(value, 2)
        budget.visit(natural(number), depth + 1)
    elif tag == "field_literal":
        _, domain, encoding, digits = record(value, 4)
        budget.visit(string(domain), depth + 1)
        budget.visit(string(digits, 4096), depth + 1)
        require(encoding in ("natural", "bits"), "field literal encoding")
        if encoding == "natural":
            natural(digits, 1 << 16384)
        else:
            require(re.fullmatch(r"0x[1-9a-f][0-9a-f]*", digits) is not None
                    and int(digits, 16) > 1, "noncanonical field bits")
    elif tag == "asset":
        _, format_, digest = record(value, 3)
        budget.visit(string(format_), depth + 1)
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                "invalid asset digest")
        budget.visit(digest, depth + 1)
    elif tag in ("expression", "origin"):
        _, structured = record(value, 2)
        require(isinstance(structured, (list, dict)), "parameter requires structured data")
        json_value(structured, depth + 1, budget)
        if tag == "origin":
            origin_structure(structured)
        else:
            expression_structure(structured)
    else:
        raise ValueError("unknown parameter tag")
    return value


def origin_structure(value):
    version, entry, steps, coordinates, event = record(value, 5)
    require(version == "zkc.native-origin-template/0" and coordinates == [], "invalid origin template")

    def identifier(name):
        require(isinstance(name, str) and 0 < len(name) <= 128
                and all(33 <= ord(char) <= 126 for char in name), "invalid origin identifier")

    identifier(entry)
    require(isinstance(steps, list) and len(steps) <= 64, "invalid origin steps")
    for step in steps:
        kind, protocol, site = record(step, 3)
        require(kind in ("apply", "repeat"), "invalid origin step kind")
        identifier(protocol)
        identifier(site)
    record(event)
    require(bool(event), "empty origin event")
    sizes = {"query": 7, "message": 6, "start": 3}
    require(isinstance(event[0], str) and event[0] in sizes, "unknown origin event")
    record(event, sizes[event[0]])
    for name in event[1:]:
        identifier(name)
    if event[0] == "query":
        require(event[3].startswith("input_"), "invalid origin input")
        natural(event[3][6:])
    return event


def expression_structure(value):
    """Read the ring arena's shape; domain/literal/embedding laws stay separate."""
    version, inputs, nodes, outputs = record(value, 4)
    require(version == "zkc.ring/0" and isinstance(inputs, list) and len(inputs) <= 65536
            and isinstance(nodes, list) and len(nodes) <= 65536
            and isinstance(outputs, list) and len(outputs) <= 4096, "invalid ring arena")
    require(len(compact(value).encode("utf-8")) <= 8 << 20, "ring byte limit")
    for field in inputs:
        string(field)
    depths, fields = [], []

    def reference(index, count):
        require(type(index) is int and 0 <= index < count, "invalid ring reference")
        return index

    for position, node in enumerate(nodes):
        record(node)
        require(bool(node), "empty ring node")
        tag = node[0]
        if tag == "constant":
            _, field, number = record(node, 3)
            string(field)
            require(isinstance(number, str) and len(number) <= 256, "ring literal limit")
            natural(number, 1 << 1024)
            depth = 1
        elif tag == "input":
            _, index = record(node, 2)
            field, depth = inputs[reference(index, len(inputs))], 1
        elif tag in ("add", "mul"):
            _, left, right = record(node, 3)
            reference(left, position)
            reference(right, position)
            require(fields[left] == fields[right], "ring field mismatch")
            field, depth = fields[left], 1 + max(depths[left], depths[right])
        elif tag in ("neg", "embed"):
            record(node, 2 if tag == "neg" else 3)
            index = reference(node[-1], position)
            field, depth = fields[index], depths[index] + 1
            if tag == "embed":
                field = string(node[1])
        else:
            raise ValueError("unknown ring node")
        require(depth <= 1024, "ring depth limit")
        fields.append(field)
        depths.append(depth)
    for output in outputs:
        reference(output, len(nodes))
    return value


def validate_parameters(values, specification, field=None, modulus=None):
    """Check the declared parameter family without assigning an operation law."""
    require(isinstance(values, list) and len(values) <= 1024, "invalid parameters")
    maximum = specification["maximum"]
    require(len(values) >= specification["minimum"]
            and (maximum is None or len(values) <= maximum), "parameter count mismatch")
    budget = Budget()
    for value in values:
        parameter(value, budget=budget)
    validator = specification["validator"]
    if validator == "None":
        require(values == [], "unexpected parameters")
    elif validator in ("Natural", "Extent", "MatrixShape", "MatrixVector", "GatherIndices", "ScatterIndices"):
        require(all(value[0] == "natural" for value in values), "expected natural parameters")
        limit = {"Extent": 1048577, "MatrixShape": 65537, "MatrixVector": 1048577,
                 "GatherIndices": 1048577}.get(validator, U64)
        for value in values:
            natural(value[1], limit)
        if validator == "MatrixVector":
            require(len(values) == 3 and int(values[2][1]) <= 1, "matrix vector orientation")
    elif validator in ("FieldLiteral", "FieldLiterals"):
        require(field is not None and modulus is not None, "field parameter needs independent domain admission")
        require(all(value[0] == "field_literal" and value[1] == field and value[2] == "natural"
                    and int(value[3]) < modulus for value in values), "field literal domain or range")
    elif validator in ("AssetIdentity", "MatrixIdentity"):
        format_ = "zkc.matrix/0" if validator == "MatrixIdentity" else specification["assetFormat"]
        require(len(values) == 1 and values[0][0] == "asset" and values[0][1] == format_, "asset format mismatch")
    elif validator == "NativeOrigin":
        require(len(values) == 1 and values[0][0] == "origin", "expected native origin parameter")
        origin_hex(values[0])
    elif validator == "NumericalExpression":
        raise ValueError("numerical parameter needs installed expression interpretation")
    else:
        raise ValueError("unknown parameter validator")
    return values


def origin_hex(value):
    """Boundary conversion to the existing canonical occurrence codec."""
    from bridges.common.lean_render import encode_tree, origin
    parameter(value)
    require(value[0] == "origin", "expected origin parameter")

    def tree(node):
        require(isinstance(node, (str, list)), "invalid origin tree")
        if isinstance(node, list):
            for child in node:
                tree(child)
    tree(value[1])
    encoded = encode_tree(value[1]).hex()
    origin(encoded)
    return encoded


def attribute(value, depth=0, budget=None):
    budget = budget or Budget()
    budget.visit(value, depth)
    record(value)
    require(bool(value), "empty attribute")
    tag = value[0]
    if tag == "integer":
        _, signedness, width, number = record(value, 4)
        require(signedness in ("signless", "signed", "unsigned"), "invalid integer signedness")
        bits = int(natural(width, 4097))
        require(bits > 0 and isinstance(number, str) and len(number) <= 1235
                and re.fullmatch(r"0|-?[1-9][0-9]*", number) is not None, "invalid integer attribute")
        number_ = int(number)
        require(-(1 << (bits - 1)) <= number_ < (1 << (bits - 1)) if signedness == "signed"
                else 0 <= number_ < (1 << bits), "integer attribute overflow")
        budget.visit(number, depth + 1)
    else:
        _, payload = record(value, 2)
        if tag == "string":
            budget.visit(string(payload, nonempty=False), depth + 1)
        elif tag == "bool":
            require(type(payload) is bool, "invalid Boolean attribute")
        elif tag == "symbol":
            require(isinstance(payload, list) and bool(payload), "invalid symbol components")
            for part in payload:
                budget.visit(string(part), depth + 1)
        elif tag == "type":
            logical_type(payload, depth + 1, budget)
        elif tag == "parameter":
            parameter(payload, depth + 1, budget)
        elif tag == "array":
            require(isinstance(payload, list), "invalid attribute array")
            for child in payload:
                attribute(child, depth + 1, budget)
        elif tag == "dictionary":
            attributes(payload, depth + 1, budget)
        else:
            raise ValueError("unknown attribute tag")
    return value


def attributes(value, depth=0, budget=None):
    budget = budget or Budget()
    require(isinstance(value, list), "invalid attribute dictionary")
    previous = None
    result = {}
    for pair in value:
        name, child = record(pair, 2)
        budget.visit(string(name), depth + 1)
        require(previous is None or previous < name, "attributes must be unique and sorted")
        previous = name
        attribute(child, depth + 1, budget)
        result[name] = child
    return result


def binding(value, source=False):
    """Decode complete ports and kinded actuals; do not trust supplied ports."""
    if not source and value == []:
        return value
    record(value, 7 if source else 5)
    if source:
        require(value[0] == "binding", "invalid source binding")
        string(value[1], 256)
        value = value[2:]
    contract, arguments, implementation, inputs, outputs = value
    string(contract, 512)
    string(implementation, 512, nonempty=False)
    require(isinstance(arguments, list) and len(arguments) <= 1024, "invalid binding arguments")
    budget = Budget()
    for actual in arguments:
        argument(actual, budget=budget, mask=True)
    for ports in (inputs, outputs):
        require(isinstance(ports, list) and len(ports) <= 1024, "invalid binding ports")
        for port in ports:
            logical_type(port, budget=budget)
    return value


def resolve_signature(value, project=None, allowed=None):
    """Rederive fixed ports from declarations and independently supplied members.

    A member resolver is mandatory when the declaration projects a domain.
    The caller separately checks capabilities and semantic profile membership.
    """
    contract, arguments, _, inputs, outputs = binding(value)
    require(allowed is None or contract in allowed, "binding outside consumer profile")
    operations = {row["name"]: row for row in declarations()["operations"]}
    require(contract in operations, "unknown binding contract")
    op = operations[contract]
    require(op["signature"]["kind"] == "fixed", "unsupported signature family")
    values, position = [], 0
    for term in op["scope"]:
        tag = term["kind"]
        if tag == "root":
            require(position < len(arguments) and kind_matches(arguments[position], term["parameter"]),
                    "binding static argument kind")
            values.append(arguments[position])
            position += 1
        elif tag == "project":
            require(project is not None, "binding needs associated domain resolver")
            actual = project(values[term["parent"]], term["member"])
            argument(actual)
            values.append(actual)
        elif tag == "natural":
            values.append(["nat", str(term["value"])])
        elif tag == "apply":
            values.append(["type", ["apply", term["constructor"], [values[i] for i in term["arguments"]]]])
        else:
            raise ValueError("unknown signature scope term")
    require(position == len(arguments), "binding static argument arity")

    def port(item):
        if "term" in item:
            actual = values[item["term"]]
            require(actual[0] == "type", "signature port must have Type kind")
            return actual[1]
        return ["apply", item["constructor"], [values[i] for i in item["arguments"]]]

    expected = [[port(item) for item in op["signature"][side]] for side in ("inputs", "outputs")]
    for side in expected:
        for item in side:
            logical_type(item)
    require(expected == [inputs, outputs], "binding logical signature mismatch")
    return op, values


def type_inventory(values):
    require(isinstance(values, list) and len(values) <= 4096, "invalid type inventory")
    budget, seen = Budget(), set()
    for value in values:
        logical_type(value, budget=budget)
        key = compact(value)
        require(key not in seen, "duplicate logical type")
        seen.add(key)
    return values


class RealizationTypes:
    """Realization's unsigned JSON references and exact first-use discipline.

    The owning realization reader visits all references in wire traversal order,
    then calls finish. Merely decoding this table never authorizes a payload.
    """

    def __init__(self, values):
        self.values = type_inventory(values)
        self.seen = set()
        self.budget = Budget()

    def reference(self, index, payload=False):
        require(type(index) is int and 0 <= index < len(self.values), "invalid realization type reference")
        if index not in self.seen:
            require(index == len(self.seen), "realization type first-use order")
            self.seen.add(index)
        value = self.values[index]
        logical_type(value, budget=self.budget)
        if payload:
            require(not is_handle(value), "logical handle is not an ordinary payload")
        return value

    def finish(self):
        require(len(self.seen) == len(self.values), "unused realization type")
