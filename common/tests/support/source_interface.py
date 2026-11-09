"""The strict reader of `zkc.language-interface/0` for native source-identity tests.

The [Entry interface contract](../../../docs/spec/formats/entry.md) fixes the
exact JSON members of the interface and of every record in it: unknown tags,
missing members and extra members refuse, and a required-nullable member is
present with JSON null. This reader checks those member sets and the JSON kind
of every member recursively, the conditional oracle members, the selected
protocol, contiguous port indices, and the ordering of public selections. It
returns the decoded value unchanged.

It does not repeat the native reader's coverage, schema digest, component and
source-correspondence checks; a bridge that relies on an association reads it
from the members decoded here (for example a port's `native` array and its
`components`), never from a position or a name.
"""

import json
import re

from source_transport import Refused, require

FORMAT = "zkc.language-interface/0"
PROOF_FORMATS = ("zkc.framed/0", "raw.bytes/0")
KINDS = ("boolean", "index", "field", "group", "unit", "tuple", "array", "record", "logical_record",
         "variant", "associated", "builtin", "oracle", "oracle_sequence")
HANDLES = ("oracle", "oracle_sequence")
FACETS = ("data", "oracle_data", "oracle_anchor", "custody")
CLAUSE_KINDS = ("target", "input", "output", "continuation")
PURPOSES = ("parameter", "statement", "witness")
DEFINITIONS = {"formula": ("function",), "opaque": (), "r1cs": ("asset",), "air": ("asset",),
               "bundle": ("asset",)}
UNSIGNED = re.compile(r"0|[1-9][0-9]{0,19}")
U32 = (1 << 32) - 1


def loads(text):
    """Decode interface text, refusing duplicate keys and non-finite numbers."""
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"interface: duplicate member {key!r}")
            result[key] = value
        return result

    def invalid(value):
        raise Refused(f"interface: non-finite number {value}")

    try:
        value = json.loads(text, object_pairs_hook=unique, parse_constant=invalid)
    except (ValueError, TypeError) as error:
        if isinstance(error, Refused):
            raise
        raise Refused(f"interface: malformed JSON: {error}") from error
    return decode(value)


def decode(value):
    """Check `value` against the exact interface shape and return it."""
    members(value, "interface", ("format", "capture", "original", "toolchain", "entry", "protocol",
                                 "protocols", "relations", "job", "setups"))
    require(value["format"] == FORMAT, f"interface: expected format {FORMAT}")
    for name in ("capture", "original", "toolchain", "entry", "protocol"):
        string(value[name], f"interface.{name}")
    protocols = array(value["protocols"], "interface.protocols", protocol)
    symbols = [item["symbol"] for item in protocols]
    require(len(set(symbols)) == len(symbols), "interface.protocols: duplicate protocol symbol")
    require(symbols.count(value["protocol"]) == 1, "interface.protocol: selects no retained protocol")
    relations = array(value["relations"], "interface.relations", relation)
    names = [item["symbol"] for item in relations]
    require(len(set(names)) == len(names), "interface.relations: duplicate relation symbol")
    job(value["job"], "interface.job")
    array(value["setups"], "interface.setups", setup)
    return value


def selected_protocol(value):
    """The protocol record the interface selects."""
    (found,) = [item for item in value["protocols"] if item["symbol"] == value["protocol"]]
    return found


# ---------------------------------------------------------------------------
# Member sets and JSON kinds

def members(value, where, required, optional=()):
    require(isinstance(value, dict), f"{where}: expected an object")
    missing = sorted(set(required) - set(value))
    extra = sorted(set(value) - set(required) - set(optional))
    require(not missing, f"{where}: missing members {', '.join(missing)}")
    require(not extra, f"{where}: unexpected members {', '.join(extra)}")
    return value


def string(value, where):
    require(isinstance(value, str), f"{where}: expected a string")
    return value


def natural(value, where, limit=U32):
    require(type(value) is int and 0 <= value <= limit, f"{where}: expected a natural number")
    return value


def boolean(value, where):
    require(type(value) is bool, f"{where}: expected a Boolean")
    return value


def unsigned(value, where):
    """A canonical unsigned 64-bit decimal string."""
    require(isinstance(value, str) and UNSIGNED.fullmatch(value) is not None and int(value) < 1 << 64,
            f"{where}: expected a canonical unsigned decimal string")
    return value


def one_of(value, choices, where):
    require(isinstance(value, str) and value in choices, f"{where}: expected one of {', '.join(choices)}")
    return value


def nullable(value, where, read):
    return None if value is None else read(value, where)


def array(value, where, read):
    require(isinstance(value, list), f"{where}: expected an array")
    return [read(item, f"{where}[{index}]") for index, item in enumerate(value)]


def naturals(value, where):
    return array(value, where, natural)


def strings(value, where):
    return array(value, where, string)


def tagged(value, where, variants):
    """An object whose `kind` selects its exact remaining members."""
    require(isinstance(value, dict), f"{where}: expected an object")
    kind = one_of(value.get("kind"), tuple(variants), where + ".kind")
    members(value, where, ("kind", *variants[kind]))
    return kind


# ---------------------------------------------------------------------------
# Records

def setup(value, where):
    members(value, where, ("name", "inputs"))
    string(value["name"], where + ".name")
    array(value["inputs"], where + ".inputs", lambda item, at: (
        members(item, at, ("port", "path")), natural(item["port"], at + ".port"),
        naturals(item["path"], at + ".path")))


def job(value, where):
    kind = tagged(value, where, {
        "run": (),
        "proof": ("prover", "verifier", "public", "acceptance", "completion", "target", "construction",
                  "gates"),
    })
    if kind == "run":
        return
    string(value["prover"], where + ".prover")
    string(value["verifier"], where + ".verifier")
    array(value["public"], where + ".public", lambda item, at: (
        members(item, at, ("port", "path", "role")), natural(item["port"], at + ".port"),
        naturals(item["path"], at + ".path"), string(item["role"], at + ".role")))
    keys = [(item["port"], item["path"]) for item in value["public"]]
    for (port, path), (next_port, next_path) in zip(keys, keys[1:]):
        require((port, path) < (next_port, next_path),
                f"{where}.public: selections are not strictly ordered by port then path")
        require(port != next_port or next_path[:len(path)] != path,
                f"{where}.public: a selection overlaps its ancestor")
    selector(value["acceptance"], where + ".acceptance")
    nullable(value["completion"], where + ".completion", selector)
    nullable(value["target"], where + ".target", string)
    construction(value["construction"], where + ".construction")
    array(value["gates"], where + ".gates", gate)


def gate(value, where):
    members(value, where, ("path", "bits"))
    path = strings(value["path"], where + ".path")
    require(path and all(path), f"{where}.path: expected a nonempty path of nonempty identifiers")
    natural(value["bits"], where + ".bits", 64)


def construction(value, where):
    kind = tagged(value, where, {
        "authored": ("format",),
        "fiat_shamir": ("format", "suite", "services"),
        "derived": ("format", "suite", "services", "symbol"),
    })
    one_of(value["format"], PROOF_FORMATS, where + ".format")
    if kind == "authored":
        return
    services = naturals(value["services"], where + ".services")
    require(services and services == sorted(set(services)),
            f"{where}.services: expected a nonempty strictly increasing array")
    if kind == "fiat_shamir":
        string(value["suite"], where + ".suite")
        require(len(services) == 1, f"{where}.services: a native construction selects one service")
    else:
        nullable(value["suite"], where + ".suite", string)
        string(value["symbol"], where + ".symbol")


def protocol(value, where):
    members(value, where, ("symbol", "roles", "inputs", "outputs", "services", "clauses",
                           "common_input_requirements"))
    string(value["symbol"], where + ".symbol")
    strings(value["roles"], where + ".roles")
    for direction in ("inputs", "outputs"):
        ports = array(value[direction], f"{where}.{direction}", port)
        require([item["index"] for item in ports] == list(range(len(ports))),
                f"{where}.{direction}: port indices are not contiguous")
    array(value["services"], where + ".services", service)
    array(value["clauses"], where + ".clauses", clause)
    array(value["common_input_requirements"], where + ".common_input_requirements", requirement)
    return value


def port(value, where):
    require(isinstance(value, dict), f"{where}: expected an object")
    handle = schema(value.get("schema"), where + ".schema")["kind"] in HANDLES
    members(value, where, ("name", "type", "index", "native", "schema", "placement", "components",
                           *(("maximum_rows",) if handle else ())))
    string(value["name"], where + ".name")
    string(value["type"], where + ".type")
    natural(value["index"], where + ".index")
    naturals(value["native"], where + ".native")
    placement(value["placement"], where + ".placement")
    array(value["components"], where + ".components", component)
    if handle:
        # Null exactly for a kind that fixes its row count.
        if sized(value["schema"]):
            require(value["maximum_rows"] is None, f"{where}.maximum_rows: expected null for a sized kind")
        else:
            unsigned(value["maximum_rows"], where + ".maximum_rows")
    return value


def service(value, where):
    members(value, where, ("name", "contract", "owner", "native"))
    for name in ("name", "contract", "owner"):
        string(value[name], f"{where}.{name}")
    natural(value["native"], where + ".native")


def selector(value, where):
    members(value, where, ("direction", "port", "role", "path"))
    one_of(value["direction"], ("input", "output"), where + ".direction")
    natural(value["port"], where + ".port")
    nullable(value["role"], where + ".role", string)
    naturals(value["path"], where + ".path")
    return value


def application(value, where):
    members(value, where, ("relation", "operands"))
    string(value["relation"], where + ".relation")
    array(value["operands"], where + ".operands", selector)
    return value


def clause(value, where):
    members(value, where, ("name", "kind", "subject", "residual", "decision"))
    string(value["name"], where + ".name")
    one_of(value["kind"], CLAUSE_KINDS, where + ".kind")
    application(value["subject"], where + ".subject")
    nullable(value["residual"], where + ".residual", application)
    nullable(value["decision"], where + ".decision", selector)


def requirement(value, where):
    members(value, where, ("components", "observation"))
    array(value["components"], where + ".components", lambda item, at: (
        members(item, at, ("input", "role", "path")), natural(item["input"], at + ".input"),
        string(item["role"], at + ".role"),
        array(item["path"], at + ".path", lambda step, place: (
            members(step, place, ("kind", "index")),
            one_of(step["kind"], ("field", "alternative", "payload"), place + ".kind"),
            natural(step["index"], place + ".index")))))
    tagged(value["observation"], where + ".observation", {"value": (), "tag": (), "extent": ("axis",)})
    if value["observation"]["kind"] == "extent":
        natural(value["observation"]["axis"], where + ".observation.axis")


def schema(value, where):
    require(isinstance(value, dict), f"{where}: expected an object")
    kind = one_of(value.get("kind"), KINDS, where + ".kind")
    members(value, where, ("kind", "identity", "generated", "type", "custody", "sealed", "constructible",
                           "permissions", "roles", "element", "leaves", "fields", "alternatives",
                           *(("oracle", "data_schema") if kind in HANDLES else ()),
                           *(("maximum",) if kind == "oracle_sequence" else ())))
    string(value["identity"], where + ".identity")
    nullable(value["generated"], where + ".generated", string)
    string(value["type"], where + ".type")
    natural(value["custody"], where + ".custody")
    boolean(value["sealed"], where + ".sealed")
    boolean(value["constructible"], where + ".constructible")
    array(value["permissions"], where + ".permissions",
          lambda item, at: one_of(item, ("Copy", "Drop"), at))
    strings(value["roles"], where + ".roles")
    nullable(value["element"], where + ".element", schema)
    strings(value["leaves"], where + ".leaves")
    array(value["fields"], where + ".fields", field)
    array(value["alternatives"], where + ".alternatives", lambda item, at: (
        members(item, at, ("name", "fields")), string(item["name"], at + ".name"),
        array(item["fields"], at + ".fields", field)))
    if kind in HANDLES:
        oracle(value["oracle"], where + ".oracle")
        schema(value["data_schema"], where + ".data_schema")
    if kind == "oracle_sequence":
        unsigned(value["maximum"], where + ".maximum")
    return value


def oracle(value, where):
    members(value, where, ("kind", "arguments"))
    string(value["kind"], where + ".kind")

    def argument(item, at):
        require(isinstance(item, list) and len(item) == 2 and item[0] in ("type", "nat"),
                f"{at}: expected a typed oracle argument pair")
        if item[0] == "type":
            string(item[1], at + "[1]")
        else:
            unsigned(item[1], at + "[1]")
    array(value["arguments"], where + ".arguments", argument)
    return value


def sized(value):
    """Whether a handle schema's kind fixes its row count."""
    return any(item[0] == "nat" for item in value["oracle"]["arguments"])


def field(value, where):
    require(isinstance(value, dict), f"{where}: expected an object")
    # Validate the child first: whether `maximum_rows` belongs to the field
    # depends on its kind.
    child = schema(value.get("schema"), where + ".schema")
    unsized = child["kind"] in HANDLES and not sized(child)
    members(value, where, ("name", "offset", "public", "placement", "schema",
                           *(("maximum_rows",) if unsized else ())))
    string(value["name"], where + ".name")
    natural(value["offset"], where + ".offset")
    boolean(value["public"], where + ".public")
    nullable(value["placement"], where + ".placement", placement)
    if unsized:
        unsigned(value["maximum_rows"], where + ".maximum_rows")
    return value


def placement(value, where):
    kind = tagged(value, where, {"data": ("roles",), "oracle": ("holder", "receivers"),
                                 "product": ("instance", "arguments", "fields")})
    if kind == "data":
        naturals(value["roles"], where + ".roles")
    elif kind == "oracle":
        natural(value["holder"], where + ".holder")
        naturals(value["receivers"], where + ".receivers")
    else:
        string(value["instance"], where + ".instance")
        naturals(value["arguments"], where + ".arguments")
        array(value["fields"], where + ".fields", placement)
    return value


def component(value, where):
    members(value, where, ("path", "leaf", "role", "facet", "native"))
    naturals(value["path"], where + ".path")
    natural(value["leaf"], where + ".leaf")
    natural(value["role"], where + ".role")
    one_of(value["facet"], FACETS, where + ".facet")
    natural(value["native"], where + ".native")
    return value


def relation(value, where):
    members(value, where, ("symbol", "static_arguments", "inputs", "definition"))
    string(value["symbol"], where + ".symbol")
    require(isinstance(value["static_arguments"], list), f"{where}.static_arguments: expected an array")
    array(value["inputs"], where + ".inputs", lambda item, at: (
        members(item, at, ("name", "purpose", "native", "schema")), string(item["name"], at + ".name"),
        one_of(item["purpose"], PURPOSES, at + ".purpose"), naturals(item["native"], at + ".native"),
        schema(item["schema"], at + ".schema")))
    kind = tagged(value["definition"], where + ".definition", DEFINITIONS)
    for name in DEFINITIONS[kind]:
        string(value["definition"][name], f"{where}.definition.{name}")
    return value
