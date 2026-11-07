"""The catalogue slot shared by the structured-source and constructed-participant exports.

An export carries the native rows of the identities it uses, closed under
associated members, and the rows of the random services it uses:

    catalogue := [nominal-rows, service-rows]
    ["nominal", identity, sort, [[member, identity]...], [capability...], modulus | null]
    ["service", contract, sampled-field, [method...]]

The renderers read associated members and capability facts from these rows,
never from a restated table. The rows are producer data: Lean admission checks
them against its own catalogue (`Catalogue.agrees`), so a renderer that reads
them certifies nothing by itself.
"""

from functools import partial
import re

from bridges.common import lean_render, schema
from bridges.common.lean_render import record, require

# Catalogue identities and members are bounded by the source profile's strings.
text = partial(lean_render.text, limit=512)
seq = lean_render.seq

SORTS = {"Field": ".field", "Group": ".group", "Commitment": ".commitment",
         "Transcript": ".transcript"}


def modulus(value):
    if value is None:
        return "none"
    require(isinstance(value, str) and re.fullmatch(r"[1-9][0-9]{0,1023}", value) is not None,
            "invalid catalogue modulus")
    return f"(some {value})"


def nominal(value):
    tag, identity, sort, members, capabilities, characteristic = record(value, 6)
    require(tag == "nominal" and sort in SORTS, "invalid nominal catalogue row")

    def member(pair):
        name, target = record(pair, 2)
        return f"({text(name)}, {text(target)})"
    return (f"⟨{text(identity)}, {SORTS[sort]}, {seq(members, member)}, "
            f"{seq(capabilities, text)}, {modulus(characteristic)}⟩")


def service_row(value):
    tag, contract, sampled, methods = record(value, 4)
    require(tag == "service", "invalid service catalogue row")
    return f"⟨{text(contract)}, {text(sampled)}, {seq(methods, text)}⟩"


def catalogue(value):
    """The Lean `Catalogue` term of a catalogue slot, after checking its shape."""
    nominals, services = record(value, 2)
    return f"{{ nominals := {seq(nominals, nominal)}, services := {seq(services, service_row)} }}"


def member_resolver(rows):
    """Project an associated member through the exported row of its parent.

    The member's result sort comes from the catalog's member declaration; its
    identity comes only from the exported row.
    """
    def project(parent, member):
        require(rows is not None and parent[0] == "domain", "missing associated domain catalogue")
        matches = [row for row in rows[0] if row[1] == parent[2] and row[2] == parent[1]]
        require(len(matches) == 1, "unknown associated domain")
        members = dict(matches[0][3])
        require(member in members, "missing associated domain member")
        declarations = [row for row in schema.declarations()["members"]
                        if row["name"] == member and row["owner"]["sort"] == parent[1]]
        require(len(declarations) == 1, "unknown associated member declaration")
        return ["domain", declarations[0]["result"]["sort"], members[member]]
    return project


def require_capabilities(operation, terms, rows):
    """Each capability requirement of a resolved signature holds of the exported
    row of its single domain argument."""
    nominals = {row[1]: row for row in rows[0]} if rows else {}
    for requirement in operation["requirements"]:
        arguments = [terms[i] for i in requirement["arguments"]]
        require(len(arguments) == 1 and arguments[0][0] == "domain", "unsupported source requirement")
        domain = nominals.get(arguments[0][2])
        require(domain is not None and requirement["capability"] in domain[4], "missing binding capability")


def field_modulus(rows, identity):
    """Read a field's characteristic; formal catalogue admission checks the row."""
    matches = [row for row in rows[0] if row[1] == identity and row[2] == "Field"]
    require(len(matches) == 1 and len(matches[0]) == 6 and matches[0][5] is not None,
            "field parameter needs independent domain admission")
    value = matches[0][5]
    modulus(value)
    require(int(value) > 1, "invalid field characteristic")
    return int(value)


def service(rows, contract):
    """The exported row of a random service contract."""
    matches = [row for row in rows[1] if row[1] == contract]
    require(len(matches) == 1, "unknown service catalogue row")
    return matches[0]
