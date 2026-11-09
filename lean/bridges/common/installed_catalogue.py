#!/usr/bin/env python3
"""Generate the installed catalogue rows of the Lean readers from the catalog.

`common/catalog/declarations.json` owns the installed domain rows and random
services. This generator projects every one of them into
`Zkc.IR.Source.Structured.InstalledCatalogue`, in the encoding the native
exporter gives exported rows: identity, sort, associated members and
capability facts in declaration order and, for a field, its characteristic as
the modulus; a service's methods are `draw` and each method whose capability
its sampled field holds, selected by the nominal `service.random` constructor
in service-method declaration order. Which
rows Lean admits is decided by hand in `CatalogueEnvironment.lean`, never here.

`--write` installs the module; `--check` refuses a module that differs from a
fresh rendering of the declarations.
"""

import argparse
from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common import lean_render, schema  # noqa: E402
from bridges.common.lean_render import Refused, require  # noqa: E402
from support.packages import module_path  # noqa: E402

LEAN = Path(__file__).resolve().parents[2]
MODULE = module_path("Zkc.IR.Source.Structured.InstalledCatalogue")
SORTS = {"Field": ".field", "Group": ".group", "Commitment": ".commitment", "Transcript": ".transcript"}
# A catalog identity: a letter or underscore, then letters, digits and `_ . - /`.
# It names its Lean definition between guillemets.
IDENTITY = re.compile(r"[A-Za-z_][A-Za-z0-9_./-]{0,255}")


def identity(value):
    require(isinstance(value, str) and IDENTITY.fullmatch(value) is not None,
            f"invalid catalog identity {value!r}")
    return value


def text(value):
    return lean_render.text(value, 256, printable_ascii=True)


def object_fields(value, fields):
    """Exact shapes for the source rows consumed by this independent reader."""
    require(isinstance(value, dict), "expected catalog object")
    require(set(fields) <= value.keys(), "missing catalog fields")
    require(value.keys() <= set(fields), "unknown catalog fields")


def source_name(value):
    require(isinstance(value, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value) is not None,
            "invalid source name")
    return value


def source_term(value):
    require(isinstance(value, dict), "expected source type")
    if "constructor" in value:
        object_fields(value, ("constructor",))
        source_name(value["constructor"])
    else:
        object_fields(value, ("static", "member") if "member" in value else ("static",))
        require(type(value["static"]) is int and 0 <= value["static"] <= 1048576,
                "invalid source static index")
        if "member" in value:
            source_name(value["member"])


def service_methods(declarations):
    """Validate source identities and select only this consumer's nominal owner.

    Source names never confer service authority. Other service constructors may
    use the same method names, and their rows must not enter Random's profile.
    The signature rows describe gates; they install no new Lean interpretation.
    """
    tables = ("frontendRules", "frontendDeclarations", "serviceSignatures", "serviceMethods")
    require(all(table in declarations for table in tables), "missing catalog tables")
    require(all(isinstance(declarations[table], list) for table in tables), "expected catalog rows")
    rules = {}
    for row in declarations["frontendRules"]:
        object_fields(row, ("name", "kind", "statics", "inputs", "output"))
        name = source_name(row["name"])
        require(name not in rules, "duplicate frontend rule")
        rules[name] = row
    identities, names, prelude, constructors = set(), set(), set(), set()
    for row in declarations["frontendDeclarations"]:
        object_fields(row, ("identity", "owner", "name", "kind", "statics", "inputs",
                            "output", "association", "prelude"))
        declared = schema.string(row["identity"])
        require(declared not in identities, "duplicate frontend identity")
        identities.add(declared)
        owner, name = schema.string(row["owner"]), source_name(row["name"])
        require(re.fullmatch(r"zkc(?:::[A-Za-z_][A-Za-z0-9_]*)+", owner) is not None,
                "invalid frontend owner")
        require((owner, name) not in names, "duplicate frontend ownership")
        names.add((owner, name))
        require(row["kind"] in ("Math", "Local", "Interface", "Requirement"), "invalid frontend kind")
        require(type(row["prelude"]) is bool, "expected prelude Boolean")
        if row["prelude"]:
            require(name not in prelude, "duplicate prelude frontend name")
            prelude.add(name)
        require(isinstance(row["statics"], list) and isinstance(row["inputs"], list),
                "expected source parameters")
        parameters = set()
        for static in row["statics"]:
            object_fields(static, ("name", "parameter"))
            parameter = source_name(static["name"])
            require(parameter not in parameters, "duplicate source parameter name")
            parameters.add(parameter)
            kind = static["parameter"]
            object_fields(kind, ("kind", "sort"))
            require(kind["kind"] in ("Domain", "Type", "Nat"), "invalid source parameter kind")
            schema.string(kind["sort"], nonempty=False)
            require(kind["kind"] == "Domain" or kind["sort"] == "", "non-domain kind has a sort")
        for slot in row["inputs"]:
            object_fields(slot, ("name", "type"))
            parameter = source_name(slot["name"])
            require(parameter not in parameters, "duplicate source parameter name")
            parameters.add(parameter)
            source_term(slot["type"])
        if row["output"] is not None:
            source_term(row["output"])
        association = row["association"]
        object_fields(association, ("kind", "target"))
        require(association["kind"] in ("primitive", "rule"), "invalid frontend association")
        schema.string(association["target"])
        if association["kind"] == "rule":
            require(association["target"] in rules, "unknown frontend rule")
        requirement_rule = (association["kind"] == "rule"
                            and rules[association["target"]]["kind"] == "Requirement")
        if row["kind"] == "Requirement" or requirement_rule:
            require(row["kind"] == "Requirement" and association["kind"] == "rule" and not row["inputs"]
                    and row["output"] is None, "invalid consumer requirement shape")
            rule = rules[association["target"]]
            require(rule["kind"] == "Requirement" and not rule["inputs"]
                    and rule["output"] is None
                    and rule["statics"] == [static["parameter"] for static in row["statics"]],
                    "consumer requirement rule signature mismatch")
        if association == {"kind": "rule", "target": "RandomConstructor"}:
            require(rules["RandomConstructor"] == {
                "name": "RandomConstructor", "kind": "Interface",
                "statics": [{"kind": "Domain", "sort": "Field"}],
                "inputs": [], "output": None,
            }, "unsupported RandomConstructor rule")
            require(row["kind"] == "Interface" and not row["inputs"] and row["output"] is None
                    and [s["parameter"] for s in row["statics"]] == [{"kind": "Domain", "sort": "Field"}],
                    "invalid RandomConstructor shape")
            constructors.add(declared)

    signatures = {}
    for row in declarations["serviceSignatures"]:
        object_fields(row, ("name", "capability"))
        name = source_name(row["name"])
        require(name not in signatures, "duplicate service signature")
        capability = schema.string(row["capability"], nonempty=False)
        if capability:
            source_name(capability)
            require(any(c["name"] == capability and c["parameters"] == [{"kind": "Domain", "sort": "Field"}]
                        for c in declarations["capabilities"]), "unknown service capability")
        signatures[name] = capability
    methods, selected = set(), []
    for row in declarations["serviceMethods"]:
        object_fields(row, ("identity", "constructor", "name", "signature", "capability"))
        declared = schema.string(row["identity"])
        require(declared not in identities, "duplicate service method identity")
        identities.add(declared)
        constructor = schema.string(row["constructor"])
        require(constructor in constructors, "invalid service method constructor")
        name = source_name(row["name"])
        require((constructor, name) not in methods, "duplicate service method")
        methods.add((constructor, name))
        signature = source_name(row["signature"])
        capability = schema.string(row["capability"], nonempty=False)
        require(signature in signatures and signatures[signature] == capability,
                "service method capability mismatch")
        if constructor == "service.random":
            # The formal consumer interprets these method names with fixed
            # signatures. Validate that profile before projecting names only;
            # a new catalog signature does not install a Lean interpretation.
            supported = {"draw": ("RandomDraw", ""),
                         "index": ("RandomIndex", "IndexRandomness"),
                         "indices": ("RandomIndices", "IndexBlockRandomness")}
            # Other names remain catalog data; the operation reader has no
            # rule for them. A canonical name cannot acquire another meaning.
            require(name not in supported or supported[name] == (signature, capability),
                    "unsupported formal service method profile")
            selected.append(row)
    return selected


def characteristic(row):
    value = (row.get("field") or {}).get("characteristic")
    require(isinstance(value, str) and re.fullmatch(r"[1-9][0-9]{0,1023}", value) is not None,
            f"{row['identity']}: invalid field characteristic")
    return value


def domain(row):
    """The definitions of one domain row: its characteristic, for a field, and its row."""
    name = identity(row["identity"])
    require(row.get("sort") in SORTS, f"{name}: the Lean catalogue has no sort {row.get('sort')!r}")
    members = ", ".join(f"({text(member)}, {text(identity(target))})" for member, target in row["members"])
    capabilities = ", ".join(text(capability) for capability in row["capabilities"])
    lines = []
    modulus = "none"
    if row["sort"] == "Field":
        lines.append(f"def Characteristics.«{name}» : Nat := {characteristic(row)}")
        modulus = f"some Characteristics.«{name}»"
    lines += [f"def Domains.«{name}» : Nominal where",
              f"  identity := {text(name)}",
              f"  sort := {SORTS[row['sort']]}",
              f"  members := [{members}]",
              f"  capabilities := [{capabilities}]",
              f"  modulus := {modulus}"]
    return "\n".join(lines)


def service(row, domains, methods):
    """The definition of one random service, with the methods its field installs."""
    contract, field = identity(row["contract"]), identity(row["field"])
    sampled = domains.get(field)
    require(sampled is not None and sampled["sort"] == "Field", f"{contract}: unknown sampled field {field!r}")
    offered = [method["name"] for method in methods
               if method["capability"] == "" or method["capability"] in sampled["capabilities"]]
    return "\n".join([f"def Services.«{contract}» : Service where",
                      f"  contract := {text(contract)}",
                      f"  sampled := {text(field)}",
                      f"  methods := [{', '.join(text(method) for method in offered)}]"])


def render(declarations):
    """The generated Lean module of the installed rows of `declarations`."""
    require(isinstance(declarations, dict)
            and declarations.get("format") == "zkc.contract-declarations/0", "catalog format")
    methods = service_methods(declarations)
    rows = declarations["domains"]
    domains = {row["identity"]: row for row in rows}
    require(len(domains) == len(rows), "duplicate catalog domain identity")
    services = declarations["randomServices"]
    contracts = [row["contract"] for row in services]
    require(len(set(contracts)) == len(contracts), "duplicate random service contract")
    definitions = "\n\n".join([*(domain(row) for row in rows),
                                *(service(row, domains, methods) for row in services)])
    nominals = ",\n    ".join(f"Domains.«{row['identity']}»" for row in rows)
    offered = ",\n    ".join(f"Services.«{contract}»" for contract in contracts)
    return f'''module

public import Zkc.IR.Source.Structured.Catalogue

@[expose] public section

/-! Installed catalogue rows, generated from `common/catalog/declarations.json`.
Regenerate with bridges/common/installed_catalogue.py --write;
checks/check_installed_catalogue.py refuses a module that differs from a fresh
rendering.

Every installed domain row and random service, in declaration order, in the
encoding of exported rows. Which rows the Lean readers admit is decided in
`CatalogueEnvironment`, not here. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Installed

{definitions}

/-- Every installed domain row and random service. -/
def catalogue : Catalogue where
  nominals := [
    {nominals}]
  services := [
    {offered}]

end Zkc.Source.Structured.Installed
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--declarations", type=Path, help="the declarations to render (default: the catalog's)")
    parser.add_argument("--output", type=Path, default=MODULE, help="the generated module")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    source = args.declarations or LEAN.parent / "common/catalog/declarations.json"
    declarations = schema.loads(source.read_bytes())
    content = render(declarations)
    if args.write:
        args.output.write_text(content, encoding="utf-8")
    elif not args.output.is_file() or args.output.read_bytes() != content.encode("utf-8"):
        raise Refused(f"stale generated module: {args.output}; regenerate with --write")
    print(f"installed catalogue: {len(declarations['domains'])} domains, "
          f"{len(declarations['randomServices'])} services, {'written' if args.write else 'current'}")


if __name__ == "__main__":
    try:
        main()
    except Refused as error:
        sys.exit(str(error))
