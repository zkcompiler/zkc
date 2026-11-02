#!/usr/bin/env python3
"""Generate the installed catalogue rows of the Lean readers from the catalog.

`common/catalog/declarations.json` owns the installed domain rows and random
services. This generator projects every one of them into
`Zkc/Source/Structured/InstalledCatalogue.lean`, in the encoding the native
exporter gives exported rows: identity, sort, associated members and
capability facts in declaration order and, for a field, its characteristic as
the modulus; a service's methods are `draw` and each method whose capability
its sampled field holds, in the order of the service-method declarations. Which
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

LEAN = Path(__file__).resolve().parents[2]
MODULE = LEAN / "Zkc/Source/Structured/InstalledCatalogue.lean"
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
    require(declarations.get("format") == "zkc.contract-declarations/0", "catalog format")
    rows = declarations["domains"]
    domains = {row["identity"]: row for row in rows}
    require(len(domains) == len(rows), "duplicate catalog domain identity")
    services = declarations["randomServices"]
    contracts = [row["contract"] for row in services]
    require(len(set(contracts)) == len(contracts), "duplicate random service contract")
    definitions = "\n\n".join([*(domain(row) for row in rows),
                                *(service(row, domains, declarations["serviceMethods"]) for row in services)])
    nominals = ",\n    ".join(f"Domains.«{row['identity']}»" for row in rows)
    offered = ",\n    ".join(f"Services.«{contract}»" for contract in contracts)
    return f'''module

public import Zkc.Source.Structured.Catalogue

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
    declarations = (schema.declarations() if args.declarations is None
                    else schema.loads(args.declarations.read_bytes()))
    content = render(declarations)
    if args.write:
        args.output.write_text(content, encoding="utf-8")
    elif not args.output.is_file() or args.output.read_text(encoding="utf-8") != content:
        raise Refused(f"stale generated module: {args.output}; regenerate with --write")
    print(f"installed catalogue: {len(declarations['domains'])} domains, "
          f"{len(declarations['randomServices'])} services, {'written' if args.write else 'current'}")


if __name__ == "__main__":
    try:
        main()
    except Refused as error:
        sys.exit(str(error))
