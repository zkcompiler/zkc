"""Owner-local checked identities, private closures, and imported selections."""

import json
from pathlib import Path
from contextlib import contextmanager
from itertools import count

from cases import case
from commands import Commands
from tools import compiler, records

record_dir = records()
commands = Commands(record_dir)
fixture_ids = count()


@contextmanager
def project_directory():
    path = record_dir / f"project-{next(fixture_ids)}"
    path.mkdir(parents=True, exist_ok=True)
    yield path


def identity(name):
    return f'library(namespace="project-tests",name="{name}",version="1",resolution="r1")'


CELL = f'''module {{
  {identity("cell")};
  association Private = "private subject";
  pub interface Cell {{ type Value copy drop; local step(value: Value) -> Value; }}
  pub component BoolCell: Cell {{
    type Value = bool;
    local step(implementationBinder: bool) -> bool {{ return Helper(implementationBinder); }}
  }}
  fn Helper(x: bool) -> bool {{ return x; }}
  pub fn Client<C: Cell>(input: C::Value) -> C::Value {{ return C::step(value: input); }}
}}'''


def write(root, name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


def run(root, source, libraries, mode="protocol-analyze", refuses=None):
    app = write(root, "app.pir", source)
    files = [write(root, f"{name}/lib.pir", text) for name, text in libraries.items()]
    result = commands.run([compiler, mode, app, *[f"--library={p}" for p in files]], refuses=refuses)
    return json.loads(result) if result and mode in ("protocol-source", "protocol-analyze") else result


def direct():
    return f'''module {{
      {identity("app")}; dependency cell = {identity("cell")};
      use cell::{{Cell, BoolCell, Client}};
      link Identity = Client<BoolCell>;
      fn Main(x: bool) -> bool {{ return Identity(input: x); }}
    }}'''


def owned(report, section, owner):
    rows = report["checked_libraries"][section]
    result = {}
    for row in rows:
        declaration = row.get("declaration", row.get("body", {}).get("declaration", {}))
        if declaration.get("library") == owner:
            result[declaration["name"]] = row["identity"]
    return result


with case("private helper closure links without granting its caller private names"), project_directory() as tmp:
    root = Path(tmp)
    report = run(root, direct(), {"cell": CELL})
    assert report["state"] == "source_checked", report["diagnostics"]
    run(root, direct(), {"cell": CELL}, "protocol-admit")
    for private in ("Helper", "Private"):
        run(root, direct().replace("Cell, BoolCell, Client", f"Cell, BoolCell, Client, {private}"),
            {"cell": CELL}, "protocol-source", "source-name-private")


with case("a diamond preserves the common owner's exact checked identity"), project_directory() as tmp:
    root = Path(tmp)
    baseline = run(root, direct(), {"cell": CELL})
    libraries = {"cell": CELL}
    for name in ("left", "right"):
        libraries[name] = f'''module {{
          {identity(name)}; dependency cell = {identity("cell")};
          pub use cell::{{Cell, BoolCell}}; use cell::Client;
          association Hidden = "{name}";
          pub fn Through<C: Cell>(value: C::Value) -> C::Value {{
            return Client::<C>(input: value);
          }}
        }}'''
    diamond = f'''module {{
      {identity("app")};
      dependency left = {identity("left")}; dependency right = {identity("right")};
      use left::{{Through as Left, BoolCell as A}};
      use right::{{Through as Right, BoolCell as B}};
      link One = Left<A>; link Two = Right<B>;
      fn Main(x: bool) -> bool {{ let y = One(value: x); return Two(value: y); }}
    }}'''
    report = run(root, diamond, libraries)
    assert report["state"] == "source_checked", report["diagnostics"]
    for section in ("interfaces", "clients"):
        assert owned(report, section, "cell") == owned(baseline, section, "cell")
    source = run(root, diamond, libraries, "protocol-source")
    reordered = dict(reversed(list(libraries.items())))
    assert source == run(root, diamond.replace("as Left", "as Renamed").replace("= Left<A>", "= Renamed<A>"),
                         reordered, "protocol-source")
    run(root, diamond, libraries, "protocol-admit")


with case("same member spellings in two owners retain distinct origins and subjects"), project_directory() as tmp:
    root = Path(tmp)
    second = CELL.replace(identity("cell"), identity("second"))
    app = f'''module {{
      dependency a = {identity("cell")}; dependency b = {identity("second")};
      use a::{{Client as A, BoolCell as CA}};
      use b::{{Client as B, BoolCell as CB}};
      link Left = A<CA>; link Right = B<CB>;
      fn Main(x: bool) -> bool {{let y = Left(x); return Right(y);}}
    }}'''
    report = run(root, app, {"a": CELL, "b": second})
    assert report["state"] == "source_checked", report["diagnostics"]
    assert owned(report, "interfaces", "cell") != owned(report, "interfaces", "second")
    run(root, app, {"a": CELL, "b": second}, "protocol-admit")


with case("an anonymous application can own checked local definitions"), project_directory() as tmp:
    app = CELL.replace(identity("cell") + ";", "").replace("pub ", "")
    app = app[:-1] + "link Closed = Client<BoolCell>; }"
    report = run(Path(tmp), app, {})
    assert report["state"] == "source_checked", report["diagnostics"]


with case("checked generic traversals compose and configure by public static labels"), project_directory() as tmp:
    root = Path(tmp)
    library = f'''module {{ {identity("folds")};
      pub fn Last<N: nat>(items: Array<bool, N>, initial: bool) -> bool {{
        return fold items with initial |state, item| {{ item }};
      }}
      pub fn Three(value: bool) -> bool {{
        return Last::<3>(items: [value, value, value], initial: value);
      }}
    }}'''
    source = f'''module {{
      dependency folds = {identity("folds")}; use folds::{{Last, Three}};
      configure Empty = Last(N = 0);
      fn Main(value: bool) -> bool {{
        let empty = Empty(items: [], initial: value);
        return Three(value: empty);
      }}
    }}'''
    report = run(root, source, {"folds": library})
    assert report["state"] == "source_checked", report["diagnostics"]
    run(root, source, {"folds": library}, "protocol-admit")
    for binding in ("Unknown = 0", "N = 0, N = 0", ""):
        run(root, source.replace("N = 0", binding), {"folds": library},
            "protocol-source", "library-source-configuration")


with case("same named protocols remain distinct and private constructors cannot be impersonated"), project_directory() as tmp:
    root = Path(tmp)
    libs = {name: f'''module {{ {identity(name)};
      pub checked struct Ticket(value: bool) constructors(Make);
      pub fn Make(value: bool) -> Ticket {{ return Ticket(value = value); }}
      pub protocol Echo {{ roles(A); inputs(A value: bool); outputs(A bool); return value; }}
    }}''' for name in ("left", "right")}
    source = f'''module {{
      dependency left = {identity("left")}; dependency right = {identity("right")};
      use left::Echo as Left; use right::Echo as Right; use left::Ticket;
      protocol Parent {{ roles(A); inputs(A value: bool); outputs(A bool);
        dependencies(first: Left(), second: Right());
        invoke first(value) -> (middle);
        invoke second(middle) -> (result);
        return result;
      }}
      instance Root: Parent {{ roles(A=A); dependencies(first=L, second=R); }}
      instance L: Left {{ roles(A=A); }} instance R: Right {{ roles(A=A); }}
      entry main=Root;
    }}'''
    run(root, source, libs, "protocol-admit")
    forged = source.replace("protocol Parent", "fn Make(x: bool)->Ticket { return Ticket(value = x); } protocol Parent")
    run(root, forged, libs, "protocol-source", "source-checked-construction")


with case("split multi-type branding compares aliases seals and explicit identities"), project_directory() as tmp:
    import re

    root = Path(tmp)
    library = f'''module {{
      {identity("branded")};
      pub interface Pair {{
        type Value drop; type Stamp drop;
        local keep(value: Value, stamp: Stamp) -> (Value, Stamp);
      }}
      pub component Empty<Tag: association>: Pair {{
        type Value = (); type Stamp = ();
        local keep(value: Value, stamp: Stamp) -> (Value, Stamp) {{
          return (value, stamp);
        }}
      }}
      pub fn Client<C: Pair>(value: C::Value, stamp: C::Stamp) -> (C::Value, C::Stamp) {{
        return C::keep(value: value, stamp: stamp);
      }}
    }}'''
    app = f'''module {{
      dependency branded = {identity("branded")};
      use branded::{{Empty, Client}};
      association Shared = "shared";
      association Left = "left"; association Right = "right";
      select A = Empty<Shared>; select B = Empty<Shared>;
      link First = Client<A>; link Second = Client<B>;
    }}'''
    alternatives = [
        (app, 2),
        (app.replace("select A", "seal A").replace("select B", "seal B"), 4),
        (app.replace("A = Empty<Shared>", "A = Empty<Left>")
            .replace("B = Empty<Shared>", "B = Empty<Right>"), 4),
    ]
    for text, count in alternatives:
        output = run(root, text, {"branded": library}, "protocol-source")
        slots = set(re.findall(r"resource_unit:library_slot_[0-9]+", json.dumps(output)))
        assert len(slots) == count, slots
        run(root, text, {"branded": library}, "protocol-admit")


with case("source cannot impersonate installed contract owner"), project_directory() as tmp:
    run(Path(tmp), '''module {
      library(namespace="zkc",name="installed-contracts",version="1",resolution="builtin");
      fn Main(x: bool) -> bool { return x; }
    }''', {}, "protocol-source", "source-library-reserved")


with case("diagnostic overflow is bounded and cannot recover to emission"), project_directory() as tmp:
    app = "module {\n" + "\n".join(
        f"use missing::F{i};" for i in range(300)
    ) + "\n}"
    report = run(Path(tmp), app, {})
    assert report["state"] == "incomplete"
    assert len(report["diagnostics"]) == 256
    assert report["diagnostics"][-1]["code"] == "source-diagnostic-limit"
    run(Path(tmp), app, {}, "protocol-source", "source-name-unresolved")
