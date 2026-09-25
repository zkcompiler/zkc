"""Source project resolution uses identities, visibility and captured inputs."""

import json
import subprocess

from tools import compiler, records
from journal import names


def identity(name, version="1"):
    return f'library(namespace="test", name="{name}", version="{version}", resolution="r1")'


root = records()
app = root / "app.pir"
lib = root / "lib.pir"

def run(source, libraries, code=None, mode="protocol-source"):
    app.write_text(source)
    paths = []
    for name, text in libraries.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        if name.endswith("lib.pir"):
            paths.append(path)
    result = subprocess.run(
        [str(compiler), mode, str(app), *[f"--library={p}" for p in paths]],
        capture_output=True,
        text=True,
    )
    if code:
        assert result.returncode > 0, result.stdout
        assert names(result.stderr, code), result.stderr
        assert not result.stdout
        return result.stderr
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)

library = f"module {{ {identity('bits')}; pub fn Identity(value: bool) -> bool {{ return value; }} }}"
client = f"""module {{
  dependency bits = {identity('bits')};
  use bits::Identity;
  fn Main(value: bool) -> bool {{ return Identity(value); }}
}}"""
baseline = run(client, {"lib.pir": library})
alias = client.replace("use bits::Identity;", "use bits::Identity as Same;").replace(
    "return Identity(value)", "return Same(value)"
)
assert baseline == run(alias, {"lib.pir": library})
relocated = run(client, {"moved/lib.pir": library})
assert baseline == relocated
run(client, {"lib.pir": library.replace("pub fn", "fn")}, "source-name-private")
run(client.replace('version="1"', 'version="2"'), {"lib.pir": library}, "source-dependency-missing")
run(client.replace("use bits::Identity;", "use bits::Absent;"), {"lib.pir": library}, "source-name-unresolved")
run(client.replace("use bits::Identity;", "use bits::Identity; use bits::Identity;"),
    {"lib.pir": library}, "source-name-duplicate")

facade = f"module {{ {identity('bits')}; mod inner; pub use inner::Identity; }}"
child = "module { pub fn Identity(value: bool) -> bool { return value; } }"
run(client, {"lib.pir": facade, "inner.pir": child})
run(client, {"lib.pir": facade, "inner.pir": child.replace("pub fn", "fn")},
    "source-name-private")
run(client.replace("use bits::Identity;", "use bits::inner::Identity;"),
    {"lib.pir": facade, "inner.pir": child}, "source-name-private")

# `self` and `super` name a module with its own visibility. A private module
# re-exported through them would otherwise become reachable from outside.
selfish = "module { pub use self as Here; pub fn Identity(value: bool) -> bool { return value; } }"
through = client.replace("use bits::Identity;", "use bits::Here::Identity;")
exposing = f"module {{ {identity('bits')}; mod inner; pub use inner::Here; }}"
run(through, {"lib.pir": exposing, "inner.pir": selfish}, "source-private-reexport")
run(through, {"lib.pir": exposing.replace("mod inner", "pub mod inner"), "inner.pir": selfish})
nested = f"module {{ {identity('bits')}; mod outer; pub use outer::inner::Up as Here; }}"
run(through, {"lib.pir": nested, "outer.pir": "module { pub mod inner; }",
              "outer/inner.pir": "module { pub use super as Up; }"}, "source-private-reexport")

# A logical origin is the module path and the name, and a carrier name is at
# most 128 bytes. A path that makes it longer is refused at the declaration,
# naming the origin and the bound, rather than at admission of the carrier.
long = "m" * 60
deep = client.replace("use bits::Identity;", f"use bits::{long}::{long}::Identity;")
error = run(deep, {"lib.pir": f"module {{ {identity('bits')}; pub mod {long}; }}",
                   f"{long}.pir": f"module {{ pub mod {long}; }}",
                   f"{long}/{long}.pir": child}, "source-origin-limit")
assert f"'{long}.{long}.Identity'" in error and "128 bytes" in error, error
assert f"{long}/{long}.pir:1:" in error, error
# Only an origin that becomes a carrier name is bounded: a type's is not.
typed = f"""module {{
  dependency bits = {identity('bits')};
  use bits::{long}::{long}::Flag;
  fn Main(value: Flag) -> Flag {{ return value; }}
}}"""
run(typed, {"lib.pir": f"module {{ {identity('bits')}; pub mod {long}; }}",
            f"{long}.pir": f"module {{ pub mod {long}; }}",
            f"{long}/{long}.pir": "module { pub struct Flag { set: bool } }"})
run(deep.replace(f"{long}::{long}", f"{long}::{long[:3]}"),
    {"lib.pir": f"module {{ {identity('bits')}; pub mod {long}; }}",
     f"{long}.pir": f"module {{ pub mod {long[:3]}; }}",
     f"{long}/{long[:3]}.pir": child})

# A declared name may contain dots. Where it is also a path to another
# declaration, an unquoted use of it could mean either, so it refuses; quoting
# names the declaration here. With no path reading it stays an exact name.
dotted = f"""module {{
  dependency bits = {identity('bits')};
  fn bits.Identity(value: bool) -> bool {{ let out: bool = bool::not(value); return out; }}
  fn Main(value: bool) -> bool {{ return CALL(value); }}
}}"""


def callee(carrier):
    """The function Main applies."""
    if carrier[0] == "zkc.relations/1":
        carrier = carrier[2]
    [main] = [f for f in carrier[2] if f[1] == "Main"]
    [apply] = [s for s in main[4] if s[0] == "apply"]
    return apply[2]


for spelling in ("bits::Identity", "bits.Identity"):
    run(dotted.replace("CALL", spelling), {"lib.pir": library}, "source-name-ambiguous")
assert callee(run(dotted.replace("CALL", '"bits.Identity"'), {"lib.pir": library})) == "bits.Identity"
elsewhere = library.replace("Identity", "Other")
assert callee(run(dotted.replace("CALL", "bits.Identity"), {"lib.pir": elsewhere})) == "bits.Identity"
nested = """module { mod inner;
  fn inner.Keep(value: bool) -> bool origin Chosen() { return value; }
  fn Main(value: bool) -> bool { return CALL(value); }
}"""
run(nested.replace("CALL", "inner.Keep"), {"inner.pir": "module { pub fn Keep(value: bool) -> bool { return value; } }"},
    "source-name-ambiguous")
assert callee(run(nested.replace("CALL", "inner.Keep"), {"inner.pir": "module { }"})) == "inner.Keep"

# A relation view's generated helpers are members of the view, so a path to one
# is a second reading too, whether it reaches the view directly or through an
# import.
field = "Vector<bls12-381.fr::Element>"
helper = f"""module {{ mod shapes;
  dependency bits = {identity('bits')};
  fn "HELPER"(statement: {field}, witness: {field}) -> {field} {{ return statement; }}
  fn Main(statement: {field}, witness: {field}) -> {field} {{ return CALL(statement, witness); }}
}}"""
view_files = {
    "lib.pir": f"""module {{ {identity('bits')}; relation Circuit = r1cs("data.json");
      pub derive Core = rank_one(Circuit, public_matrices); }}""",
    "shapes.pir": "module { use bits::Core as View; }",
    "data.json": json.dumps(["zkc.relation.r1cs/1", "bls12-381.fr", "4", "1", "1",
                             [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]]),
}
for spelling in ("bits.Core_Assemble", "shapes.View_Assemble"):
    declared = helper.replace("HELPER", spelling)
    run(declared.replace("CALL", spelling), view_files, "source-name-ambiguous")
    assert callee(run(declared.replace("CALL", f'"{spelling}"'), view_files)) == spelling

# A declaration clause keeps the same rule, although its common record keeps
# only the spelling. Each clause here names a dotted declaration in this module
# that is also a path into `bits`; quoted, the project compiles.
clause_library = f"""module {{ {identity('bits')};
  pub protocol P {{ roles(A); return; }}
  pub instance I: P {{ roles(A=A); }}
  pub fn Make(value: bool) -> bool {{ return value; }}
  pub fn Keep<F: domain Field>(value: F::Element) -> F::Element {{ return value; }}
  pub interface Cell {{ type Value drop; local step(x: Value) -> Value; }}
  pub fn Client<C: Cell>(x: C::Value) -> C::Value {{ return C::step(x); }}
  pub fn Select(tags: Indices) -> index {{ return tags.len(); }}
  pub mod shapes;
}}"""
clauses = f"""module {{
  dependency bits = {identity('bits')};
  protocol "bits.P" {{ roles(A); return; }}
  protocol Q {{ roles(A); dependencies(c: "bits.P"()); invoke c() -> (); return; }}
  instance "bits.I": "bits.P" {{ roles(A=A); }}
  instance Root: Q {{ roles(A=A); dependencies(c="bits.I"); }}
  entry main = Root;
  entry other = "bits.I";
  checked struct Ticket(value: bool) constructors("bits.Make");
  fn "bits.Make"(value: bool) -> Ticket {{ return Ticket(value = value); }}
  fn "bits.Keep"<F: domain Field>(value: F::Element) -> F::Element {{ return value; }}
  configure Closed = "bits.Keep"(F = "koala-bear");
  interface "bits.Cell" {{ type Value drop; local step(x: Value) -> Value; }}
  component Flag: "bits.Cell" {{ type Value = bool; local step(x: bool) -> bool {{ return x; }} }}
  interface Cell {{ type Value drop; local step(x: Value) -> Value; }}
  component Counter: Cell {{ type Value = bool; local step(x: bool) -> bool {{ return x; }} }}
  fn "bits.Client"<C: Cell>(x: C::Value) -> C::Value {{ return C::step(x); }}
  link Linked = "bits.Client"<Counter>;
  fn "bits.Select"(tags: Indices) -> index {{ return tags.len(); }}
  protocol Replay {{
    roles (Worker); parameters (events); inputs (Worker tags: Indices); outputs ();
    loop [event] events carry (t = tags) -> (held) {{ yield (t); }}
    return ();
  }}
  instance Family: Replay {{
    parameters (events = ingress(64, Worker = "bits.Select"(tags))); roles (Worker = Worker);
  }}
  entry family = Family;
}}"""
clause_files = {"lib.pir": clause_library, "shapes.pir": 'module { relation R = r1cs("data.json"); }',
                "data.json": json.dumps(["zkc.relation.r1cs/1", "bls12-381.fr", "4", "1", "1",
                                         [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]])}
run(clauses, clause_files)
for quoted, unquoted in [
    ('instance "bits.I": "bits.P"', 'instance "bits.I": bits.P'),
    ('dependencies(c: "bits.P"())', 'dependencies(c: bits.P())'),
    ('dependencies(c="bits.I")', 'dependencies(c=bits.I)'),
    ('entry other = "bits.I";', 'entry other = bits.I;'),
    ('constructors("bits.Make")', 'constructors(bits.Make)'),
    ('configure Closed = "bits.Keep"(', 'configure Closed = bits.Keep('),
    ('component Flag: "bits.Cell"', 'component Flag: bits.Cell'),
    ('link Linked = "bits.Client"<', 'link Linked = bits.Client<'),
    ('Worker = "bits.Select"(tags)', 'Worker = bits.Select(tags)'),
]:
    assert clauses.count(quoted) == 1, quoted
    run(clauses.replace(quoted, unquoted), clause_files, "source-name-ambiguous")
# A relation's name must be a plain symbol, so a dotted relation declared here
# is refused when relations are admitted, after resolution has read the quoted
# spelling as that declaration.
viewing = clauses.replace("entry family = Family;", """entry family = Family;
  use bits::shapes as m;
  relation "m.R" = r1cs("data.json");
  derive View = rank_one("m.R", public_matrices);""")
error = run(viewing, clause_files, "relation-admission")
assert not names(error, "source-name-ambiguous"), error
run(viewing.replace('rank_one("m.R",', "rank_one(m.R,"), clause_files, "source-name-ambiguous")

# A carrier prints back to text with the names the compiler generated for it,
# and exposes the same lossless public carrier-text reader as its own check.
def printed(carrier):
    path = root / "printed.json"
    path.write_text(json.dumps(carrier))
    result = subprocess.run([str(compiler), "protocol-format", str(path)], capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    return result.stdout


linked = run(f"""module {{ {identity('cells')};
  interface Cell {{ type Value drop; local step(x: Value) -> Value; }}
  component BoolCell: Cell {{ type Value = bool; local step(x: bool) -> bool {{ return x; }} }}
  fn Client<C: Cell>(x: C::Value) -> C::Value {{ return C::step(x); }}
  link Closed = Client<BoolCell>;
  fn Main(x: bool) -> bool {{ return Closed(x); }}
}}""", {})
for carrier, prefix in ((baseline, "src_"), (linked, "lib_")):
    text = printed(carrier)
    assert f"fn {prefix}" in text, text
    assert text.startswith("carrier module"), text
    assert run(text, {}) == carrier
    run(text.replace("carrier module", "module", 1), {}, "source-name-reserved")

cycle = f"module {{ {identity('bits')}; pub use second as Identity; use Identity as second; }}"
run(client, {"lib.pir": cycle}, "source-import-cycle")
duplicate = {"a/lib.pir": library, "b/lib.pir": library.replace("return value", "return true")}
run(client, duplicate, "source-library-conflict")

bad_signature = f"""module {{ {identity('bits')};
  struct Hidden {{ bit: bool }}
  pub fn Identity(value: Hidden) -> Hidden {{ return value; }}
}}"""
run(client, {"lib.pir": bad_signature}, "source-private-signature")
bad_body = library.replace("return value", "return missing")
error = run(client, {"lib.pir": bad_body}, "source-name-unresolved")
assert str(lib) in error, error

# Identity comes from the application's dependency closure. A captured library
# that nothing in it depends on would otherwise take part in origin
# qualification and change the constructed artifact, so it is refused.
unrelated = f"module {{ {identity('other')}; pub fn Identity(value: bool) -> bool {{ return value; }} }}"
run(client, {"lib.pir": library, "other/lib.pir": unrelated}, "project-library-unreachable")
base = f"module {{ {identity('base')}; pub fn Identity(value: bool) -> bool {{ return value; }} }}"
middle = f"""module {{ {identity('bits')};
  dependency base = {identity('base')};
  use base::Identity as Inner;
  pub fn Identity(value: bool) -> bool {{ return Inner(value); }}
}}"""
run(client, {"lib.pir": middle, "base/lib.pir": base})

# Recovery after a failed name marks every transitive caller unavailable in
# work linear in the references, whatever order the declarations appear in.
count = 8000
chain = "\n".join(f"  fn F{i}(x: bool) -> bool {{ return F{i + 1}(x); }}" for i in range(count))
app.write_text(f"module {{\n{chain}\n  fn F{count}(x: bool) -> bool {{ return Missing(x); }}\n}}\n")
result = subprocess.run([str(compiler), "protocol-source", str(app)],
                        capture_output=True, text=True, timeout=5)
assert result.returncode > 0 and ": error: source-name-unresolved: " in result.stderr, result.stderr

print("frontend project resolution controls passed")
