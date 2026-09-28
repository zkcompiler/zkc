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

library = f" {identity('bits')}; pub fn Identity(value: bool) -> bool {{ return value; }} "
client = f"""
  dependency bits = {identity('bits')};
  use bits::Identity;
  fn Main(value: bool) -> bool {{ return Identity(value); }}
"""
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

facade = f" {identity('bits')}; mod inner; pub use inner::Identity; "
child = " pub fn Identity(value: bool) -> bool { return value; } "
run(client, {"lib.pir": facade, "inner.pir": child})
run(client, {"lib.pir": facade, "inner.pir": child.replace("pub fn", "fn")},
    "source-name-private")
run(client.replace("use bits::Identity;", "use bits::inner::Identity;"),
    {"lib.pir": facade, "inner.pir": child}, "source-name-private")

# `self` and `super` name a module with its own visibility. A private module
# re-exported through them would otherwise become reachable from outside.
selfish = " pub use self as Here; pub fn Identity(value: bool) -> bool { return value; } "
through = client.replace("use bits::Identity;", "use bits::Here::Identity;")
exposing = f" {identity('bits')}; mod inner; pub use inner::Here; "
run(through, {"lib.pir": exposing, "inner.pir": selfish}, "source-private-reexport")
run(through, {"lib.pir": exposing.replace("mod inner", "pub mod inner"), "inner.pir": selfish})
nested = f" {identity('bits')}; mod outer; pub use outer::inner::Up as Here; "
run(through, {"lib.pir": nested, "outer.pir": " pub mod inner; ",
              "outer/inner.pir": " pub use super as Up; "}, "source-private-reexport")

# A logical origin is the module path and the name, and a carrier name is at
# most 128 bytes. A path that makes it longer is refused at the declaration,
# naming the origin and the bound, rather than at admission of the carrier.
long = "m" * 60
deep = client.replace("use bits::Identity;", f"use bits::{long}::{long}::Identity;")
error = run(deep, {"lib.pir": f" {identity('bits')}; pub mod {long}; ",
                   f"{long}.pir": f" pub mod {long}; ",
                   f"{long}/{long}.pir": child}, "source-origin-limit")
assert f"'{long}.{long}.Identity'" in error and "128 bytes" in error, error
assert f"{long}/{long}.pir:1:" in error, error
# Only an origin that becomes a carrier name is bounded: a type's is not.
typed = f"""
  dependency bits = {identity('bits')};
  use bits::{long}::{long}::Flag;
  fn Main(value: Flag) -> Flag {{ return value; }}
"""
run(typed, {"lib.pir": f" {identity('bits')}; pub mod {long}; ",
            f"{long}.pir": f" pub mod {long}; ",
            f"{long}/{long}.pir": " pub struct Flag { set: bool } "})
run(deep.replace(f"{long}::{long}", f"{long}::{long[:3]}"),
    {"lib.pir": f" {identity('bits')}; pub mod {long}; ",
     f"{long}.pir": f" pub mod {long[:3]}; ",
     f"{long}/{long[:3]}.pir": child})

# Punctuation and quoted declaration names cannot compete with a real path.
for name, code in (("bits.Identity", "source-syntax"), ('"bits.Identity"', "source-identifier"),
                   ("bits-Identity", "source-syntax")):
    invalid = f"""dependency bits = {identity('bits')};
      fn {name}(value: bool) -> bool {{ return value; }}
      fn Main(value: bool) -> bool {{ return bits::Identity(value); }}
    """
    run(invalid, {"lib.pir": library}, code)

# A local helper and a dependency path have different declaration identities.
selected = f"""dependency bits = {identity('bits')};
  fn LocalIdentity(value: bool) -> bool {{ return value; }}
  fn Main(value: bool) -> bool {{ return CALL(value); }}
"""
for target in ("LocalIdentity", "bits::Identity"):
    run(selected.replace("CALL", target), {"lib.pir": library})

# Every declaration-selector position rejects the obsolete quoted-reference
# escape. The matching ordinary reference remains legal.
clauses = '''
  protocol P { roles(A); return; }
  protocol Q { roles(A); dependencies(c: P()); invoke c() -> (); return; }
  instance I: P { roles(A=A); }
  instance Root: Q { roles(A=A); dependencies(c=I); }
  entry main = Root;
  entry other = I;
  checked struct Ticket { value: bool } constructors(Make);
  fn Make(value: bool) -> Ticket { return Ticket { value }; }
  fn Keep<F: domain Field>(value: F::Element) -> F::Element { return value; }
  configure Closed = Keep(F = "koala-bear");
  interface Cell { type Value drop; local step(x: Value) -> Value; }
  component Flag: Cell { type Value = bool; local step(x: bool) -> bool { return x; } }
  fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x); }
  link Linked = Client<Flag>;
'''
run(clauses, {})
for ordinary, obsolete in (
    ("instance I: P", 'instance I: "P"'),
    ("dependencies(c: P())", 'dependencies(c: "P"())'),
    ("dependencies(c=I)", 'dependencies(c="I")'),
    ("entry other = I;", 'entry other = "I";'),
    ("constructors(Make)", 'constructors("Make")'),
    ("configure Closed = Keep(", 'configure Closed = "Keep"('),
    ("component Flag: Cell", 'component Flag: "Cell"'),
    ("link Linked = Client<", 'link Linked = "Client"<'),
):
    run(clauses.replace(ordinary, obsolete), {}, "source-identifier")

# A carrier prints back to text with the names the compiler generated for it,
# and exposes the same lossless public carrier-text reader as its own check.
def printed(carrier):
    path = root / "printed.json"
    path.write_text(json.dumps(carrier))
    result = subprocess.run([str(compiler), "protocol-format", str(path)], capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    return result.stdout


linked = run(f""" {identity('cells')};
  interface Cell {{ type Value drop; local step(x: Value) -> Value; }}
  component BoolCell: Cell {{ type Value = bool; local step(x: bool) -> bool {{ return x; }} }}
  fn Client<C: Cell>(x: C::Value) -> C::Value {{ return C::step(x); }}
  link Closed = Client<BoolCell>;
  fn Main(x: bool) -> bool {{ return Closed(x); }}
""", {})
for carrier, prefix in ((baseline, "src_"), (linked, "lib_")):
    text = printed(carrier)
    assert f"fn {prefix}" in text, text
    assert text.startswith("carrier module"), text
    assert run(text, {}) == carrier
    run(f"fn {prefix}forbidden(x: bool) -> bool {{ return x; }}", {}, "source-name-reserved")

cycle = f" {identity('bits')}; pub use second as Identity; use Identity as second; "
run(client, {"lib.pir": cycle}, "source-import-cycle")
duplicate = {"a/lib.pir": library, "b/lib.pir": library.replace("return value", "return true")}
run(client, duplicate, "source-library-conflict")

bad_signature = f""" {identity('bits')};
  struct Hidden {{ bit: bool }}
  pub fn Identity(value: Hidden) -> Hidden {{ return value; }}
"""
run(client, {"lib.pir": bad_signature}, "source-private-signature")
bad_body = library.replace("return value", "return missing")
error = run(client, {"lib.pir": bad_body}, "source-name-unresolved")
assert str(lib) in error, error

# Identity comes from the application's dependency closure. A captured library
# that nothing in it depends on would otherwise take part in origin
# qualification and change the constructed artifact, so it is refused.
unrelated = f" {identity('other')}; pub fn Identity(value: bool) -> bool {{ return value; }} "
run(client, {"lib.pir": library, "other/lib.pir": unrelated}, "project-library-unreachable")
base = f" {identity('base')}; pub fn Identity(value: bool) -> bool {{ return value; }} "
middle = f""" {identity('bits')};
  dependency base = {identity('base')};
  use base::Identity as Inner;
  pub fn Identity(value: bool) -> bool {{ return Inner(value); }}
"""
run(client, {"lib.pir": middle, "base/lib.pir": base})

# Recovery after a failed name marks every transitive caller unavailable in
# work linear in the references, whatever order the declarations appear in.
count = 8000
chain = "\n".join(f"  fn F{i}(x: bool) -> bool {{ return F{i + 1}(x); }}" for i in range(count))
app.write_text(f"\n{chain}\n  fn F{count}(x: bool) -> bool {{ return Missing(x); }}\n\n")
result = subprocess.run([str(compiler), "protocol-source", str(app)],
                        capture_output=True, text=True, timeout=5)
assert result.returncode > 0 and ": error: source-name-unresolved: " in result.stderr, result.stderr

print("frontend project resolution controls passed")
