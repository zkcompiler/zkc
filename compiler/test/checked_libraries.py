"""Readable checked-library authoring: abstraction before private layout."""
import json

from cases import case
from commands import Commands
from source_text import unlocated
from tools import records

commands = Commands(records())
IDENTITY = 'library(namespace="example", name="cells", version="1", resolution="capture-1");'
INTERFACE = '''interface Cell {
  type Value drop;
  local step(x: Value) -> Value;
}'''
CLIENT = '''fn Client<C: Cell>(x: C::Value) -> C::Value {
  return C::step(x);
}'''
EMPTY = '''component EmptyCell: Cell {
  type Value = ();
  local step(x: Value) -> Value { return x; }
}'''
SCALAR = '''component ScalarCell<F: domain field>: Cell {
  type Value = field<F>;
  local step(x: Value) -> Value { return x; }
}'''
DEMO = f'''module {{ {IDENTITY} {INTERFACE} {CLIENT} {EMPTY} {SCALAR}
  link Empty = Client<EmptyCell>;
  link Scalar = Client<ScalarCell<"koala-bear">>;
}}'''


def run(command, text, refuses=None):
    return commands.source(command, text, refuses=refuses)


def source(text):
    return json.loads(run("protocol-source", text))


with case("readable syntax survives formatting and inspection"):
    before = unlocated(json.loads(run("protocol-parse", DEMO))["content"])
    formatted = run("protocol-format", DEMO)
    after = unlocated(json.loads(run("protocol-parse", formatted))["content"])
    assert before == after
    assert len(after["libraryComponents"]) == 2
    assert after["libraryIdentities"][0]["resolution"] == "capture-1"
    assert len(after["libraryLinks"]) == 2

with case("one abstract client links zero-payload affine and scalar layouts"):
    emitted = run("protocol-source", DEMO)
    assert "resource_unit:" in emitted
    assert "field:koala-bear" in emitted
    assert '"Empty"' in emitted and '"Scalar"' in emitted
    # The portable result must independently survive the ordinary source route.
    assert source(emitted) == json.loads(emitted)

with case("client checks separately without any component declaration"):
    report = json.loads(run("protocol-analyze", f"module {{ {IDENTITY} {INTERFACE} {CLIENT} }}"))
    assert report["state"] == "source_checked"
    assert report["checked_libraries"]["query_state"] == "retained_checked_capabilities"
    assert report["checked_libraries"]["pir_admission"] == "not_requested"

with case("affine duplication fails before selecting a concrete implementation"):
    bad = CLIENT.replace("return C::step(x);", "let y = C::step(x); return C::step(x);")
    run("protocol-source", f"module {{ {IDENTITY} {INTERFACE} {bad} }}", "library-resource-use")

with case("copy permission permits reuse under the public interface"):
    copy = INTERFACE.replace("Value drop", "Value copy drop")
    client = CLIENT.replace("return C::step(x);", "let y = C::step(x); return C::step(x);")
    source(f"module {{ {IDENTITY} {copy} {client} {SCALAR} link Closed = Client<ScalarCell<\"koala-bear\">>; }}")

with case("copy promise cannot be implemented by affine RNG"):
    copy = INTERFACE.replace("Value drop", "Value copy drop")
    affine = SCALAR.replace("field<F>", "rng<F>")
    run("protocol-source", f"module {{ {IDENTITY} {copy} {CLIENT} {affine} link Closed = Client<ScalarCell<\"koala-bear\">>; }}", "library-permission-bound")

with case("typed product projection remains before layout"):
    client = '''fn Client<C: Cell>(x: (C::Value, C::Value)) -> C::Value {
      return C::step(x[1]);
    }'''
    source(f"module {{ {IDENTITY} {INTERFACE} {client} {EMPTY} link Closed = Client<EmptyCell>; }}")

with case("static source array projections preserve distinct resources"):
    client = '''fn Client<C: Cell>(x: Array<C::Value, 2>) -> (C::Value, C::Value) {
      return (C::step(x[0]), C::step(x[1]));
    }'''
    source(f"module {{ {IDENTITY} {INTERFACE} {client} {EMPTY} link Closed = Client<EmptyCell>; }}")

with case("overlapping whole and partial moves fail"):
    client = '''fn Client<C: Cell>(x: Array<C::Value, 2>) -> Array<C::Value, 2> {
      let y = C::step(x[0]); return x;
    }'''
    run("protocol-source", f"module {{ {IDENTITY} {INTERFACE} {client} }}", "library-resource-use")

with case("dynamic array indexing is refused explicitly"):
    client = '''fn Client<C: Cell>(x: Array<C::Value, 2>, n: index) -> C::Value {
      return x[n];
    }'''
    run("protocol-source", f"module {{ {IDENTITY} {INTERFACE} {client} }}", "library-source-index")

with case("sorted associated natural width is typed in the interface"):
    interface = '''interface Views { type View drop; nat Width;
      local forward(x: Array<View, Width>) -> Array<View, Width>;
    }'''
    client = '''fn Client<C: Views>(x: Array<C::View, C::Width>) -> Array<C::View, C::Width> {
      return C::forward(x);
    }'''
    source(f"module {{ {IDENTITY} {interface} {client} }}")

for text, code in [
    (DEMO.replace('resolution="capture-1"', 'mystery="capture-1"'), "library-source-identity"),
    (DEMO.replace("type Value drop", "type Value magical"), "library-source-permission"),
    (DEMO.replace("return C::step(x);", "if true { return x; } return x;"), "library-source-control"),
    (DEMO.replace("return C::step(x);", "let mut y = x; return y;"), "library-source-control"),
    (DEMO.replace("return C::step(x);", "return C::missing(x);"), "library-source-call"),
    (DEMO.replace("Client<EmptyCell>", "Client<Missing>"), "source-name-unresolved"),
    (DEMO.replace("Client<EmptyCell>", "Client<EmptyCell, EmptyCell>"), "library-source-link"),
    (DEMO.replace('ScalarCell<"koala-bear">', "ScalarCell<2>"), "library-static-sort"),
    (DEMO.replace("return C::step(x);", "return x; C::step(x);"), "library-source-return"),
]:
    with case(code + ": " + text[-90:]):
        run("protocol-source", text, code)

# This file's DEMO is also directly reusable as a native demo source; runtime and
# cryptographic equivalence claims are intentionally outside these compiler tests.

with case("unit-result guard remains an installed logical operation"):
    interface = INTERFACE.replace("x: Value", "x: Value, ok: bool").replace("-> Value;", "-> Value effects (local);")
    empty = EMPTY.replace("x: Value", "x: Value, ok: bool").replace("-> Value {", "-> Value effects (local) {").replace("return x;", "control::require(ok); return x;")
    client = CLIENT.replace("x: C::Value", "x: C::Value, ok: bool").replace("-> C::Value {", "-> C::Value effects (local) {").replace("C::step(x)", "C::step(x, ok)")
    emitted = run("protocol-source", f"module {{ {IDENTITY} {interface} {client} {empty} link Closed = Client<EmptyCell>; }}")
    assert "control.require" in emitted
    assert "resource_unit:" in emitted

with case("natural and association parameters remain typed selections"):
    interface = '''interface Views { type View drop; nat Width; association Subject;
      local forward(x: Array<View, Width>) -> Array<View, Width>;
    }'''
    component = '''component ViewsImpl<N: nat, S: association>: Views {
      nat Width = N; association Subject = S; type View = bool;
      local forward(x: Array<View, N>) -> Array<View, N> { return x; }
    }'''
    client = '''fn Client<C: Views>(x: Array<C::View, C::Width>) -> Array<C::View, C::Width> {
      return C::forward(x);
    }'''
    text = f'''module {{ {IDENTITY} association Captured = "relation:exact-subject-1";
      {interface} {component} {client} link Closed = Client<ViewsImpl<2, Captured>>;
    }}'''
    source(text)
    run("protocol-source", text.replace("ViewsImpl<2, Captured>", "ViewsImpl<Captured, 2>"), "library-static-sort")

with case("exact public domain equation rejects a different installed field"):
    interface = '''interface FieldAPI { domain F: field = "koala-bear";
      local step(x: field<F>) -> field<F>;
    }'''
    component = '''component Impl: FieldAPI { domain F: field = "bls12-381.fr";
      local step(x: field<F>) -> field<F> { return x; }
    }'''
    client = '''fn Client<C: FieldAPI>(x: field<C::F>) -> field<C::F> { return C::step(x); }'''
    run("protocol-source", f"module {{ {IDENTITY} {interface} {component} {client} link Closed = Client<Impl>; }}", "library-bound")

with case("explicit component origin is refused rather than discarded"):
    component = EMPTY.replace("-> Value {", "-> Value origin Other() {")
    run("protocol-source", f"module {{ {IDENTITY} {INTERFACE} {component} }}", "library-source-origin")

with case("static-only components retain a captured constructor environment"):
    text = f'''module {{ {IDENTITY}
      interface Marker {{ type Value copy drop; }}
      component BoolMarker: Marker {{ type Value = bool; }}
      fn Client<C: Marker>(x: C::Value) -> C::Value {{ return x; }}
      link Closed = Client<BoolMarker>;
    }}'''
    source(text)

with case("explicit selected backend is not silently discarded"):
    text = f'''module {{ {IDENTITY}
      bind negate = bool::not() using "logical/bool.not";
      interface Bit {{ type Value copy drop; local flip(x: Value) -> Value; }}
      component Impl: Bit {{ type Value = bool;
        local flip(x: Value) -> Value {{ return negate(x); }}
      }}
    }}'''
    run("protocol-source", text, "library-source-implementation")

with case("generic component dependency checks against its bound interface"):
    wrapper = '''component Wrapper<D: Cell>: Cell {
      type Value = D::Value;
      local step(x: Value) -> Value { return D::step(x); }
    }'''
    text = f'''module {{ {IDENTITY} {INTERFACE} {CLIENT} {EMPTY} {wrapper}
      link Closed = Client<Wrapper<EmptyCell>>;
    }}'''
    emitted = run("protocol-source", text)
    assert "resource_unit:" in emitted

with case("component dependency must match the exact declared interface"):
    wrapper = '''component Wrapper<D: Cell>: Cell {
      type Value = D::Value;
      local step(x: Value) -> Value { return D::step(x); }
    }'''
    other = '''interface Other { type Value drop; local step(x: Value) -> Value; }
      component OtherImpl: Other { type Value = bool;
        local step(x: Value) -> Value { return x; }
      }'''
    text = f'''module {{ {IDENTITY} {INTERFACE} {CLIENT} {EMPTY} {wrapper} {other}
      link Closed = Client<Wrapper<OtherImpl>>;
    }}'''
    run("protocol-source", text, "library-interface-drift")

with case("authored occurrence labels cannot silently lose their identity"):
    client = CLIENT.replace("return C::step(x);", "[named] let y = C::step(x); return y;")
    run("protocol-source", f"module {{ {IDENTITY} {INTERFACE} {client} }}", "library-source-site")


NATIVE_DEMO = """module {
  library(namespace="example", name="checked-guards", version="1", resolution="demo-1");
  interface Guarded {
    type Value drop;
    local make(ok: bool) -> Value effects (local);
    local use(x: Value) -> bool effects (local);
  }
  component EmptyGuard: Guarded {
    type Value = ();
    local make(ok: bool) -> Value effects (local) {
      control::require(ok);
      return ();
    }
    local use(x: Value) -> bool effects (local) {
      let zero = index::constant() attributes(0);
      return index::equal(zero, zero);
    }
  }
  component BoolGuard: Guarded {
    type Value = bool;
    local make(ok: bool) -> Value effects (local) {
      control::require(ok);
      return ok;
    }
    local use(x: Value) -> bool effects (local) { return x; }
  }
  fn Client<C: Guarded>(ok: bool) -> bool effects (local) {
    let value = C::make(ok);
    return C::use(value);
  }
  link Empty = Client<EmptyGuard>;
  link Scalar = Client<BoolGuard>;
  protocol RunEmpty {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let accepted = Empty(ok);
    return accepted;
  }
  protocol RunScalar {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let accepted = Scalar(ok);
    return accepted;
  }
  instance EmptyRun: RunEmpty { roles (P = Prover); }
  instance ScalarRun: RunScalar { roles (P = Prover); }
  entry empty = EmptyRun;
  entry scalar = ScalarRun;
}
"""

with case("readable two-layout guarded clients compile through physical PIR"):
    emitted = run("protocol-source", NATIVE_DEMO)
    assert "control.require" in emitted and "resource_unit.create" in emitted
    physical = run("protocol-compile", NATIVE_DEMO)
    assert '"empty"' in physical and '"scalar"' in physical

with case("same-named component members retain distinct origin selectors"):
    origins = json.loads(run("protocol-algorithm-map", NATIVE_DEMO))[2]
    definitions = {row[2] for row in origins}
    assert {'EmptyGuard.make', 'BoolGuard.make'} <= definitions
    assert 'make' not in definitions

with case("pure aliases share while explicit seals distinguish selections"):
    import re
    aliases = f'''module {{ {IDENTITY} {INTERFACE} {EMPTY} {CLIENT}
      select A = EmptyCell; select B = EmptyCell;
      link First = Client<A>; link Second = Client<B>;
    }}'''
    shared = run("protocol-source", aliases)
    assert len(set(re.findall(r"resource_unit:library_slot_[0-9]+", shared))) == 1
    sealed = run("protocol-source", aliases.replace("select A", "seal A").replace("select B", "seal B"))
    assert len(set(re.findall(r"resource_unit:library_slot_[0-9]+", sealed))) == 2

with case("selection alias cycles refuse with a bounded diagnostic"):
    run("protocol-source", f"module {{ {IDENTITY} select A = B; select B = A; }}", "library-source-cycle")

with case("installed primitive work cannot be claimed effect-free"):
    text = f'''module {{ {IDENTITY}
      interface Bit {{ type Value copy drop; local flip(x: Value) -> Value; }}
      component Impl: Bit {{ type Value = bool;
        local flip(x: Value) -> Value {{ return bool::not(x); }}
      }}
    }}'''
    run("protocol-source", text, "library-effect")

with case("unsupported required facets block linking"):
    interface = INTERFACE.replace("type Value drop;", 'type Value drop; facet required "unknown-owner" "security";')
    run("protocol-source", f"module {{ {IDENTITY} {interface} {EMPTY} {CLIENT} link Closed = Client<EmptyCell>; }}", "library-required-facet")

with case("unsupported optional facets are retained without blocking"):
    interface = INTERFACE.replace("type Value drop;", 'type Value drop; facet optional "unknown-owner" "security";')
    source(f"module {{ {IDENTITY} {interface} {EMPTY} {CLIENT} link Closed = Client<EmptyCell>; }}")

with case("supported resource and conservative effect facets check"):
    interface = INTERFACE.replace("type Value drop;", '''type Value drop;
      facet required "zkc.frontend.library" "resources";
      facet required "zkc.frontend.library" "effects";''')
    source(f"module {{ {IDENTITY} {interface} {EMPTY} {CLIENT} link Closed = Client<EmptyCell>; }}")

with case("retained queries expose abstract checks and linked layouts"):
    report = json.loads(run("protocol-analyze", DEMO))["checked_libraries"]
    assert report["query_state"] == "retained_checked_capabilities"
    assert len(report["clients"]) == 1 and len(report["links"]) == 2
    client = report["clients"][0]
    assert client["body"]["inputs"][0]["type"]["kind"] == "abstract"
    assert client["imports"][0]["interface_fingerprint"] == report["interfaces"][0]["fingerprint"]
    layouts = [v for link in report["links"] for fn in link["functions"] for v in fn["layouts"]]
    assert any(leaf["kind"] == "resource_unit" for v in layouts for leaf in v["leaves"])
    assert any(leaf["kind"] == "logical" for v in layouts for leaf in v["leaves"])
    moved = json.loads(run("protocol-analyze", "\n\n" + DEMO))["checked_libraries"]
    assert moved["clients"][0]["fingerprint"] == client["fingerprint"]

with case("optional facet evidence stays unavailable in immutable link query"):
    interface = INTERFACE.replace("type Value drop;", 'type Value drop; facet optional "unknown-owner" "security";')
    report = json.loads(run("protocol-analyze", f"module {{ {IDENTITY} {interface} {EMPTY} {CLIENT} link Closed = Client<EmptyCell>; }}"))["checked_libraries"]
    assert report["links"][0]["evidence"][0]["state"] == "unavailable"

with case("nominal records construct and project before private layout"):
    text = f'''module {{ {IDENTITY}
      struct Box {{ value: bool }}
      interface Boxes {{ type Value copy drop;
        local pack(x: bool) -> Value; local unpack(x: Value) -> bool;
      }}
      component Impl: Boxes {{ type Value = Box;
        local pack(x: bool) -> Value {{ return Box {{ value: x }}; }}
        local unpack(x: Value) -> bool {{ return x.value; }}
      }}
      fn Client<C: Boxes>(x: bool) -> bool {{ return C::unpack(C::pack(x)); }}
      link Closed = Client<Impl>;
    }}'''
    source(text)
    report = json.loads(run("protocol-analyze", text))["checked_libraries"]
    assert report["component_bodies"][0]["body"]["instructions"][0]["output"]["type"]["kind"] == "record"

with case("equal record layouts do not erase nominal mismatch"):
    text = f'''module {{ {IDENTITY}
      struct A {{ value: bool }} struct B {{ value: bool }}
      interface Boxes {{ type Value copy drop; local pack(x: bool) -> Value; }}
      component Impl: Boxes {{ type Value = A;
        local pack(x: bool) -> Value {{ return B {{ value: x }}; }}
      }}
    }}'''
    run("protocol-source", text, "library-type-mismatch")

with case("effect declarations cannot silently extend ordinary source functions"):
    run("protocol-source", 'module { fn Ordinary(x: bool) -> bool effects (local) { return x; } }', "source-effects")

with case("a client must declare its imported member effect"):
    interface = INTERFACE.replace("-> Value;", "-> Value effects (local);")
    run("protocol-source", f"module {{ {IDENTITY} {interface} {CLIENT} }}", "library-effect")


GROUP_DEMO = """module {
  library(namespace="example", name="groups", version="1", resolution="group-case");
  interface GroupAPI {
    domain G: group;
    domain F: field = G::Scalar;
    local scalar(x: field<F>) -> field<F>;
  }
  component GroupImpl<H: domain group>: GroupAPI {
    domain G: group = H;
    domain F: field = H::Scalar;
    local scalar(x: field<F>) -> field<F> { return x; }
  }
  fn Client<C: GroupAPI>(x: field<C::F>) -> field<C::F> { return C::scalar(x); }
  link Closed = Client<GroupImpl<"ristretto255.group">>;
}
"""

with case("group scalar equation links using installed associated-domain truth"):
    emitted = run("protocol-source", GROUP_DEMO)
    assert "field:ristretto255.scalar" in emitted
    run("protocol-admit", GROUP_DEMO)

with case("unequal selected scalar domain refuses despite the field constructor"):
    mismatched = GROUP_DEMO.replace("domain F: field = H::Scalar;", 'domain F: field = "bls12-381.fr";')
    run("protocol-source", mismatched, "library-bound")


# Declaration conformance must hold under parameter bounds, before any selected
# representation is available, including unused declarations and parameters.
UPGRADE = f'''module {{ {IDENTITY}
  interface Affine {{ type Value drop; local step(x: Value) -> Value; }}
  interface Copyable {{ type Value copy drop; local step(x: Value) -> Value; }}
  component Base: Affine {{ type Value = bool;
    local step(x: Value) -> Value {{ return x; }}
  }}
  component Upgrade<D: Affine>: Copyable {{ type Value = D::Value;
    local step(x: Value) -> Value {{ return D::step(x); }}
  }}
  fn Client<C: Copyable>(x: C::Value) -> (C::Value, C::Value) {{
    return (C::step(x), C::step(x));
  }}
  link Closed = Client<Upgrade<Base>>;
}}'''

for selected in (False, True):
    with case(f"affine dependency cannot export copy through bool storage, selected={selected}"):
        text = UPGRADE if selected else UPGRADE.replace("link Closed = Client<Upgrade<Base>>;", "")
        run("protocol-source", text, "library-permission-bound")

with case("unused methodless component cannot strengthen dependency permissions"):
    text = f'''module {{ {IDENTITY}
      interface Affine {{ type Value drop; }}
      interface Copyable {{ type Value copy drop; }}
      component Upgrade<D: Affine>: Copyable {{ type Value = D::Value; }}
    }}'''
    run("protocol-source", text, "library-permission-bound")

METHODLESS_BOUND = f'''module {{ {IDENTITY}
  interface Need {{ type Value copy drop; }}
  interface Other {{ type Value drop; }}
  interface Marker {{ type Value copy drop; }}
  component Wrong: Other {{ type Value = bool; }}
  component Right: Need {{ type Value = bool; }}
  component Wrap<D: Need>: Marker {{ type Value = bool; }}
  fn Client<C: Marker>(x: C::Value) -> C::Value {{ return x; }}
  link Closed = Client<Wrap<Wrong>>;
}}'''

with case("unused parameter interface bound survives a methodless selection"):
    run("protocol-source", METHODLESS_BOUND, "library-interface-drift")

with case("methodless selection with the exact unused bound links"):
    source(METHODLESS_BOUND.replace("Wrap<Wrong>", "Wrap<Right>"))

with case("parameter bound persists when existing methods do not use it"):
    text = METHODLESS_BOUND.replace(
        "interface Marker { type Value copy drop; }",
        "interface Marker { type Value copy drop; local id(x: Value) -> Value; }",
    ).replace(
        "component Wrap<D: Need>: Marker { type Value = bool; }",
        "component Wrap<D: Need>: Marker { type Value = bool; local id(x: Value) -> Value { return x; } }",
    )
    run("protocol-source", text, "library-interface-drift")

with case("unselected component must match interface signatures"):
    text = f'''module {{ {IDENTITY}
      interface I {{ local f(x: bool) -> bool; }}
      component Bad: I {{ local f(x: index) -> index {{ return x; }} }}
    }}'''
    run("protocol-source", text, "library-type-mismatch")

with case("unselected component must define the complete interface member set"):
    text = f'''module {{ {IDENTITY}
      interface I {{ local f(x: bool) -> bool; }}
      component Bad: I {{}}
    }}'''
    run("protocol-source", text, "library-conformance")

with case("convenient selected domain cannot repair a nonparametric signature"):
    text = f'''module {{ {IDENTITY}
      interface I {{ domain F: field; local f(x: field<F>) -> field<F>; }}
      component Bad<H: domain field>: I {{ domain F: field = "koala-bear";
        local f(x: field<H>) -> field<H> {{ return x; }}
      }}
      fn Client<C: I>(x: field<C::F>) -> field<C::F> {{ return C::f(x); }}
      link Closed = Client<Bad<"koala-bear">>;
    }}'''
    run("protocol-source", text, "library-type-mismatch")

# Nominal source equality must not follow equal private storage.
NOMINAL_FORGERY = f'''module {{ {IDENTITY}
  interface Token {{ type V drop; local spend(x: V) -> bool; }}
  component TokenImpl: Token {{ type V = bool;
    local spend(x: V) -> bool {{ return x; }}
  }}
  interface Wrapper {{ type S copy drop;
    local wrap(x: bool) -> S; local leak(x: S) -> bool;
  }}
  component W<D: Token>: Wrapper {{ type S = bool;
    local wrap(x: bool) -> S {{ return x; }}
    local leak(x: D::V) -> bool {{ return D::spend(x); }}
  }}
  fn Client<C: Wrapper>(x: bool) -> bool {{ return C::leak(C::wrap(x)); }}
  link Closed = Client<W<TokenImpl>>;
}}'''

for selected in (False, True):
    with case(f"own bool storage cannot forge a dependency token signature, selected={selected}"):
        text = NOMINAL_FORGERY if selected else NOMINAL_FORGERY.replace("link Closed = Client<W<TokenImpl>>;", "")
        run("protocol-source", text, "library-type-mismatch")

with case("lawful copy wrapper uses only the dependency's public permission"):
    source(UPGRADE.replace("interface Affine { type Value drop;", "interface Affine { type Value copy drop;"))

with case("methodless component query retains unused parameter obligations"):
    text = METHODLESS_BOUND.replace("link Closed = Client<Wrap<Wrong>>;", "")
    report = json.loads(run("protocol-analyze", text))["checked_libraries"]
    assert report["unselected_component_conformance"] == "checked_parametric"
    assert report["links"] == [] and report["component_bodies"] == []
    components = {c["name"]: c for c in report["components"]}
    assert set(components) == {"Wrong", "Right", "Wrap"}
    wrapper = components["Wrap"]
    assert wrapper["state"] == "checked_parametric" and wrapper["fingerprint"]
    assert wrapper["functions"] == []
    assert wrapper["type_bounds"] == [] and wrapper["requirements"] == []
    assert len(wrapper["imports"]) == 1
    bound = wrapper["imports"][0]
    need = next(i for i in report["interfaces"] if i["name"] == "Need")
    assert bound["parameter"]["declaration"]["name"] == "D"
    assert bound["interface_fingerprint"] == need["fingerprint"]
    assert need["types"][0]["copy"] and need["types"][0]["drop"]
    moved = json.loads(run("protocol-analyze", "\n\n" + text))["checked_libraries"]
    assert moved["components"] == report["components"]
    changed = json.loads(run("protocol-analyze", text.replace("Wrap<D: Need>", "Wrap<D: Other>")))["checked_libraries"]
    changed_wrapper = next(c for c in changed["components"] if c["name"] == "Wrap")
    assert changed_wrapper["fingerprint"] != wrapper["fingerprint"]
    assert changed_wrapper["imports"][0]["interface_fingerprint"] != bound["interface_fingerprint"]

with case("unused generic group declaration retains its checked static equations"):
    text = GROUP_DEMO.replace('link Closed = Client<GroupImpl<"ristretto255.group">>;', "")
    report = json.loads(run("protocol-analyze", text))["checked_libraries"]
    component = report["components"][0]
    assert component["state"] == "checked_parametric" and component["fingerprint"]
    assert component["interface_fingerprint"] == report["interfaces"][0]["fingerprint"]
    scalar = next(s["value"] for s in component["statics"] if s["name"] == "F")
    assert scalar["kind"] == "project" and scalar["member"] == "Scalar"
    assert component["functions"][0]["fingerprint"] == report["component_bodies"][0]["fingerprint"]

with case("methodless wrapper derives group equation from its parameter interface"):
    text = f'''module {{ {IDENTITY}
      interface GroupAPI {{ domain G: group; domain F: field = G::Scalar; }}
      component GroupImpl<H: domain group>: GroupAPI {{
        domain G: group = H; domain F: field = H::Scalar;
      }}
      component Wrapper<D: GroupAPI>: GroupAPI {{
        domain G: group = D::G; domain F: field = D::F;
      }}
      fn Client<C: GroupAPI>(x: field<C::F>) -> field<C::F> {{ return x; }}
      link Closed = Client<Wrapper<GroupImpl<"ristretto255.group">>>;
    }}'''
    assert "field:ristretto255.scalar" in run("protocol-source", text)

with case("seal retains Self-rooted member signatures under static substitution"):
    text = f'''module {{ {IDENTITY}
      interface I {{ domain F: field; local step(x: field<F>) -> field<F>; }}
      component Impl<H: domain field>: I {{ domain F: field = H;
        local step(x: field<Self::F>) -> field<Self::F> {{ return x; }}
      }}
      fn Client<C: I>(x: field<C::F>) -> field<C::F> {{ return C::step(x); }}
      seal A = Impl<"koala-bear">;
      select B = Impl<"koala-bear">;
      link Sealed = Client<A>;
      link Plain = Client<B>;
    }}'''
    emitted = run("protocol-source", text)
    assert "field:koala-bear" in emitted and '"Sealed"' in emitted and '"Plain"' in emitted
    reversed_links = text.replace(
        "link Sealed = Client<A>;\n      link Plain = Client<B>;",
        "link Plain = Client<B>;\n      link Sealed = Client<A>;",
    )
    run("protocol-source", reversed_links)

with case("unsupported required facets refuse even on unselected components"):
    interface = INTERFACE.replace("type Value drop;", 'type Value drop; facet required "unknown-owner" "security";')
    run("protocol-source", f"module {{ {IDENTITY} {interface} {EMPTY} }}", "library-required-facet")

# Checked call contracts preserve the authored API independently of private
# binder names, flattened storage, and the order in which declarations appear.
HELPERS = f'''module {{ {IDENTITY} {INTERFACE} {EMPTY}
  fn Client<C: Cell>(state: C::Value) -> C::Value {{
    return Helper::<C>(state: state);
  }}
  fn Helper<D: Cell>(state: D::Value) -> D::Value {{
    return D::step(x: state);
  }}
  link Closed = Client<EmptyCell>;
}}'''

with case("checked source helper composes before private body selection"):
    emitted = run("protocol-source", HELPERS)
    assert '"Helper"' in emitted and '"Closed"' in emitted
    assert "resource_unit:" in emitted
    run("protocol-admit", HELPERS)

with case("helper inference reads a rigid abstract head"):
    run("protocol-source", HELPERS.replace("Helper::<C>", "Helper"))

with case("unselected helper still checks its resource use"):
    bad = HELPERS.replace("return D::step(x: state);", "let used = D::step(x: state); return state;")
    run("protocol-source", bad.replace("link Closed = Client<EmptyCell>;", ""), "library-resource-use")

with case("recursive helper graph refuses before selection"):
    run("protocol-source", HELPERS.replace("return D::step(x: state);", "return Client::<D>(state: state);").replace("link Closed = Client<EmptyCell>;", ""), "library-call-cycle")

with case("an external helper declaration cannot supply an executable body"):
    run("protocol-source", HELPERS.replace("{\n    return D::step(x: state);\n  }", "external;"), "library-open-call")

with case("helper static actual must preserve its exact interface bound"):
    other = "interface Other { type Value drop; }"
    run("protocol-source", HELPERS.replace(INTERFACE, INTERFACE + other).replace("Helper<D: Cell>", "Helper<D: Other>").replace("return D::step(x: state);", "return state;"), "library-interface-drift")

with case("a helper's component actual is one the caller imports, reported at the call"):
    def located(text, code, at):
        """Refused with `code`, at the line holding the text `at`."""
        run("protocol-source", text, code)
        said = commands.attempt([commands.tool, "protocol-source", "-"], stdin=text).stderr
        line = text[:text.index(at)].count("\n") + 1
        assert said.startswith(f"-:{line}:"), said

    located(HELPERS.replace("Helper::<C>(state: state)", "Helper::<EmptyCell>(state: state)"),
            "library-component-actual", "Helper::<EmptyCell>")
    # An interface mismatch keeps its own identifier, and is also at the call.
    other = "interface Other { type Value drop; }"
    located(HELPERS.replace(INTERFACE, INTERFACE + other).replace(
                "Helper<D: Cell>", "Helper<D: Other>").replace("return D::step(x: state);", "return state;"),
            "library-interface-drift", "Helper::<C>")

with case("a sealed alias that selects no component is refused at the alias"):
    text = HELPERS.replace("link Closed = Client<EmptyCell>;", 'link Closed = Client<EmptyCell>;\n  seal A = "koala-bear";')
    run("protocol-source", text, "library-source-selection")
    said = commands.attempt([commands.tool, "protocol-source", "-"], stdin=text).stderr
    line = text[:text.index("seal A")].count("\n") + 1
    assert said.startswith(f"-:{line}:"), said

with case("ordinary helpers acquire a checked callable and body contract"):
    text = f'''module {{ {IDENTITY}
      interface Marker {{ }} component M: Marker {{ }}
      fn Client<C: Marker>(value: bool) -> bool {{ return Identity(value: value); }}
      fn Identity(value: bool) -> bool {{ return value; }}
      link Closed = Client<M>;
    }}'''
    run("protocol-source", text)
    run("protocol-source", text.replace("return value;", "return bool::not(value);"), "library-effect")

NAMED = f'''module {{ {IDENTITY}
  interface Pair {{ local choose(left: bool, right: bool) -> bool; }}
  component Impl: Pair {{
    local choose(privateLeft: bool, privateRight: bool) -> bool {{ return privateLeft; }}
  }}
  fn Client<C: Pair>(a: bool, b: bool) -> bool {{ return C::choose(right: b, left: a); }}
  link Closed = Client<Impl>;
  fn Use(x: bool, y: bool) -> bool {{ return Closed(b: y, a: x); }}
}}'''

with case("interface and closed-link labels survive different private binders"):
    run("protocol-source", NAMED)
    run("protocol-admit", NAMED)

for arguments in ("unknown: b, left: a", "left: b, left: a", "b, left: a", "left: a"):
    with case(f"checked call refuses invalid argument bijection {arguments}"):
        run("protocol-source", NAMED.replace("right: b, left: a", arguments), "library-source-argument-name")

with case("installed positional operation does not acquire guessed labels"):
    text = f'''module {{ {IDENTITY}
      interface Marker {{ }}
      fn Client<C: Marker>(value: bool) -> bool effects (local) {{ return bool::not(value: value); }}
    }}'''
    run("protocol-source", text, "library-source-argument-name")

with case("named argument expected types precede empty aggregate construction"):
    text = f'''module {{ {IDENTITY}
      interface I {{ local f(items: Array<bool, 0>, flag: bool) -> bool; }}
      component Impl: I {{ local f(xs: Array<bool, 0>, b: bool) -> bool {{ return b; }} }}
      fn Client<C: I>(value: bool) -> bool {{ return C::f(flag: value, items: []); }}
      link Closed = Client<Impl>;
    }}'''
    run("protocol-source", text)

with case("closed aggregate argument binds its logical label before flattening"):
    text = f'''module {{ {IDENTITY}
      interface Marker {{ }} component M: Marker {{ }}
      fn Client<C: Marker>(pair: (bool, bool), flag: bool) -> (bool, bool) {{ return pair; }}
      link Closed = Client<M>;
      fn Use(a: bool, b: bool) -> (bool, bool) {{ return Closed(flag: b, pair: (a, b)); }}
    }}'''
    run("protocol-source", text)
    run("protocol-admit", text)
    run("protocol-source", text.replace("flag: b, pair: (a, b)", "v0_0: a, v0_1: b, flag: b"), "source-argument-name")

with case("named argument permutation cannot duplicate an affine input"):
    text = f'''module {{ {IDENTITY}
      interface I {{ type V drop; local f(first: V, second: V) -> V; }}
      fn Client<C: I>(value: C::V) -> C::V {{ return C::f(second: value, first: value); }}
    }}'''
    run("protocol-source", text, "library-resource-use")

ORDERED = f'''module {{ {IDENTITY}
  interface Two {{ local choose(left: bool, right: bool) -> bool; }}
  component Impl: Two {{ local choose(a: bool, b: bool) -> bool {{ return a; }} }}
  fn Client<C: Two>(x: bool, y: bool) -> bool effects (local) {{
    return C::choose(right: First(x), left: Second(y));
  }}
  fn First(value: bool) -> bool effects (local) {{ return bool::not(value); }}
  fn Second(value: bool) -> bool effects (local) {{ return bool::not(value); }}
  link Closed = Client<Impl>;
}}'''

with case("named operands evaluate exactly once in written order before permutation"):
    emitted = source(ORDERED)
    functions = {row[1]: row for row in emitted[2] if row[0] == "function"}
    calls = [row for row in functions["Closed"][4] if row[0] == "apply"]
    assert [functions[row[2]][5][0] for row in calls] == ["First", "Second", "Impl.choose"]
    assert calls[-1][4] == [calls[1][5][0], calls[0][5][0]]

with case("a stopping first named operand suppresses every later operand"):
    stopped = ORDERED.replace("fn First(value: bool) -> bool effects (local) { return bool::not(value); }", "fn First(value: bool) -> bool effects (local) { stop abort; }")
    emitted = source(stopped)
    functions = {row[1]: row for row in emitted[2] if row[0] == "function"}
    calls = [row for row in functions["Closed"][4] if row[0] == "apply"]
    assert [functions[row[2]][5][0] for row in calls] == ["First"]
    run("protocol-admit", stopped)

with case("a helper's declared effects cannot be omitted by its caller"):
    run("protocol-source", ORDERED.replace("Client<C: Two>(x: bool, y: bool) -> bool effects (local)", "Client<C: Two>(x: bool, y: bool) -> bool"), "library-effect")

with case("installed roots have the same owner across author libraries"):
    def installed_roots(value):
        if isinstance(value, dict):
            if value.get("module") == ["installed"]:
                yield value
            for item in value.values():
                yield from installed_roots(item)
        elif isinstance(value, list):
            for item in value:
                yield from installed_roots(item)
    text = f'''module {{ {IDENTITY}
      interface Field {{ domain F: field = "koala-bear"; }}
    }}'''
    left = list(installed_roots(json.loads(run("protocol-analyze", text))))
    right = list(installed_roots(json.loads(run("protocol-analyze", text.replace('name="cells"', 'name="other"')))))
    assert left and right and left == right
    assert {root["library"] for root in left} == {"installed-contracts"}

with case("helper natural and domain arguments infer from typed structural dimensions"):
    text = f'''module {{ {IDENTITY}
      interface Marker {{ }} component M: Marker {{ }}
      fn Client<C: Marker>(values: Array<field<"koala-bear">, 2>) -> Array<field<"koala-bear">, 2> {{ return Echo(values: values); }}
      fn Echo<F: domain field, N: nat>(values: Array<field<F>, N>) -> Array<field<F>, N> {{ return values; }}
      link Closed = Client<M>;
    }}'''
    run("protocol-source", text)
    run("protocol-admit", text)
    mismatched = text.replace("Client<C: Marker>", "Client<C: Marker, N: nat>").replace('Array<field<"koala-bear">, 2>', 'Array<field<"koala-bear">, N>').replace("Client<M>", "Client<M, 2>").replace("Echo(values:", 'Echo::<"bls12-381.fr", N>(values:')
    run("protocol-source", mismatched, "library-type-mismatch")

with case("a source helper cannot silently replace an installed primitive"):
    text = f'''module {{ {IDENTITY}
      interface Marker {{ }}
      fn Client<C: Marker>(value: bool) -> bool effects (local) {{ return bool::not(value); }}
      fn "bool.not"(value: bool) -> bool {{ return value; }}
    }}'''
    report = json.loads(run("protocol-analyze", text))
    assert report["state"] == "source_checked", report
    clients = report["checked_libraries"]["clients"]
    client = next(c for c in clients if c["display_name"] == "Client")
    calls = [i for i in client["body"]["instructions"] if i["kind"] == "call"]
    assert calls[0]["target"]["operation"] == "bool.not", calls
    helper = json.loads(run("protocol-analyze", text.replace("bool::not(value)", '\"bool.not\"(value)')))
    assert helper["state"] == "source_checked", helper
    client = next(c for c in helper["checked_libraries"]["clients"] if c["display_name"] == "Client")
    calls = [i for i in client["body"]["instructions"] if i["kind"] == "call"]
    assert calls[0]["target"]["function"]["name"] == "bool.not", calls

with case("component members cannot silently shadow installed operation namespaces"):
    text = f'''module {{ {IDENTITY}
      interface Bits {{ local not(value: bool) -> bool; }}
      fn Client<bool: Bits>(value: bool) -> bool {{ return bool::not(value); }}
    }}'''
    run("protocol-source", text, "library-source-call-ambiguity")
    run("protocol-source", text.replace("<bool: Bits>", "<C: Bits>").replace("bool::not", "C::not"))

with case("named enum operands receive the matched formal's expected type"):
    text = f'''module {{ {IDENTITY}
      enum Flag {{ Off(), On(bool) }}
      interface I {{ local choose(value: Flag, ok: bool) -> bool; }}
      component Impl: I {{ local choose(v: Flag, b: bool) -> bool {{ return b; }} }}
      fn Client<C: I>(ok: bool) -> bool {{ return C::choose(ok: ok, value: Flag::Off()); }}
      link Closed = Client<Impl>;
    }}'''
    run("protocol-source", text)
    run("protocol-source", text.replace("value: Flag::Off()", "unknown: Flag::Off()"), "library-source-argument-name")

with case("closed variant aggregates retain the existing admitted carrier path"):
    text = f'''module {{ {IDENTITY}
      enum Flag {{ Off(), On(bool) }}
      interface Marker {{ }} component M: Marker {{ }}
      fn Client<C: Marker>(pair: (Flag, bool)) -> (Flag, bool) {{ return pair; }}
      link Closed = Client<M>;
    }}'''
    emitted = run("protocol-source", text)
    assert "variant:" in emitted
    run("protocol-admit", text)

with case("an external helper signature supports checking without executable linking"):
    text = HELPERS.replace("{\n    return D::step(x: state);\n  }", "external;").replace("link Closed = Client<EmptyCell>;", "")
    run("protocol-source", text)

with case("an explicit link root forms a domain-generic checked callable"):
    text = f'''module {{ {IDENTITY}
      fn Echo<F: domain field>(value: field<F>) -> field<F> {{ return value; }}
      link Closed = Echo<"koala-bear">;
      fn Use(value: "koala-bear"::Element) -> "koala-bear"::Element {{ return Closed(value: value); }}
    }}'''
    run("protocol-source", text)
    run("protocol-admit", text)
