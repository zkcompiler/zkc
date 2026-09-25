"""Lexical finite traversals, captures, and ordered expected argument binding."""
import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())
IDENTITY = 'library(namespace="test", name="authoring", version="1", resolution="fixture");'
MARKER = 'interface Marker {} component Selected: Marker {}'


def run(text, refuses=None, command="protocol-source"):
    return commands.source(command, text, refuses=refuses)


def module(body):
    return f'module {{ {IDENTITY} {MARKER} {body} }}'


def accepted(text):
    emitted = run(text)
    assert json.loads(run(emitted)) == json.loads(emitted)
    run(text, command="protocol-admit")
    return json.loads(emitted)


def functions(emitted):
    return {row[1]: row for row in emitted[2] if row[0] == "function"}


def forwarded_returns(fns, name, inputs):
    """Follow only pure forwarding calls; any primitive work fails this check."""
    fn = fns[name]
    values = dict(zip((port[0] for port in fn[2]), inputs))
    for row in fn[4]:
        if row[0] == "return":
            return [values[value] for value in row[1]]
        assert row[0] == "apply", row
        results = forwarded_returns(fns, row[2], [values[value] for value in row[4]])
        values.update(zip(row[5], results))
    raise AssertionError("forwarding body must return")


for count in (0, 1, 3):
    with case(f"map collects {count} ordered elements with a free challenge"):
        text = module(f'''
          fn Client<C: Marker>(items: Array<bool, {count}>, challenge: bool)
              -> Array<bool, {count}> effects (local) {{
            return map items |item| {{ bool::and(item, challenge) }};
          }}
          link Closed = Client<Selected>;
        ''')
        emitted = accepted(text)
        # Literal expansion is bounded; no closure or traversal enters PIR.
        assert '"map"' not in json.dumps(emitted)
        bindings = {row[0]: row[1] for row in emitted[1]}
        # The source bridge may expose an aggregate wrapper; primitive counts
        # are therefore measured across all selected functions.
        all_ops = [row for fn in functions(emitted).values() for row in fn[4]
                   if row[0] == "op" and bindings.get(row[2]) == "bool.and"]
        assert len(all_ops) == count

    with case(f"fold preserves ordered calls and initial state for {count} trips"):
        text = module(f'''
          fn Step(state: bool, item: bool) -> bool effects (local) {{
            return bool::and(state, item);
          }}
          fn Client<C: Marker>(items: Array<bool, {count}>, initial: bool) -> bool effects (local) {{
            return fold items with initial |state, item| {{ Step(item: item, state: state) }};
          }}
          link Closed = Client<Selected>;
        ''')
        emitted = accepted(text)
        fns = functions(emitted)
        calls = [row for fn in fns.values() for row in fn[4]
                 if row[0] == "apply" and fns[row[2]][5][0].endswith("Step")]
        assert len(calls) == count
        if count == 0:
            closed = fns["Closed"]
            assert closed[4][-1][0] == "return"
            assert forwarded_returns(fns, "Closed", ["initial"]) == ["initial"]

for count in (0, 1, 3):
    with case(f"terminal map suppresses remaining trips and calls for {count} trips"):
        text = module(f'''
          fn Client<C: Marker>(items: Array<bool, {count}>, after: bool) -> bool effects (local) {{
            let mapped: Array<bool, {count}> = map items |item| {{ stop abort; }};
            return bool::not(after);
          }}
          link Closed = Client<Selected>;
        ''')
        emitted = accepted(text)
        bodies = [fn[4] for fn in functions(emitted).values()]
        assert any(row[0] == "stop" for body in bodies for row in body) == (count != 0)
        if count:
            assert all(row[0] != "op" for body in bodies for row in body)

with case("lexical steps use the same selected helper and branch capture rules"):
    accepted(module('''
      fn Client<C: Marker>(items: Array<bool, 2>, z: bool, a: bool) -> Array<bool, 2> {
        return map items |item| {
          if item -> (next) { yield z; } else { yield a; }
          next
        };
      }
      link Closed = Client<Selected>;
    '''))

with case("nested map and fold infer captures through lexical step scopes"):
    accepted(module('''
      fn Client<C: Marker>(items: Array<Array<bool, 2>, 2>, initial: bool) -> Array<bool, 2> effects (local) {
        return map items |row| {
          fold row with initial |state, item| { bool::and(state, item) }
        };
      }
      link Closed = Client<Selected>;
    '''))

with case("empty map checks its body even though no step executes"):
    run(module('''
      fn Client<C: Marker>(items: Array<bool, 0>, x: bool) -> Array<bool, 0> {
        return map items |item| { bool::not(item) };
      }
      link Closed = Client<Selected>;
    '''), "library-effect")

with case("fold rejects a state type change"):
    run(module('''
      fn Client<C: Marker>(items: Array<bool, 2>, initial: ()) -> () {
        return fold items with initial |state, item| { item };
      }
      link Closed = Client<Selected>;
    '''), "library-source-traversal")

with case("map requires a finite array rather than an arbitrary product"):
    run(module('''
      fn Client<C: Marker>(items: (bool, bool)) -> Array<bool, 2> {
        return map items |item| { item };
      }
      link Closed = Client<Selected>;
    '''), "library-source-traversal")

AFFINE = '''
  interface Cell { type Value drop; local step(x: Value) -> Value; }
  component Empty: Cell { type Value = (); local step(x: Value) -> Value { return x; } }
'''
for count in (0, 1, 2):
    with case(f"affine invariant capture refuses even for {count} trips"):
        run(f'''module {{ {IDENTITY} {AFFINE}
          fn Client<C: Cell>(items: Array<bool, {count}>, resource: C::Value) -> Array<C::Value, {count}> {{
            return map items |item| {{ C::step(resource) }};
          }}
          link Closed = Client<Empty>;
        }}''', "library-traversal-capture")

with case("array element consumption remains affine inside lexical map"):
    run(f'''module {{ {IDENTITY} {AFFINE}
      fn Client<C: Cell>(items: Array<C::Value, 2>) -> Array<(C::Value, C::Value), 2> {{
        return map items |item| {{ (item, item) }};
      }}
      link Closed = Client<Empty>;
    }}''', "library-resource-use")

with case("affine map and fold preserve zero-storage resource transfers"):
    accepted(f'''module {{ {IDENTITY} {AFFINE}
      fn Client<C: Cell>(items: Array<C::Value, 2>) -> Array<C::Value, 2> {{
        return map items |item| {{ C::step(item) }};
      }}
      link Closed = Client<Empty>;
    }}''')

with case("ordinary named arguments receive expected types before empty literals"):
    accepted('''module {
      fn Choose(flag: bool, items: Indices) -> bool { return flag; }
      fn Use(flag: bool) -> bool { return Choose(items: [], flag: flag); }
    }''')

with case("ordinary positional arguments receive the same expected types"):
    accepted('''module {
      fn Choose(flag: bool, items: Indices) -> bool { return flag; }
      fn Use(flag: bool) -> bool { return Choose(flag, []); }
    }''')

with case("ordinary generic operand heads determine expected empty vector type"):
    accepted('''module {
      fn Choose<F: Field>(flag: F::Element, items: Vector<F::Element>) -> F::Element { return flag; }
      fn Use(flag: "koala-bear"::Element) -> "koala-bear"::Element {
        return Choose(items: [], flag: flag);
      }
    }''')

for args in ("flag: flag, flag: flag", "unknown: flag, items: []", "flag, items: []", "flag: flag"):
    with case(f"ordinary invalid label bijection refuses before operands: {args}"):
        run(f'''module {{
          fn Choose(flag: bool, items: Indices) -> bool {{ return flag; }}
          fn Use(flag: bool) -> bool {{ return Choose({args}); }}
        }}''', "source-argument-name")

with case("ordinary function traversals enter the checked finite traversal owner"):
    accepted('''module {
      fn Map(items: Array<bool, 2>) -> Array<bool, 2> effects (local) {
        return map items |item| { bool::not(item) };
      }
      fn Fold(items: Array<bool, 2>, initial: bool) -> bool effects (local) {
        return fold items with initial |state, item| { bool::and(state, item) };
      }
    }''')

with case("free aggregate places leave unrelated affine siblings available"):
    accepted(f'''module {{ {IDENTITY} {AFFINE}
      fn Client<C: Cell>(items: Array<bool, 2>, held: (bool, C::Value))
          -> (Array<bool, 2>, C::Value) {{
        let mapped = map items |item| {{ held[0] }};
        return (mapped, held.1);
      }}
      link Closed = Client<Empty>;
    }}''')

with case("nested projected captures resolve without capturing whole parents"):
    accepted(module('''
      fn Client<C: Marker>(items: Array<bool, 2>, held: ((bool, bool), bool)) -> Array<bool, 2> {
        return map items |item| { held[0][1] };
      }
      link Closed = Client<Selected>;
    '''))

with case("literal Boolean fold initial uses existing operations"):
    accepted(module('''
      fn Client<C: Marker>(items: Array<bool, 2>) -> bool effects (local) {
        return fold items with false |state, item| { bool::or(state, item) };
      }
      link Closed = Client<Selected>;
    '''))

with case("map refuses a mismatched expected element type"):
    run(module('''
      fn Client<C: Marker>(items: Array<bool, 2>) -> Array<(), 2> {
        return map items |item| { item };
      }
      link Closed = Client<Selected>;
    '''), "library-source-traversal")

with case("checked named arguments inside a lexical step bind expected empty arrays"):
    accepted(module('''
      fn Choose(flag: bool, empty: Array<bool, 0>) -> bool { return flag; }
      fn Client<C: Marker>(items: Array<bool, 2>) -> Array<bool, 2> {
        return map items |item| { Choose(empty: [], flag: item) };
      }
      link Closed = Client<Selected>;
    '''))


def rows(value, kind):
    if isinstance(value, dict):
        if value.get("kind") == kind:
            yield value
        for child in value.values():
            yield from rows(child, kind)
    elif isinstance(value, list):
        for child in value:
            yield from rows(child, kind)


with case("capture order is authored first use rather than alphabetical"):
    report = json.loads(run(module('''
      fn Client<C: Marker>(items: Array<bool, 2>, z: bool, a: bool) -> Array<bool, 2> effects (local) {
        return map items |item| { bool::and(z, a) };
      }
      link Closed = Client<Selected>;
    '''), command="protocol-analyze"))
    traversals = list(rows(report, "array_traversal"))
    assert traversals
    assert traversals[0]["captures"] == [{"value": 1, "path": []}, {"value": 2, "path": []}]

with case("capture deduplication identifies equivalent literal places"):
    report = json.loads(run(module('''
      fn Client<C: Marker>(items: Array<bool, 2>, held: (bool, bool)) -> Array<bool, 2> effects (local) {
        return map items |item| { bool::and(held.0, held[0]) };
      }
      link Closed = Client<Selected>;
    '''), command="protocol-analyze"))
    traversals = list(rows(report, "array_traversal"))
    assert traversals[0]["captures"] == [{"value": 1, "path": [0]}]

for count in (0, 1, 3):
    with case(f"affine fold threads its initial resource for {count} trips"):
        accepted(f'''module {{ {IDENTITY} {AFFINE}
          fn Client<C: Cell>(items: Array<bool, {count}>, initial: C::Value) -> C::Value {{
            return fold items with initial |state, item| {{ C::step(state) }};
          }}
          link Closed = Client<Empty>;
        }}''')

with case("resolved aliases share one inferred affine capture across exclusive arms"):
    accepted(f'''module {{ {IDENTITY} {AFFINE}
      fn Client<C: Cell>(flag: bool, resource: C::Value) -> C::Value {{
        let alias = resource;
        if flag -> (result) {{ yield alias; }} else {{ yield resource; }}
        return result;
      }}
      link Closed = Client<Empty>;
    }}''')

with case("explicit overlapping affine captures retain their refusal"):
    run(f'''module {{ {IDENTITY} {AFFINE}
      fn Client<C: Cell>(flag: bool, resource: C::Value) -> C::Value {{
        let alias = resource;
        if flag capture(alias, resource) -> (result) {{ yield alias; }} else {{ yield resource; }}
        return result;
      }}
      link Closed = Client<Empty>;
    }}''', "library-resource-use")

with case("map retains finite variant arms and authored-arm capture order"):
    text = module('''
      enum Tag { Left(), Right() }
      fn Client<C: Marker>(items: Array<Tag, 2>, z: bool, a: bool) -> Array<bool, 2> {
        return map items |item| {
          match item -> (next) {
            Right() => { yield z; },
            Left() => { yield a; }
          }
          next
        };
      }
      link Closed = Client<Selected>;
    ''')
    accepted(text)
    report = json.loads(run(text, command="protocol-analyze"))
    traversal = next(rows(report, "array_traversal"))
    assert traversal["captures"] == [{"value": 1, "path": []}, {"value": 2, "path": []}]

with case("ordinary runtime indexing captures its vector rather than a fictitious field"):
    accepted('''module {
      fn Use(flag: bool, items: Indices) -> index {
        if flag -> (result) {
          let item = items[0]; yield item;
        } else {
          let item = items[0]; yield item;
        }
        return result;
      }
    }''')

with case("nested record array projections capture only the used element"):
    accepted(module('''
      struct Held(values: Array<bool, 2>);
      fn Client<C: Marker>(items: Array<bool, 2>, held: Held) -> Array<bool, 2> {
        return map items |item| { held.values[1] };
      }
      link Closed = Client<Selected>;
    '''))

with case("finite traversal expansion is bounded"):
    run(module('''
      fn Client<C: Marker>(items: Array<bool, 4097>) -> Array<bool, 4097> {
        return map items |item| { item };
      }
      link Closed = Client<Selected>;
    '''), "library-limit")

with case("lexical map composes through a natural-generic source helper"):
    accepted(module('''
      fn Map<N: nat>(items: Array<bool, N>) -> Array<bool, N> {
        return map items |item| { item };
      }
      fn Client<C: Marker>(items: Array<bool, 2>) -> Array<bool, 2> {
        return Map::<2>(items: items);
      }
      link Closed = Client<Selected>;
    '''))

with case("ordinary named operands evaluate once in written order before permutation"):
    emitted = accepted('''module {
      fn Choose(left: bool, right: bool) -> bool { return left; }
      fn First(value: bool) -> bool { return bool::not(value); }
      fn Second(value: bool) -> bool { return bool::not(value); }
      fn Use(x: bool, y: bool) -> bool { return Choose(right: First(x), left: Second(y)); }
    }''')
    calls = [row for row in functions(emitted)["Use"][4] if row[0] == "apply"]
    assert [row[2] for row in calls] == ["First", "Second", "Choose"]
    assert calls[-1][4] == [calls[1][5][0], calls[0][5][0]]

with case("ordinary local terminal arms do not manufacture continuing yields"):
    accepted('''module {
      fn Use(flag: bool, value: bool) -> bool {
        if flag -> (result) { stop abort; } else { yield value; }
        return result;
      }
    }''')

with case("ordinary source refuses instructions following a terminal stop"):
    run('''module {
      fn Use(flag: bool) -> bool { stop abort; return flag; }
    }''', "source-control-stop")

with case("ordinary finite arrays retain element shape and contextual literals"):
    accepted('''module {
      fn Echo(items: Array<(bool, bool), 2>) -> Array<(bool, bool), 2> { return items; }
      fn Use(a: bool, b: bool) -> Array<(bool, bool), 2> {
        return Echo(items: [(a, b), (b, a)]);
      }
    }''')

with case("array and product boundaries are distinct even with identical leaves"):
    run('''module {
      fn Echo(items: Array<bool, 2>) -> Array<bool, 2> { return items; }
      fn Use(a: bool, b: bool) -> Array<bool, 2> { return Echo(items: (a, b)); }
    }''', "source-annotation-type")

with case("ordinary array literal length must match its expected count"):
    run('''module {
      fn Echo(items: Array<bool, 2>) -> Array<bool, 2> { return items; }
      fn Use(a: bool) -> Array<bool, 2> { return Echo(items: [a]); }
    }''', "source-array-arity")

with case("ordinary empty arrays retain their element identity"):
    run('''module {
      fn Echo(items: Array<bool, 0>) -> Array<bool, 0> { return items; }
      fn Use(items: Array<index, 0>) -> Array<bool, 0> { return Echo(items); }
    }''', "source-annotation-type")

with case("ordinary record constructors propagate expected array field types"):
    accepted('''module {
      struct Held(values: Array<(bool, bool), 2>);
      fn Use(a: bool, b: bool) -> Held { return Held { values: [(a, b), (b, a)] }; }
    }''')

with case("ordinary array count and nested expansion are bounded"):
    run('''module { fn Use(x: Array<bool, 4097>) -> Array<bool, 4097> { return x; } }''',
        "source-array-limit")
    run('''module { fn Use(x: Array<bool, missing>) -> () { return (); } }''',
        "source-name-unresolved")
    run('''module { fn Use(x: Array<Array<(), 4096>, 4096>) -> () { return (); } }''',
        "source-array-limit")

with case("named imported link retains aggregate labels and exact record owner"):
    root = records() / "named-imported-link"
    root.mkdir(parents=True, exist_ok=True)
    lib = root / "lib.pir"
    app = root / "app.pir"
    identity = 'library(namespace="test", name="arrays", version="1", resolution="fixture")'
    lib.write_text(f'''module {{ {identity};
      pub struct Held(values: Array<(bool, bool), 2>);
      fn Echo(input: Held, flag: bool) -> Held {{ return input; }}
      pub link Selected = Echo<>;
    }}''')
    app.write_text(f'''module {{
      dependency lib = {identity};
      use lib::Held; use lib::Selected as Identity;
      fn Main(a: bool, b: bool) -> Held {{
        return Identity(flag: b, input: Held {{ values: [(a, b), (b, a)] }});
      }}
    }}''')
    emitted = commands.source("protocol-source", None, str(app), f"--library={lib}")
    assert json.loads(run(emitted)) == json.loads(emitted)
    commands.source("protocol-admit", None, str(app), f"--library={lib}")

with case("zero-length rigid array heads infer a generic element domain"):
    accepted('''module {
      fn Echo<F: Field>(items: Array<F::Element, 0>) -> Array<F::Element, 0> { return items; }
      fn Use(items: Array<"koala-bear"::Element, 0>) -> Array<"koala-bear"::Element, 0> {
        return Echo(items);
      }
    }''')

with case("rigid array heads provide expected type for a second empty argument"):
    accepted('''module {
      fn Choose<F: Field>(first: Array<F::Element, 0>, second: Array<F::Element, 0>)
          -> Array<F::Element, 0> { return second; }
      fn Use(items: Array<"koala-bear"::Element, 0>) -> Array<"koala-bear"::Element, 0> {
        return Choose(second: [], first: items);
      }
    }''')

with case("expected zero-array result determines a helper static domain"):
    accepted('''module {
      fn Empty<F: Field>() -> Array<F::Element, 0> { return []; }
      fn Use() -> Array<"koala-bear"::Element, 0> { return Empty(); }
    }''')

with case("fold initial may be an authored record construction"):
    accepted(module('''
      struct State(value: bool);
      fn Client<C: Marker>(items: Array<bool, 2>, initial: bool) -> State {
        return fold items with State { value: initial } |state, item| { state };
      }
      link Closed = Client<Selected>;
    '''))

for count in (0, 2):
    with case(f"selected terminal member stops lexical traversal at first trip, count={count}"):
        text = f'''module {{ {IDENTITY}
          interface Step {{ local next(item: bool) -> bool; }}
          component Halt: Step {{ local next(item: bool) -> bool {{ stop abort; }} }}
          fn Client<C: Step>(items: Array<bool, {count}>, after: bool) -> bool effects (local) {{
            let mapped: Array<bool, {count}> = map items |item| {{ C::next(item) }};
            return bool::not(after);
          }}
          link Closed = Client<Halt>;
        }}'''
        emitted = accepted(text)
        fns = functions(emitted)
        pending, reached, instructions = ["Closed"], set(), []
        while pending:
            name = pending.pop()
            if name in reached:
                continue
            reached.add(name)
            instructions.extend(fns[name][4])
            pending.extend(row[2] for row in fns[name][4] if row[0] == "apply")
        assert any(row[0] == "stop" for row in instructions) == (count != 0)
        if count:
            assert sum(row[0] == "apply" and fns[row[2]][5][0].endswith("Halt.next")
                       for row in instructions) == 1
            assert not any(row[0] == "op" for row in instructions)

with case("inferred capture union keeps whole aggregate once across exclusive arms"):
    accepted(module('''
      fn Whole<C: Marker>(value: (bool, bool)) -> bool { return value.0; }
      fn Client<C: Marker>(items: Array<bool, 2>, held: (bool, bool)) -> Array<bool, 2> {
        return map items |item| {
          if item -> (chosen) { yield held.0; }
          else { let value = Whole::<C>(held); yield value; }
          chosen
        };
      }
      link Closed = Client<Selected>;
    '''))
