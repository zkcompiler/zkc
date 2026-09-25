"""Checked source enums and isolated, ownership-safe local regions."""
import json

from cases import case
from commands import Commands
from source_text import unlocated
from tools import examples, records

commands = Commands(records())
IDENTITY = 'library(namespace="example", name="variants", version="1", resolution="capture");'
CELL = '''interface Cell { type State drop; local step(x: State) -> State; }
component Scalar: Cell { type State = bool; local step(x: State) -> State { return x; } }'''
ENUM = 'enum Outcome<C: Cell> { Ready(C::State), Invalid(bool) }'
CLIENT = '''fn Client<C: Cell>(state: C::State, ok: bool) -> bool {
  let result: Outcome<C> = Outcome::Ready(state);
  match result capture(ok) -> (answer) {
    Ready(state) => { let next = C::step(state); yield (ok); },
    Invalid(error) => { yield (error); }
  }
  return answer;
}'''


def module(client=CLIENT, enum=ENUM, cell=CELL, link=False):
    return f'module {{ {IDENTITY} {cell} {enum} {client} ' + ('link Closed = Client<Scalar>;' if link else '') + '}'


def run(text, refuses=None):
    return commands.source('protocol-source', text, refuses=refuses)


with case('source example formats and retains enum and region syntax'):
    text = (examples / 'checked-variants.pir').read_text()
    before = unlocated(json.loads(commands.source('protocol-parse', text))['content'])
    formatted = commands.source('protocol-format', text)
    assert before == unlocated(json.loads(commands.source('protocol-parse', formatted))['content'])
    assert before['enums'][0]['name'] == 'Outcome'
    assert 'array_traversal' in json.dumps(before)
    assert '"if"' in json.dumps(before)

with case('an empty array of variants links like a non-empty one'):
    # A variant inside an empty array has no flat leaf; the linked entry still
    # keeps the flat boundary every variant port keeps.
    for count in (0, 2):
        run(module(f'fn Client<C: Cell>(xs: Array<Outcome<C>, {count}>, ok: bool) -> bool {{ return ok; }}',
                   link=True))
        run(module(f'fn Client<C: Cell>(xs: Array<Outcome<C>, {count}>, ok: bool) '
                   f'-> (Array<Outcome<C>, {count}>, bool) {{ return (xs, ok); }}', link=True))

with case('a variant behind a component representation keeps the flat boundary'):
    # The client's signature names only C::State; the selected representation
    # is what holds the variant, so the concrete port types decide.
    for state in ('(Flag, bool)', '(Array<Flag, 0>, bool)'):
        cell = ('interface Cell { type State drop; local step(x: State) -> State; } '
                'enum Flag { On(bool), Off(bool) } '
                f'component Scalar: Cell {{ type State = {state}; local step(x: State) -> State {{ return x; }} }}')
        run(module('fn Client<C: Cell>(x: C::State) -> C::State { return C::step(x); }', cell=cell, link=True))

with case('full source example links unequal layouts and zero traversal'):
    emitted = run((examples / 'checked-variants.pir').read_text())
    assert 'variant:' in emitted and 'resource_unit:' in emitted
    assert json.loads(run(emitted)) == json.loads(emitted)

with case('all abstract arms are checked before selection'):
    report = json.loads(commands.source('protocol-analyze', module()))
    assert report['state'] == 'source_checked'
    body = report['checked_libraries']['clients'][0]['body']
    assert any(i['kind'] == 'match' for i in body['instructions'])
    run(module(CLIENT.replace('yield (error);', 'let first = C::step(state); yield (error);')), 'library-source-name')

for name, replacement in [
    ('missing', 'Ready(state) => { yield (ok); }'),
    ('duplicate', 'Ready(state) => { yield (ok); }, Ready(state) => { yield (ok); }'),
    ('extra', 'Ready(state) => { yield (ok); }, Invalid(error) => { yield (error); }, Extra() => { yield (ok); }'),
]:
    with case(f'{name} match arm is refused'):
        start = CLIENT.index('    Ready(state)')
        end = CLIENT.index('\n  }', start)
        run(module(CLIENT[:start] + replacement + CLIENT[end:]), 'library-source-match-arm')

with case('wrong constructor payload type is refused'):
    run(module(CLIENT.replace('Outcome::Ready(state)', 'Outcome::Ready(ok)')), 'library-type-mismatch')

with case('constructor nominal mismatch is refused'):
    enum = ENUM + ' enum Other<C: Cell> { Ready(C::State), Invalid(bool) }'
    run(module(CLIENT.replace('Outcome::Ready(state)', 'Other::Ready(state)'), enum), 'library-source-enum-nominal')

with case('constructor requires expected type'):
    run(module(CLIENT.replace('result: Outcome<C>', 'result')), 'library-source-enum-expected')

with case('unknown constructor alternative is refused'):
    run(module(CLIENT.replace('Outcome::Ready(state)', 'Outcome::Missing(state)')), 'library-source-enum-alternative')

with case('inactive payload cannot be projected'):
    run(module(CLIENT.replace('match result', 'let payload = result.Ready; match result')), 'library-source-projection')

with case('match outputs must agree across arms'):
    run(module(CLIENT.replace('yield (error);', 'yield (());')), 'source-syntax')
    run(module(CLIENT.replace('yield (ok);', 'yield (next);')), 'library-type-mismatch')

with case('affine payload cannot be reused inside an arm'):
    run(module(CLIENT.replace('yield (ok);', 'let twice = C::step(state); yield (ok);')), 'library-resource-use')

with case('checked source preserves non-droppable payload obligations'):
    run(module(cell=CELL.replace('State drop;', 'State;')), 'library-resource-leak')

with case('copy bound allows payload reuse'):
    copy = CELL.replace('State drop', 'State copy drop')
    run(module(CLIENT.replace('yield (ok);', 'let twice = C::step(state); yield (ok);'), cell=copy, link=True))

with case('arm scope restores outer bindings and does not leak payload names'):
    run(module(CLIENT.replace('return answer;', 'let next = C::step(state); return answer;')), 'library-resource-use')
    run(module(CLIENT.replace('return answer;', 'return error;')), 'source-name-unresolved')

TRAVERSE = '''fn Client<C: Cell>(items: Array<C::State, 2>, initial: C::State, ok: bool) -> C::State {
  for element in items carry(state = initial) capture(ok) -> (output) {
    let used = C::step(state);
    let next = C::step(element);
    yield (next);
  }
  return output;
}'''
with case('array traversal checks abstract state before expansion'):
    run(module(TRAVERSE, link=True))

with case('zero traversal preserves the initial state'):
    zero = TRAVERSE.replace('items: Array<C::State, 2>, ', '').replace('  for element', '  let items: Array<C::State, 0> = [];\n  for element')
    run(module(zero, link=True))

with case('empty array element gets expected enum type'):
    client = '''fn Client<C: Cell>(ok: bool) -> bool {
      let values: Array<Outcome<C>, 0> = [];
      return ok;
    }'''
    run(module(client, link=True))

with case('traversal capture must be copyable'):
    run(module(TRAVERSE.replace('capture(ok)', 'capture(initial)')), 'library-resource-use')
    extra = TRAVERSE.replace('ok: bool', 'ok: bool, shared: C::State').replace('capture(ok)', 'capture(shared)')
    run(module(extra), 'library-traversal-capture')

with case('traversal cannot access uncaptured outer names'):
    run(module(TRAVERSE.replace('capture(ok)', 'capture()').replace('let used', 'let ambient = ok; let used')), 'library-source-name')

with case('traversal cannot reuse a consumed element'):
    run(module(TRAVERSE.replace('yield (next);', 'let twice = C::step(element); yield (next);')), 'library-resource-use')

with case('traversal carried type and arity are checked'):
    run(module(TRAVERSE.replace('yield (next);', 'yield (ok);')), 'library-type-mismatch')
    run(module(TRAVERSE.replace('-> (output)', '-> (output, extra)')), 'library-source-traversal')

with case('recursive enum declaration refused even unused'):
    run(module(enum='enum Cycle<C: Cell> { Again(Cycle<C>) }', client=''), 'library-source-limit')

with case('duplicate alternatives refused even unused'):
    run(module(enum='enum Bad { Item(bool), Item(bool) }', client=''), 'library-source-duplicate')

with case('unsupported arbitrary type parameter is explicit'):
    run(module(enum='enum Result<T: type, E: type> { Ok(T), Err(E) }', client=''), 'source-name-unresolved')

with case('protocol match cannot schedule work'):
    text = module(client='')[:-1] + ' protocol P { roles (P); inputs (P x: bool); outputs (P bool); match x capture() -> (out) { Ready(x) => { yield (x); } } return out; }}'
    run(text, 'source-syntax')

with case('ordinary placement cannot bypass checked library match'):
    text = module(client='')[:-1] + ' protocol P { roles (P); inputs (P x: bool); outputs (P bool); let out = local P { match x capture() -> (answer) { Ready(x) => { yield (x); } } return answer; }; return out; }}'
    run(text, 'source-local-control')

with case('phantom component captures remain nominally distinct before selection'):
    client = '''fn Client<C: Cell, D: Cell>(ok: bool) -> bool {
      let result: Marker<C> = Marker::Value(ok);
      let wrong: Marker<D> = result;
      return ok;
    }'''
    run(module(client, enum='enum Marker<C: Cell> { Value(bool) }'), 'library-source-annotation')

with case('phantom captures distinguish equal concrete layouts after linking'):
    client = '''fn Client<C: Cell>(ok: bool) -> Marker<C> {
      return Marker::Value(ok);
    }'''
    cells = CELL + ' component Other: Cell { type State = bool; local step(x: State) -> State { return x; } }'
    text = module(client, enum='enum Marker<C: Cell> { Value(bool) }', cell=cells)[:-1]
    emitted = json.loads(run(text + 'link One = Client<Scalar>; link Two = Client<Other>;}'))
    functions = emitted[2]
    selected = {f[1]: f[3] for f in functions if f[1] in ('One', 'Two')}
    assert selected['One'] != selected['Two']

with case('associated count traversal checks symbolically then expands'):
    cell = CELL.replace('type State drop;', 'type State drop; nat Count;').replace('type State = bool;', 'type State = bool; nat Count = 2;')
    client = TRAVERSE.replace('Array<C::State, 2>', 'Array<C::State, C::Count>')
    run(module(client, cell=cell))
    run(module(client, cell=cell, link=True))

with case('unit and multiple payload fields have no inactive storage'):
    client = '''fn Client<C: Cell>(ok: bool) -> bool {
      let result: Packet = Packet::Pair(ok, ok);
      match result capture(ok) -> (answer) {
        Empty() => { yield (ok); },
        Pair(first, second) => { yield (second); }
      }
      return answer;
    }'''
    run(module(client, enum='enum Packet { Empty, Pair(bool, bool) }', link=True))

with case('nested match inputs stay isolated and fresh'):
    client = '''fn Client<C: Cell>(ok: bool) -> bool {
      let result: Packet = Packet::Value(ok);
      match result capture() -> (answer) {
        Value(payload) => {
          let inner: Packet = Packet::Value(payload);
          match inner capture() -> (nested) { Value(payload) => { yield (payload); } }
          yield (nested);
        }
      }
      return answer;
    }'''
    emitted = run(module(client, enum='enum Packet { Value(bool) }', link=True))
    assert emitted.count('"match"') >= 2


with case('one stopped arm does not determine continuing output types'):
    run(module(CLIENT.replace('let next = C::step(state); yield (ok);', 'stop reject;'), link=True))
    run(module(CLIENT.replace('yield (error);', 'stop abort;'), link=True))

with case('all stopping arms produce no invented values'):
    client = CLIENT.replace('-> (answer)', '-> ()').replace('let next = C::step(state); yield (ok);', 'stop reject;').replace('yield (error);', 'stop abort;').replace('  return answer;', '')
    run(module(client, link=True))

with case('local stops reject invalid reasons and following instructions'):
    run(module(CLIENT.replace('yield (error);', 'stop success;')), 'library-stop')
    run(module(CLIENT.replace('yield (error);', 'stop reject; yield (error);')), 'library-source-return')
    run(module(CLIENT.replace('yield (error);', 'stop P reject;')), 'library-source-role')

with case('role-free stop survives parsing and formatting'):
    text = module(CLIENT.replace('yield (error);', 'stop refused;'), link=True)
    before = unlocated(json.loads(commands.source('protocol-parse', text))['content'])
    formatted = commands.source('protocol-format', text)
    assert before == unlocated(json.loads(commands.source('protocol-parse', formatted))['content'])

with case('loaded relation captures exact public partition as a static subject'):
    directory = records()
    asset = directory / 'captured-relation.json'
    path = directory / 'captured-library.pir'
    snapshot = directory / 'captured-library.json'
    relation = ['zkc.relation.r1cs/1', 'bn254.fr', '3', '0', '1',
                [[[["1", "1"]], [["2", "1"]], [["0", "6"]]]]]
    asset.write_text(json.dumps(relation))
    path.write_text(f'''module {{ {IDENTITY}
      relation Circuit = r1cs("captured-relation.json");
      interface Preparation {{ type State drop; association Subject;
        local forward(state: State) -> State;
      }}
      component ForRelation<R: association>: Preparation {{
        type State = bool; association Subject = R;
        local forward(state: State) -> State {{ return state; }}
      }}
      enum Prepared<C: Preparation> {{ Ready(C::State), Invalid(bool) }}
      fn Forward<C: Preparation>(state: C::State) -> Prepared<C> {{
        return Prepared::Ready(C::forward(state));
      }}
      link Selected = Forward<ForRelation<Circuit>>;
    }}''')
    first = commands.source('protocol-resolve', None, path)
    snapshot.write_text(first)
    # The explicit loader emits the common carrier, not a source analysis AST.
    frozen = json.loads(first)
    assert frozen[0] == 'zkc.relations/1'
    assert frozen[1][0][0] == ['Circuit', relation]
    selected = next(fn for fn in frozen[2][2] if fn[1] == 'Selected')
    original_type = selected[3][0]
    original = commands.source('protocol-source', None, snapshot)
    relation[3], relation[4] = '1', '0'
    asset.write_text(json.dumps(relation))
    changed = commands.source('protocol-resolve', None, path)
    snapshot.write_text(changed)
    current = commands.source('protocol-source', None, snapshot)
    changed_module = json.loads(changed)
    changed_selected = next(fn for fn in changed_module[2][2] if fn[1] == 'Selected')
    assert changed_selected[3][0] != original_type
    assert current != original
    asset.unlink()
    snapshot.write_text(first)
    assert commands.source('protocol-source', None, snapshot) == original


def expand(text, inputs='state: bool, ok: bool', arguments='state, ok'):
    text = text.rstrip()[:-1] + f"""
      protocol Test {{
        roles (P); inputs ({', '.join('P ' + p.strip() for p in inputs.split(','))}); outputs (P bool);
        local P: let result = Closed({arguments}); return result;
      }}
      instance Run: Test {{ roles (P = Prover); }}
      entry test = Run;
    }}"""
    return commands.source('protocol-expand', text)


CONDITIONAL = CLIENT.replace(
    'let result: Outcome<C> = Outcome::Ready(state);',
    """if ok capture(state, ok) -> (result) {
    let ready: Outcome<C> = Outcome::Ready(state); yield (ready);
  } else {
    let invalid: Outcome<C> = Outcome::Invalid(ok); yield (invalid);
  }""",
)

with case('runtime conditional produces either nominal result from generic source'):
    emitted = json.loads(run(module(CONDITIONAL, link=True)))
    assert 'if' in json.dumps(emitted)
    assert 'Ready' in json.dumps(emitted) and 'Invalid' in json.dumps(emitted)
    expand(module(CONDITIONAL, link=True))
    run(module(CONDITIONAL, cell=CELL.replace('type State = bool;', 'type State = ();'), link=True))

with case('conditional condition must be Boolean with an authored location'):
    text = module(CONDITIONAL.replace('if ok capture', 'if state capture'))
    run(text, 'library-condition')
    report = json.loads(commands.source('protocol-analyze', text))
    error = next(d for d in report['diagnostics'] if d['code'] == 'library-condition')
    assert error['span']['offset'] == text.index('if state capture')

with case('conditional arms are isolated and captures move once'):
    run(module(CONDITIONAL.replace('capture(state, ok)', 'capture(ok)')), 'library-source-name')
    run(module(CONDITIONAL.replace('capture(state, ok)', 'capture(state, state, ok)')), 'library-source-duplicate')
    run(module(CONDITIONAL.replace('return answer;', 'let reused = C::step(state); return answer;')), 'library-resource-use')
    run(module(CONDITIONAL.replace('return answer;', 'return invalid;')), 'source-name-unresolved')

with case('conditional continuing result types and arities agree'):
    run(module(CONDITIONAL.replace('yield (invalid);', 'yield (ok);')), 'library-type-mismatch')
    run(module(CONDITIONAL.replace('yield (invalid);', 'yield ();')), 'library-source-branch-output')

with case('conditional stopping arm owes no payload, capture or result'):
    mixed = CONDITIONAL.replace('let invalid: Outcome<C> = Outcome::Invalid(ok); yield (invalid);', 'stop reject;')
    run(module(mixed, link=True))
    expand(module(mixed, link=True))
    run(module(mixed.replace('let ready: Outcome<C> = Outcome::Ready(state); yield (ready);', 'stop abort;')), 'library-stop')

MEMBER = """enum Decision { Ready(bool), Invalid(bool) }
interface Choose { local choose(ok: bool) -> Decision; }
component Runtime: Choose {
  local choose(ok: bool) -> Decision {
    if ok capture(ok) -> (result) {
      let ready: Decision = Decision::Ready(ok); yield (ready);
    } else {
      let invalid: Decision = Decision::Invalid(ok); yield (invalid);
    }
    return result;
  }
}
fn Client<C: Choose>(ok: bool) -> bool {
  let decision = C::choose(ok);
  match decision capture() -> (answer) {
    Ready(value) => { yield (value); },
    Invalid(error) => { yield (error); }
  }
  return answer;
}
link Closed = Client<Runtime>;"""

with case('runtime conditional in selected component member constructs either result'):
    text = f'module {{ {IDENTITY} {MEMBER} }}'
    emitted = run(text)
    assert 'if' in emitted
    expand(text, 'ok: bool', 'ok')

STOP_CLIENT = """fn Client<C: Cell>(state: C::State, ok: bool) -> C::State {
  if ok capture(state) -> (result) {
    let next = C::step(state); yield (next);
  } else {
    let next = C::step(state); yield (next);
  }
  return result;
}"""
STOP_CELL = CELL.replace('return x;', 'stop refused;')

with case('selected terminal calls erase unreachable join results'):
    run(module(STOP_CLIENT, link=True))
    text = module(STOP_CLIENT, cell=STOP_CELL, link=True)
    run(text)
    assert 'refused' in expand(text)

with case('selected terminal call in one arm preserves continuing result'):
    mixed = STOP_CLIENT.replace('} else {\n    let next = C::step(state); yield (next);', '} else {\n    yield (state);')
    text = module(mixed, cell=STOP_CELL, link=True)
    run(text)
    expand(text)

with case('terminal conditional with no outputs never invents a result'):
    client = """fn Client<C: Cell>(ok: bool) -> bool {
      if ok capture() -> () { stop reject; } else { stop refused; }
    }"""
    run(module(client, link=True))
    expand(module(client, link=True), 'ok: bool', 'ok')


with case('conditional survives bounded traversal with fresh isolated arm values'):
    client = TRAVERSE.replace('let next = C::step(element);', """if ok capture(element) -> (next) {
      let advanced = C::step(element); yield (advanced);
    } else { yield (element); }""")
    run(module(client, link=True))

with case('nested conditional and match preserve arm isolation'):
    client = CONDITIONAL.replace('yield (ok);', """if ok capture(ok) -> (chosen) {
      yield (ok);
    } else { stop reject; }
    yield (chosen);""")
    run(module(client, link=True))
    expand(module(client, link=True))

with case('selected terminal calls in resultless join clear unreachable return'):
    client = STOP_CLIENT.replace('-> C::State {', '-> bool {').replace('-> (result)', '-> ()').replace('yield (next);', 'yield ();').replace('return result;', 'return ok;')
    text = module(client, cell=STOP_CELL, link=True)
    run(text)
    expanded = expand(text)
    assert 'refused' in expanded

with case('selected terminal calls through match erase unreachable results'):
    client = """fn Client<C: Cell>(state: C::State, ok: bool) -> C::State {
      let tag: Choice = Choice::Left();
      match tag capture(state) -> (result) {
        Left() => { let next = C::step(state); yield (next); },
        Right() => { let next = C::step(state); yield (next); }
      }
      return result;
    }"""
    enum = 'enum Choice { Left(()), Right(()) }'
    run(module(client, enum=enum, link=True))
    text = module(client, enum=enum, cell=STOP_CELL, link=True)
    run(text)
    assert 'refused' in expand(text)


with case('private conditional transfers empty and stored component state'):
    for representation in ('()', 'bool'):
        cell = f"""interface Cell {{ type State drop; local step(x: State, ok: bool) -> State; }}
        component Scalar: Cell {{
          type State = {representation};
          local step(x: State, ok: bool) -> State {{
            if ok capture(x) -> (result) {{ yield (x); }} else {{ yield (x); }}
            return result;
          }}
        }}"""
        client = CONDITIONAL.replace('C::step(state)', 'C::step(state, ok)')
        run(module(client, cell=cell, link=True))


with case('selected terminal behavior propagates through member call chains'):
    forwarding = """component Forward<C: Cell>: Cell {
      type State = C::State;
      local step(x: State) -> State { return C::step(x); }
    }"""
    def forwarded(client, cell):
        return module(client, cell=cell + forwarding, link=True).replace('Client<Scalar>', 'Client<Forward<Scalar>>')
    run(forwarded(STOP_CLIENT, CELL))
    assert 'refused' in expand(forwarded(STOP_CLIENT, STOP_CELL))
    mixed = STOP_CLIENT.replace('} else {\n    let next = C::step(state); yield (next);', '} else {\n    yield (state);')
    text = forwarded(mixed, STOP_CELL)
    assert 'refused' in run(text)
    expand(text)
