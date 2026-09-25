"""Runtime-dependent checked alternatives, exact captures, and native/Lean execution."""
import hashlib
import json

import pytest

from journal import Journal
from variant_codec import tree


def authored(depth=1, capture=False, stopping=False):
    declarations = ['enum Outcome<C: Cell> { Ready(C::State), Invalid(bool) }']
    wrapping, unwrapping = [], []
    inner, value = 'Outcome', 'chosen'
    for level in range(1, depth):
        outer = f'Layer{level}'
        declarations.append(f'enum {outer}<C: Cell> {{ Wrap({inner}<C>) }}')
        wrapping.append(f'let v{level}: {outer}<C> = {outer}::Wrap({value});')

        inner, value = outer, f'v{level}'
    selected_value = value
    for level in reversed(range(1, depth)):
        output = f'u{level-1}'
        unwrapping.append(f'match {selected_value} capture() -> ({output}) {{ Wrap(x) => {{ yield (x); }} }}')
        selected_value = output
    relation = 'relation Circuit = r1cs("relation.json");' if capture else ''
    generic = '<R: association>' if capture else ''
    selected = '<Circuit>' if capture else ''
    association = 'association Subject = R;' if capture else ''
    subject = 'association Subject;' if capture else ''
    action = 'stop refused;' if stopping else 'return x;'
    return f'''module {{
      library(namespace="test", name="alternatives", version="2", resolution="exact");
      {relation}
      interface Cell {{ type State drop; {subject}
        local value(x: State) -> bool;
      }}
      component CellImpl{generic}: Cell {{ type State = bool; {association}
        local value(x: State) -> bool {{ {action} }}
      }}
      {' '.join(declarations)}
      fn Select<C: Cell>(state: C::State, ready: bool) -> bool {{
        if ready capture(state, ready) -> (chosen) {{
          let choice: Outcome<C> = Outcome::Ready(state); yield (choice);
        }} else {{
          let choice: Outcome<C> = Outcome::Invalid(ready); yield (choice);
        }}
        {' '.join(wrapping)}
        {' '.join(unwrapping)}
        match {selected_value} capture() -> (answer) {{
          Ready(state) => {{ let answer = C::value(state); yield (answer); }},
          Invalid(error) => {{ yield (error); }}
        }}
        return answer;
      }}
      link Closed = Select<CellImpl{selected}>;
      protocol Demo {{
        roles (P); inputs (P state: bool, P ready: bool); outputs (P bool);
        local P: let answer = Closed(state, ready);
        return answer;
      }}
      instance demo: Demo {{ roles (P = P); }}
      entry main = demo;
    }}'''


def execute(journal, toolchain, source, physical, ready, stopped=False):
    checker = toolchain.checker('interactive-protocol')
    reference_inputs = ['zkc.reference-inputs/1', 'main', 'checked-variants',
                        [['P', [['state', ['bool', 'true']], ['ready', ['bool', str(ready).lower()]]]]], [], [], []]
    def wire(value):
        return (b'ZKCV\x01\x05' + bytes([value])).hex()
    native_inputs = ['zkc.run/2', 'main', 'checked-variants', [],
                     [['P', [], [['state', ['wire', wire(True)]], ['ready', ['wire', wire(ready)]]], []]], []]
    reference = json.loads(journal.run([checker, '--reference', source,
                           journal.write(f'reference-{ready}.json', reference_inputs)]))
    native = json.loads(journal.run([toolchain.runtime, 'run-protocol', source, physical,
                        journal.write(f'native-{ready}.json', native_inputs), checker]))
    if stopped and ready:
        assert reference[3][:2] == ['refused', 'explicit-stop']
        assert native['outcome'][0] == 'stopped'
        assert native['stop']['detail'] == 'refused'
    else:
        assert reference[3] == ['returned', [['bool', str(ready).lower()]]]
        assert native['outcome'] == ['returned', {'P': [['bool', ready]]}]
    assert not native['resources'] and not reference[5]
    assert native['wire']['messages'] == 0
    return native['usage']


@pytest.mark.parametrize('depth,rows,stopping,wide', [
    (1, 0, False, False), (1, 200, False, False), (8, 200, False, False),
    (2, 0, True, False), (1, 200, False, True), (8, 24, False, True)])
def test_authored_variants(toolchain, directory, depth, rows, stopping, wide):
    journal = Journal(directory)
    if rows:
        relation = ['zkc.relation.r1cs/1', 'bn254.fr', '3', '0', '1',
                    [[[["1", "1"]], [["2", "1"]], [["0", "6"]]]] * rows]
        if wide:
            # Distinct full-width canonical BN254 coefficients. This is a
            # captured-subject capacity probe, not a proof of these constraints.
            modulus = 21888242871839275222246405745257275088548364400416034343698204186575808495617
            def coefficient(row, column):
                digest = hashlib.sha256(f"{row}:{column}".encode()).digest()
                return str(1 + int.from_bytes(digest, 'big') % (modulus - 1))
            relation[-1] = [[[[str(c), coefficient(r, c)]] for c in range(3)] for r in range(rows)]
        journal.write('relation.json', relation)
    authored_path = directory / 'source.pir'
    authored_path.write_text(authored(depth, bool(rows), stopping))
    if rows:
        resolved = json.loads(journal.run([toolchain.compiler, 'protocol-resolve', authored_path]))
        frozen = journal.write('resolved.json', resolved)
        source = json.loads(journal.run([toolchain.compiler, 'protocol-materialize', frozen]))
    else:
        source = json.loads(journal.run([toolchain.compiler, 'protocol-source', authored_path]))
    source_path = journal.write('source.json', source)
    checker = toolchain.checker('interactive-protocol')
    admission = json.loads(journal.run([checker, '--admit', source_path]))
    assert admission[0] == 'checked'
    physical = json.loads(journal.run([toolchain.compiler, 'protocol-compile', source_path]))
    physical_path = journal.write('physical.json', physical)
    assert json.loads(journal.run([checker, '--check', source_path, physical_path]))[0] == 'checked'
    usage = {}
    for ready in (False, True):
        usage[str(ready)] = execute(journal, toolchain, source_path, physical_path, ready, stopping)
    if rows:
        # The exact relation survives in each self-contained type's node table
        # once, even when static captures and nested abstract payloads share it.
        def variants(value):
            if isinstance(value, list):
                for v in value:
                    yield from variants(v)
            elif isinstance(value, str) and value.startswith('variant:'):
                yield value
        types = list(variants(source))
        assert types
        exact = json.dumps(relation, separators=(',', ':'))
        for spelling in types:
            graph = json.loads(bytes.fromhex(spelling[8:]))
            assert graph[1].count(exact) == 1
            assert tree(spelling)[0]  # structural nominal stays self-contained
    journal.write('capacity.json', {
        'depth': depth, 'rows': rows, 'full_width_coefficients': wide,
        'source_bytes': source_path.stat().st_size,
        'physical_bytes': physical_path.stat().st_size,
        'usage': usage,
    })
    journal.save()
