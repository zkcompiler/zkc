"""Retained immutable storage at proof scale through the common CLI Host.

The prover commits a 65,536-row matrix once and opens up to 64 rows from a
repeated phase that captures the opening state; the verifier authenticates
every row. Storage counts each allocation once however often it is captured
or passed, while each opening still charges the row and path it reads. Every
run states its capacity record, and the report repeats the record it used.
"""
import hashlib
import json

import pytest

SOURCE = '''module sample;
domain E = field("koala-bear.ext8-binomial3");
domain F = field("{field}");
domain Rows = commitment("rows.merkle-keccak256.{field}/0");
type Vector<T: Field> = builtin("vector", T);
type Root = builtin("commitment", Rows);
type Path = builtin("proof", Rows);
type State = builtin("opening_state", Rows);
fn make(size: index) -> Vector<F> {{ return kernel<F>("vector.fill", 1, size); }}
fn commit(values: Vector<F>, width: index) -> (Root, State) {{
  return kernel<Rows>("oracle.commit", values, width);
}}
fn open(state: State, query: index) -> (Vector<F>, Path) {{
  return kernel<Rows>("oracle.open", state, query);
}}
fn check(root: Root, width: index, height: index, query: index, row: Vector<F>, path: Path) -> bool {{
  return kernel<Rows>("oracle.check", root, width, height, query, row, path);
}}
fn rows(size: index, width: index) -> index {{ return kernel("index.div", size, width); }}
fn coordinate(i: index, height: index) -> index {{ return kernel("index.mod", i, height); }}
math fn both(a: bool, b: bool) -> bool {{ return intrinsic("bool.and", a, b); }}
protocol Cost roles(P,V)(size:index@(P,V), width:index@(P,V), count:index@(P,V),
    coins:Random<E>@V)->(accepted:bool@V) {{
  let values @P=make(size);
  let tree @P=commit(values, width);
  let hp @P=rows(size, width);
  let hv @V=rows(size, width);
  let root=send P->V(tree.0);
  let challenge=coins.draw();
  let delivered=send V->P(challenge);
  let mut accepted @V = true;
  for i in 0..count roles(P,V) max 64 {{
    let qp @P=coordinate(i, hp);
    let qv @V=coordinate(i, hv);
    let opening @P=open(tree.1, qp);
    let row=send P->V(opening.0);
    let path=send P->V(opening.1);
    let checked @V=check(root, width, hv, qv, row, path);
    accepted=both(accepted, checked);
  }}
  return(accepted=accepted);
}}
entry Demo=Cost {{
  prover P; verifier V; public{{size,width,count}}; accept accepted;
  construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0") {{derive coins;}}
}}
'''

ROWS = 65536
# Defaults except the element ceiling, which a multiwidth matrix needs:
# [elements, groups, wire, value, [instructions, iterations, logical], [live, total]].
DEFAULT = ['zkc.native-capacity/0', '65536', '4096', '16777216', '67108864',
           ['1000000', '100000', '4294967296'], ['67108864', '268435456']]
WIDE = [DEFAULT[0], '1048576', *DEFAULT[2:]]


def element_bytes(field):
    return 32 if field.endswith('ext8-binomial3') else 4


def state_bytes(field, width):
    """Committed table plus Merkle tree, as charged for one opening state."""
    return ROWS * width * element_bytes(field) + (2 * ROWS - 1) * 32 + 256


class Case:
    def __init__(self, toolchain, journal, directory, field, width, capacity):
        self.journal, self.directory, self.runtime = journal, directory, toolchain.runtime
        self.width, self.capacity, self.runs = width, capacity, 0
        source = directory / 'retained.zkc'
        source.write_text(SOURCE.format(field=field))
        self.package = directory / 'retained.entry'
        report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=sample={source}', '--entry=sample::Demo',
                               f'--output={self.package}'])
        self.pin = report['package_sha256']
        assert self.pin == hashlib.sha256(self.package.read_bytes()).hexdigest()

    def files(self, count, capacity):
        self.runs += 1
        request = self.journal.write(f'request-{self.runs}.json', {
            'format': 'zkc.entry-proof/0', 'context': '',
            'public': {'size': ROWS * self.width, 'width': self.width, 'count': count},
            'inputs': {}})
        limits = self.journal.write(f'capacity-{self.runs}.json', capacity)
        return request, f'--capacity={limits}', self.directory / f'proof-{self.runs}.bin'

    def prove(self, count, capacity=None, refuses=None):
        capacity = capacity or self.capacity
        request, option, proof = self.files(count, capacity)
        report = self.journal.json([self.runtime, 'prove', self.package, self.pin,
                                    request, proof, option], refuses=refuses)
        if 'execution' in report:
            assert report['capacity'] == capacity
        return report, proof

    def verify(self, count, proof):
        request, option, _ = self.files(count, self.capacity)
        report = self.journal.json([self.runtime, 'verify', self.package, self.pin,
                                    request, proof, option])
        assert report['status'] == 'accepted' and report['capacity'] == self.capacity
        return report


@pytest.mark.parametrize('field,width,capacity', [
    ('koala-bear.ext8-binomial3', 1, DEFAULT),
    ('koala-bear.ext8-binomial3', 4, WIDE),
    ('koala-bear.ext8-binomial3', 8, WIDE),
    ('koala-bear', 8, WIDE),
    ('koala-bear', 16, WIDE),
])
def test_committed_state_is_retained_once_across_64_openings(toolchain, journal, directory,
                                                             field, width, capacity):
    case = Case(toolchain, journal, directory, field, width, capacity)
    one, _ = case.prove(1)
    produced, proof = case.prove(64)
    assert produced['status'] == 'produced' and produced['execution']['iterations'] == 64
    case.verify(64, proof)
    vector = ROWS * width * element_bytes(field) + 256
    state = state_bytes(field, width)
    first, last = one['execution'], produced['execution']
    # The vector and the state are each allocated once; everything else is small.
    assert vector + state < first['total_value_bytes'] < vector + state + (64 << 10)
    # Each further opening allocates its index, row, path and messages, never
    # another copy of the captured state, and reads only its row and path.
    fresh = last['total_value_bytes'] - first['total_value_bytes']
    work = last['logical_bytes'] - first['logical_bytes']
    assert fresh % 63 == 0 and work % 63 == 0
    row = width * element_bytes(field) + 256
    assert fresh // 63 < row + (16 << 10)
    assert work // 63 < 2 * row + (16 << 10)
    # The previous per-binding charge recharged the state at every capture and call.
    assert last['total_value_bytes'] < 64 * state


def exhausted(report):
    """A refusal by a runner budget or by a kernel's allowance preflight."""
    stop = report['execution']['stop']
    assert report['status'] == 'refused'
    assert stop['kind'] == 'Limit' or 'exhausted:output-bytes' in stop['kind'], stop
    return stop


def test_stated_budgets_bind_shared_storage_and_repeated_reads(toolchain, journal, directory):
    field = 'koala-bear.ext8-binomial3'
    case = Case(toolchain, journal, directory, field, 1, DEFAULT)
    produced, _ = case.prove(64)
    usage = produced['execution']
    # Sharing does not make reads free: one byte less logical work stops the
    # prover in its final opening, before it publishes a proof.
    limited = json.loads(json.dumps(DEFAULT))
    limited[5][2] = str(usage['logical_bytes'] - 1)
    refused, proof = case.prove(64, limited, refuses=True)
    stop = exhausted(refused)
    assert stop['origin'][4][-1][2] == '63' and not proof.exists()
    assert refused['execution']['logical_bytes'] < usage['logical_bytes']
    # The fresh-allocation ceiling binds at the measured total and not before.
    limited = json.loads(json.dumps(DEFAULT))
    limited[6][1] = str(usage['total_value_bytes'])
    assert case.prove(64, limited)[0]['status'] == 'produced'
    limited[6][1] = str(usage['total_value_bytes'] - 1)
    exhausted(case.prove(64, limited, refuses=True)[0])
    # Live storage must hold the vector and the committed state together.
    limited = json.loads(json.dumps(DEFAULT))
    limited[6][0] = str(state_bytes(field, 1))
    stop = exhausted(case.prove(64, limited, refuses=True)[0])
    assert stop['origin'][4] == []
    # The work ceiling cannot be raised above its installed maximum.
    limited = json.loads(json.dumps(DEFAULT))
    limited[5][2] = str(4294967297)
    case.prove(1, limited, refuses='native-capacity-limit')
