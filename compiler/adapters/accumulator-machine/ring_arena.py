"""KoalaBear arithmetic, a `zkc.ring/0` arena builder and a reference evaluator.

KoalaBear is the prime field of characteristic P = 2^31 - 2^24 + 1. Its
installed degree-eight extension `koala-bear.ext8-binomial3` is
KoalaBear[X]/(X^8 - 3), written as eight base coordinates in the ascending
basis 1, X, ..., X^7. Every value here is such an eight-coordinate tuple; a
base-field value has zero higher coordinates, so embedding is the identity on
this representation.

The builder hash-conses nodes and inputs, and `finish` keeps only what the
selected outputs reach, because relation formation refuses unreachable nodes
and unused input bindings.
"""

from hashlib import sha256
import json

P = 2130706433
BASE = 'koala-bear'
EXTENSION = 'koala-bear.ext8-binomial3'
DEGREE = {BASE: 1, EXTENSION: 8}
ZERO = (0,) * 8
ONE = (1,) + (0,) * 7


class Refusal(Exception):
    """A named refusal; `code` is the stable identifier tests assert."""

    def __init__(self, code, detail=''):
        super().__init__(f'{code}: {detail}' if detail else code)
        self.code = code


def scalar(n):
    return (n % P,) + (0,) * 7


def add(a, b):
    return tuple((x + y) % P for x, y in zip(a, b, strict=True))


def neg(a):
    return tuple(-x % P for x in a)


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    product = [0] * 15
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                product[i + j] += x * y
    for i in range(8, 15):
        product[i - 8] += 3 * product[i]
    return tuple(x % P for x in product[:8])


def power(a, exponent):
    result = ONE
    while exponent:
        if exponent & 1:
            result = mul(result, a)
        a, exponent = mul(a, a), exponent >> 1
    return result


def inverses(values, code):
    """Batch inversion; a zero value refuses with `code` and its position."""
    prefix, running = [], ONE
    for index, value in enumerate(values):
        if value == ZERO:
            raise Refusal(code, f'position {index}')
        prefix.append(running)
        running = mul(running, value)
    inverse = power(running, P ** 8 - 2)
    result = [None] * len(values)
    for index in range(len(values) - 1, -1, -1):
        result[index] = mul(inverse, prefix[index])
        inverse = mul(inverse, values[index])
    return result


def encode(field, value):
    """Canonical element encoding: one decimal residue or eight of them."""
    if field == BASE:
        if any(value[1:]):
            raise Refusal('arena-field', 'extension value in the base field')
        return str(value[0])
    return [str(x) for x in value]


def decode(field, element):
    if field == BASE:
        return scalar(int(element))
    return tuple(int(x) for x in element)


class Expr:
    """A node of one arena with its field; arithmetic builds new nodes."""

    def __init__(self, arena, node, field):
        self.arena, self.node, self.field = arena, node, field

    def _operand(self, other):
        if isinstance(other, Expr):
            if other.arena is not self.arena or other.field != self.field:
                raise Refusal('arena-field', f'{self.field} with {other.field}')
            return other
        return self.arena.constant(self.field, other)

    def __add__(self, other):
        return self.arena.node(self.field, ['add', self.node, self._operand(other).node])

    __radd__ = __add__

    def __mul__(self, other):
        return self.arena.node(self.field, ['mul', self.node, self._operand(other).node])

    __rmul__ = __mul__

    def __neg__(self):
        return self.arena.node(self.field, ['neg', self.node])

    def __sub__(self, other):
        return self + -self._operand(other)

    def __rsub__(self, other):
        return self._operand(other) + -self

    def embed(self, field):
        if field == self.field:
            return self
        if (self.field, field) != (BASE, EXTENSION):
            raise Refusal('arena-field', f'no embedding {self.field} -> {field}')
        return self.arena.node(field, ['embed', field, self.node])


class Arena:
    def __init__(self):
        self.inputs, self.bindings, self.nodes, self.fields = [], [], [], []
        self._nodes, self._inputs = {}, {}

    def node(self, field, node):
        key = json.dumps(node)
        if key not in self._nodes:
            self._nodes[key] = len(self.nodes)
            self.nodes.append(node)
            self.fields.append(field)
        return Expr(self, self._nodes[key], field)

    def input(self, field, binding):
        """One arena input per distinct binding, as relation formation requires."""
        key = json.dumps(binding)
        if key not in self._inputs:
            self._inputs[key] = len(self.inputs)
            self.inputs.append(field)
            self.bindings.append(binding)
        index = self._inputs[key]
        if self.inputs[index] != field:
            raise Refusal('arena-field', f'binding {binding} has two fields')
        return self.node(field, ['input', index])

    def constant(self, field, value):
        if value < 0:
            return -self.constant(field, -value)
        return self.node(field, ['constant', field, str(value % P)])

    def finish(self, outputs):
        """The reachable arena for `outputs`, in order, and its input bindings."""
        reached, stack = set(), [o.node for o in outputs]
        while stack:
            index = stack.pop()
            if index in reached:
                continue
            reached.add(index)
            node = self.nodes[index]
            if node[0] in ('add', 'mul'):
                stack += node[1:]
            elif node[0] == 'neg':
                stack.append(node[1])
            elif node[0] == 'embed':
                stack.append(node[2])
        kept = sorted(reached)
        used = sorted({self.nodes[i][1] for i in kept if self.nodes[i][0] == 'input'})
        node_map = {old: new for new, old in enumerate(kept)}
        input_map = {old: new for new, old in enumerate(used)}
        nodes = []
        for index in kept:
            node = self.nodes[index]
            if node[0] == 'input':
                nodes.append(['input', input_map[node[1]]])
            elif node[0] in ('add', 'mul'):
                nodes.append([node[0], node_map[node[1]], node_map[node[2]]])
            elif node[0] == 'neg':
                nodes.append(['neg', node_map[node[1]]])
            elif node[0] == 'embed':
                nodes.append(['embed', node[1], node_map[node[2]]])
            else:
                nodes.append(list(node))
        ring = ['zkc.ring/0', [self.inputs[i] for i in used], nodes,
                [node_map[o.node] for o in outputs]]
        return ring, [self.bindings[i] for i in used]


def evaluate(ring, fetch):
    """Every output of an admitted arena, with `fetch(input_index)` values."""
    values = []
    for node in ring[2]:
        tag = node[0]
        if tag == 'input':
            values.append(fetch(node[1]))
        elif tag == 'constant':
            values.append(scalar(int(node[2])))
        elif tag == 'add':
            values.append(add(values[node[1]], values[node[2]]))
        elif tag == 'mul':
            values.append(mul(values[node[1]], values[node[2]]))
        elif tag == 'neg':
            values.append(neg(values[node[1]]))
        elif tag == 'embed':
            values.append(values[node[2]])
        else:
            raise Refusal('arena-node', tag)
    return [values[o] for o in ring[3]]


def compact(document):
    """The compact JSON text whose SHA-256 is a carrier's structural identity."""
    return json.dumps(document, separators=(',', ':'))


def identity(document):
    return sha256(compact(document).encode()).hexdigest()
