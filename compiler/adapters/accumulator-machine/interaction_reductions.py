"""Challenge-dependent interaction reductions as staged-program transformations.

`Reduction` reads a Bundle's channel and interaction descriptors and emits a
one-phase `zkc.relation-staged/0` program, either LogUp sums or grand products,
together with an honest assignment builder. Nothing here names a particular
Bundle; the accumulator machine is one consumer. The README states the
definitions, premises and what the staged predicate does not establish.

Each reduced channel draws two challenges in this order: a shift `gamma` and a
compression `delta`. A tuple `t` of arity `k` compresses to the fingerprint
`fp(t) = t_0 + delta*t_1 + ... + delta^(k-1)*t_(k-1)`, and the record's
denominator or factor is `gamma - fp(t)`.

The program is instantiated for one presence vector. Absent tables contribute
no staged columns and no claims, so the verifier must select the program that
matches the instance's presence before evaluating it.
"""

from hashlib import sha256

from ring_arena import (BASE, DEGREE, EXTENSION, ONE, P, ZERO, Arena, Refusal, add, decode, encode,
                        evaluate, identity, inverses, mul, neg, scalar, sub)

LOGUP = 'logup'
PRODUCT = 'grand-product'
EMPTY_RING = ['zkc.ring/0', [], [], []]


def maximum_height(height):
    return height[1] if height[0] == 'fixed' else height[2]


class Record:
    """One interaction of a base table: channel, side sign, tuple and count outputs."""

    def __init__(self, table, index, interaction, channels):
        kind, channel = interaction[0], interaction[1]
        if kind == 'multiset':
            _, _, locality, scope, side, tuple_outputs, count, bound = interaction
            self.sign = 1 if side == 'push' else -1
            self.side = side
        else:
            _, _, locality, scope, tuple_outputs, count, _ = interaction
            self.sign, self.side, bound = 1, 'push', None
        self.table, self.index, self.kind, self.channel = table, index, kind, channel
        self.scope, self.locality, self.bound = scope, locality, bound
        self.tuple_outputs, self.count = tuple_outputs, count
        self.tuple_field, self.count_field = channels[channel][2][0], channels[channel][3]


class Reduction:
    """A staged reduction of every channel's interactions over present tables.

    `presence` lists, per Bundle table, whether the instance supplies it.
    Bounded failures refuse with a named `Refusal`; nothing is silently
    skipped.
    """

    def __init__(self, kind, bundle, presence, challenge_field=EXTENSION):
        if kind not in (LOGUP, PRODUCT):
            raise Refusal('reduction-kind', kind)
        if challenge_field not in DEGREE:
            raise Refusal('reduction-field', challenge_field)
        _, self.publics, self.channels, self.tables = bundle
        if len(presence) != len(self.tables):
            raise Refusal('reduction-presence', 'one entry per table')
        for table, present in zip(self.tables, presence):
            if table[1] == 'required' and not present:
                raise Refusal('reduction-presence', f'required table {table[0]} is absent')
        self.kind, self.bundle, self.presence = kind, bundle, list(presence)
        self.field, self.relation = challenge_field, identity(bundle)
        self.records = [[Record(t, i, x, self.channels) for i, x in enumerate(table[8])]
                        for t, table in enumerate(self.tables)]
        for records in self.records:
            for r in records:
                self._admit(r)
        self.challenge_names = []
        for channel in self.channels:
            self.challenge_names += [f'{channel[0]}-shift', f'{channel[0]}-compression']
        self._layout()
        self._premises()
        self.program = self._program()
        self.identity = identity(self.program)

    def _admit(self, r):
        if r.scope != ['all']:
            raise Refusal('reduction-scope', f'{self.tables[r.table][0]} interaction {r.index}')
        if r.locality != ['global']:
            raise Refusal('reduction-locality', f'{self.tables[r.table][0]} interaction {r.index}')
        if r.kind == 'multiset' and r.bound != 1:
            # A natural count above one needs a canonical-range premise that the
            # staged format cannot record; see the README.
            raise Refusal('reduction-multiplicity-bound', f'bound {r.bound}')
        if r.kind == 'field-balance' and self.kind == PRODUCT:
            raise Refusal('reduction-channel-kind', 'grand products need natural Boolean counts')
        if self.field == BASE and EXTENSION in (r.tuple_field, r.count_field):
            raise Refusal('reduction-field', 'extension tuple with base-field challenges')

    def present_records(self, t):
        return self.records[t] if self.presence[t] else []

    def _layout(self):
        """Per-table auxiliary columns and the phase's claim slots, in order."""
        self.columns, self.claims, self.claim_index = [], [], {}
        for t, table in enumerate(self.tables):
            records, columns = self.present_records(t), []
            if self.kind == LOGUP:
                columns += [('inverse', r) for r in records]
                columns += [('sum', c) for c in sorted({r.channel for r in records})]
            else:
                columns += [('product', key) for key in
                            sorted({(r.channel, r.side) for r in records}, key=side_order)]
            self.columns.append(columns)
            for role, key in columns:
                if role == 'inverse':
                    continue
                name = (f'{table[0]}-{self.channels[key][0]}-sum' if role == 'sum' else
                        f'{table[0]}-{self.channels[key[0]][0]}-{key[1]}-product')
                self.claim_index[(t, key)] = len(self.claims)
                self.claims.append(name)
        if self.kind == PRODUCT:
            for c, channel in enumerate(self.channels):
                if self.channel_records(c):
                    self.claim_index[('inverse', c)] = len(self.claims)
                    self.claims.append(f'{channel[0]}-product-inverse')

    def channel_records(self, c):
        return [r for t in range(len(self.tables)) for r in self.present_records(t) if r.channel == c]

    def _premises(self):
        self.premises = []
        for c, channel in enumerate(self.channels):
            records = self.channel_records(c)
            if not records or channel[1] != 'multiset':
                continue
            for r in records:
                self.premises.append(['boolean', 0, r.table, r.count, r.scope])
            if self.kind == LOGUP:
                totals = {side: sum(maximum_height(self.tables[r.table][2]) * r.bound
                                    for r in records if r.side == side) for side in ('push', 'pull')}
                bound = max(totals.values())
                if bound >= P:
                    raise Refusal('reduction-characteristic', f'{channel[0]} counts reach {bound}')
                self.premises.append(['characteristic-exceeds', channel[3], bound])

    def _program(self):
        self.assertion_names, tables = [], []
        for t, table in enumerate(self.tables):
            entry, names = self._table(t, table)
            tables.append(entry)
            self.assertion_names.append(names)
        challenges = [[name, self.field] for name in self.challenge_names]
        claims = [[name, self.field] for name in self.claims]
        return ['zkc.relation-staged/0', self.relation, [[challenges, claims, tables]],
                self._global(), self.premises]

    def _challenge(self, arena, c, which):
        return arena.input(self.field, ['challenge', 1, 2 * c + which])

    def _fingerprint(self, arena, r, values):
        delta = self._challenge(arena, r.channel, 1)
        coordinates = [v.embed(self.field) for v in values]
        fingerprint = coordinates[-1]
        for value in reversed(coordinates[:-1]):
            fingerprint = fingerprint * delta + value
        return fingerprint

    def _table(self, t, table):
        columns = self.columns[t]
        if not columns:
            return [[], EMPTY_RING, [], []], []
        arena, memo = Arena(), {}
        _, _, _, _, groups, ring, bindings, _, _ = table

        def base(output):
            return transplant(arena, ring, bindings, output, staged_binding, memo)

        def auxiliary(role, key, offset=0):
            return arena.input(self.field, ['read', 1, 0, str(offset), columns.index((role, key))])

        def claim(key):
            return arena.input(self.field, ['claim', 1, self.claim_index[(t, key)]])

        outputs, names = [], []

        def check(name, scope, expression):
            names.append(name)
            outputs.append((scope, expression))

        records = self.present_records(t)
        label = {c: self.channels[c][0] for c in range(len(self.channels))}
        if self.kind == LOGUP:
            terms = {}
            for r in records:
                gamma = self._challenge(arena, r.channel, 0)
                fingerprint = self._fingerprint(arena, r, [base(o) for o in r.tuple_outputs])
                count = base(r.count).embed(self.field)
                inverse = auxiliary('inverse', r)
                check(f'{label[r.channel]} interaction {r.index} inverts its denominator', r.scope,
                      count * (inverse * (gamma - fingerprint) - 1))
                term = count * inverse
                terms.setdefault(r.channel, []).append(term if r.sign > 0 else -term)
            for role, c in columns:
                if role != 'sum':
                    continue
                contribution = total(terms[c])
                running = auxiliary('sum', c)
                check(f'{label[c]} sum starts with the first row', ['first'], running - contribution)
                check(f'{label[c]} sum accumulates each row', ['interior', 1, 0],
                      running - auxiliary('sum', c, -1) - contribution)
                check(f'{label[c]} sum ends at its claim', ['last'], running - claim(c))
        else:
            for role, key in columns:
                c, side = key
                factors = []
                for r in records:
                    if (r.channel, r.side) != key:
                        continue
                    gamma = self._challenge(arena, r.channel, 0)
                    fingerprint = self._fingerprint(arena, r, [base(o) for o in r.tuple_outputs])
                    count = base(r.count).embed(self.field)
                    factors.append(count * (gamma - fingerprint) + 1 - count)
                row = product(factors)
                running = auxiliary('product', key)
                check(f'{label[c]} {side} product starts with the first row', ['first'], running - row)
                check(f'{label[c]} {side} product accumulates each row', ['interior', 1, 0],
                      running - auxiliary('product', key, -1) * row)
                check(f'{label[c]} {side} product ends at its claim', ['last'], running - claim(key))
        ring_out, bindings_out = arena.finish([e for _, e in outputs])
        groups_out = [[f'{self.kind}-columns', self.field, len(columns)]]
        assertions = [[i, scope] for i, (scope, _) in enumerate(outputs)]
        return [groups_out, ring_out, bindings_out, assertions], names

    def _global(self):
        arena, outputs, self.global_names = Arena(), [], []

        def claim(index):
            return arena.input(self.field, ['claim', 1, index])

        for c, channel in enumerate(self.channels):
            keys = [(t, key) for (t, key) in self.claim_index if t != 'inverse'
                    and (key == c or (isinstance(key, tuple) and key[0] == c))]
            if not keys:
                continue
            if self.kind == LOGUP:
                outputs.append(total([claim(self.claim_index[k]) for k in keys]))
                self.global_names.append(f'{channel[0]} sums close')
            else:
                sides = {side: product([claim(self.claim_index[k]) for k in keys if k[1][1] == side],
                                       arena, self.field)
                         for side in ('push', 'pull')}
                outputs.append(sides['push'] - sides['pull'])
                self.global_names.append(f'{channel[0]} products agree')
                outputs.append(sides['push'] * claim(self.claim_index[('inverse', c)]) - 1)
                self.global_names.append(f'{channel[0]} product is nonzero')
        if not outputs:
            return [EMPTY_RING, [], []]
        ring, bindings = arena.finish(outputs)
        return [ring, bindings, list(range(len(outputs)))]

    # The honest prover.

    def assign(self, configuration, instance, witness, challenges, check_premises=True,
               refuse_zero=True):
        """The assignment for actual challenge values, in `challenge_names` order.

        Refuses when the instance's presence differs from the program's, when a
        recorded Boolean premise is false, or when an active denominator, factor
        or closing product is zero. The two flags exist so tests can build the
        assignment a prover would have to supply anyway and show what the
        staged predicate then decides; a zero then gets the inverse zero.
        """
        if len(challenges) != len(self.challenge_names):
            raise Refusal('reduction-challenge-count')
        challenges = [tuple(v) for v in challenges]
        presence = [entry[0] == 'present' for entry in instance[3]]
        if presence != self.presence:
            raise Refusal('reduction-presence', 'instance presence differs from the program')
        publics = [decode(slot[1], v) for slot, v in zip(self.publics, instance[2])]
        claims, tables = [None] * len(self.claims), []
        closing = {}
        for t, table in enumerate(self.tables):
            if not self.presence[t]:
                tables.append(None)
                continue
            columns = self.columns[t]
            if not columns:
                tables.append([])
                continue
            height, data = table_data(table, t, configuration, instance, witness)
            rows = self._record_values(t, table, height, data, publics)
            if check_premises:
                for r in self.present_records(t):
                    if r.kind == 'multiset' and any(rows[i][r][1] not in (ZERO, ONE) for i in range(height)):
                        raise Refusal('reduction-boolean-count', f'{table[0]} interaction {r.index}')
            matrix = [[None] * len(columns) for _ in range(height)]
            if self.kind == LOGUP:
                self._logup_rows(t, columns, rows, challenges, matrix, claims, refuse_zero)
            else:
                self._product_rows(t, columns, rows, challenges, matrix, claims, closing, refuse_zero)
            tables.append([[encode(self.field, v) for row in matrix for v in row]])
        if self.kind == PRODUCT:
            for c, push in closing.items():
                if push == ZERO and not refuse_zero:
                    claims[self.claim_index[('inverse', c)]] = ZERO
                    continue
                # A zero product has a zero factor, which refused above.
                (claims[self.claim_index[('inverse', c)]],) = inverses([push], 'reduction-zero-factor')
        values = [encode(self.field, v) for v in challenges]
        return ['zkc.relation-staged-assignment/0', self.identity,
                [[values, [encode(self.field, v) for v in claims], tables]]]

    def _record_values(self, t, table, height, data, publics):
        """Per row and record: the tuple values and the count, from the base arena."""
        arena, memo = Arena(), {}
        _, _, _, read_model, groups, ring, bindings, _, _ = table
        records = self.present_records(t)
        outputs = []
        for r in records:
            outputs += [transplant(arena, ring, bindings, o, lambda b: b, memo)
                        for o in r.tuple_outputs + [r.count]]
        probe, probe_bindings = arena.finish(outputs)
        rows = []
        for i in range(height):
            def fetch(index):
                binding = probe_bindings[index]
                if binding[0] == 'public':
                    return publics[binding[1]]
                _, group, offset, column = binding
                row = i + int(offset)
                row = row % height if read_model == 'cyclic' else row
                return data[group][row * groups[group][3] + column]
            values, position, row = evaluate(probe, fetch), 0, {}
            for r in records:
                width = len(r.tuple_outputs)
                row[r] = (values[position:position + width], values[position + width])
                position += width + 1
            rows.append(row)
        return rows

    def _fingerprint_value(self, r, values, challenges):
        delta = challenges[2 * r.channel + 1]
        fingerprint = values[-1]
        for value in reversed(values[:-1]):
            fingerprint = add(mul(fingerprint, delta), value)
        return fingerprint

    def _logup_rows(self, t, columns, rows, challenges, matrix, claims, refuse_zero):
        active = []
        for i, row in enumerate(rows):
            for r, (values, count) in row.items():
                denominator = sub(challenges[2 * r.channel], self._fingerprint_value(r, values, challenges))
                if count != ZERO and (refuse_zero or denominator != ZERO):
                    active.append((i, r, denominator))
                else:
                    matrix[i][columns.index(('inverse', r))] = ZERO
        found = inverses([d for _, _, d in active], 'reduction-zero-denominator')
        for (i, r, _), inverse in zip(active, found):
            matrix[i][columns.index(('inverse', r))] = inverse
        for role, c in columns:
            if role != 'sum':
                continue
            position, running = columns.index((role, c)), ZERO
            for i, row in enumerate(rows):
                for r, (_, count) in row.items():
                    if r.channel == c:
                        term = mul(count, matrix[i][columns.index(('inverse', r))])
                        running = add(running, term if r.sign > 0 else neg(term))
                matrix[i][position] = running
            claims[self.claim_index[(t, c)]] = running

    def _product_rows(self, t, columns, rows, challenges, matrix, claims, closing, refuse_zero):
        for role, key in columns:
            position, running = columns.index((role, key)), ONE
            for i, row in enumerate(rows):
                for r, (values, count) in row.items():
                    if (r.channel, r.side) != key:
                        continue
                    gamma = challenges[2 * r.channel]
                    shifted = sub(gamma, self._fingerprint_value(r, values, challenges))
                    factor = add(mul(count, shifted), sub(ONE, count))
                    if factor == ZERO and refuse_zero:
                        raise Refusal('reduction-zero-factor', f'{self.tables[t][0]} row {i}')
                    running = mul(running, factor)
                matrix[i][position] = running
            claims[self.claim_index[(t, key)]] = running
            if key[1] == 'push':
                closing[key[0]] = mul(closing.get(key[0], ONE), running)
            else:
                closing.setdefault(key[0], ONE)


def side_order(key):
    return (key[0], 0 if key[1] == 'push' else 1)


def total(terms):
    result = terms[0]
    for term in terms[1:]:
        result = result + term
    return result


def product(factors, arena=None, field=None):
    if not factors:
        return arena.constant(field, 1)
    result = factors[0]
    for factor in factors[1:]:
        result = result * factor
    return result


def staged_binding(binding):
    if binding[0] == 'public':
        return binding
    return ['read', 0, *binding[1:]]


def transplant(arena, ring, bindings, output, rebind, memo):
    """Copy one base-arena output into `arena`, rebinding its inputs."""
    root = ring[3][output]
    needed, stack = set(), [root]
    while stack:
        index = stack.pop()
        if index in needed or index in memo:
            continue
        needed.add(index)
        node = ring[2][index]
        stack += {'add': node[1:], 'mul': node[1:], 'neg': node[1:], 'embed': node[2:]}.get(node[0], [])
    for index in sorted(needed):
        node = ring[2][index]
        tag = node[0]
        if tag == 'input':
            memo[index] = arena.input(ring[1][node[1]], rebind(bindings[node[1]]))
        elif tag == 'constant':
            memo[index] = arena.constant(node[1], int(node[2]))
        elif tag == 'add':
            memo[index] = memo[node[1]] + memo[node[2]]
        elif tag == 'mul':
            memo[index] = memo[node[1]] * memo[node[2]]
        elif tag == 'neg':
            memo[index] = -memo[node[1]]
        else:
            memo[index] = memo[node[2]].embed(node[1])
    return memo[root]


def table_data(table, t, configuration, instance, witness):
    """The admitted height and every group's decoded elements, in group order."""
    name, _, height, _, groups = table[:5]
    if height[0] == 'fixed':
        h = height[1]
    elif height[0] == 'config':
        h = configuration[2][t][0]
    else:
        h = instance[3][t][1]
    sources = {'config': iter(configuration[2][t][1]),
               'public': iter(instance[3][t][2]),
               'witness': iter(witness[2][t])}
    data = [[decode(group[2], v) for v in next(sources[group[1]])] for group in groups]
    return h, data


def fixture_challenges(label, count, field=EXTENSION):
    """Fixed, reproducible test values; not drawn from any transcript."""
    values = []
    for index in range(count):
        digest = sha256(f'zkc.accumulator-machine fixture challenge/0:{label}:{index}'.encode()).digest()
        coordinates = [int.from_bytes(digest[4 * j:4 * j + 4], 'little') % P for j in range(8)]
        values.append(tuple(coordinates) if field == EXTENSION else scalar(coordinates[0]))
    return values
