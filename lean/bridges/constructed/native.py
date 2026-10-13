"""Bounded interpreter of actual generic native SSA, independent of export indices.

Z/97 arithmetic and a state-sensitive deterministic transcript are test meanings,
not the BLS curve or Merlin. Primitive replies become exact Lean replay controls.
"""
import re

OP = re.compile(r'(?:(%[A-Za-z0-9_]+)(?::(\d+))? = )?"([^"]+)"\(([^)]*)\)')
REF = re.compile(r'%[A-Za-z0-9_]+(?:#\d+)?')


def definitions(text):
    result = {}
    lines = iter(text.splitlines())
    for line in lines:
        if '"protocol.participant"()' not in line and '"local.func"()' not in line:
            continue
        name = re.search(r'sym_name = "([^"]+)"', line)[1]
        arguments = next(lines)
        args = re.findall(r'(%[A-Za-z0-9_]+):', arguments) if '^bb0(' in arguments else []
        body = [] if '^bb0(' in arguments else [arguments.strip()]
        indentation = len(line) - len(line.lstrip())
        for bodyline in lines:
            if bodyline.startswith(' ' * indentation + '})'):
                break
            if bodyline.strip():
                body.append(bodyline.strip())
        result[name] = (args, body)
    return result


class Stopped(Exception):
    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


class Native:
    def __init__(self, text, receive, stop_at=None, stop_reason='abort'):
        self.definitions = definitions(text)
        self.receive = receive
        self.received = 0
        self.challenges = []
        self.entries = []
        self.stop_at = stop_at
        self.stop_reason = stop_reason
        self.buffers = {}

    def buffer(self, value):
        token = 100000 + len(self.buffers)
        self.buffers[token] = value
        return token

    def primitive(self, name, args, line):
        if name == 'data.exec.bytes_empty':
            return [self.buffer(b'')]
        if name == 'data.exec.bytes_length':
            return [len(self.buffers[args[0]])]
        if name == 'data.exec.bytes_slice':
            data, start, count = self.buffers[args[0]], args[1], args[2]
            if start + count > len(data):
                raise Stopped('refused')
            return [self.buffer(data[start:start + count])]
        if name in ('crypto.exec.encoding_field_from_be', 'crypto.exec.encoding_group_from_compressed'):
            data = self.buffers[args[0]]
            count = 32 if name.endswith('field_from_be') else 48
            value = int.from_bytes(data, 'big')
            valid = len(data) == count and value < 97
            return [int(valid), value if valid else 0]
        if name == 'algebra.exec.index_constant':
            return [int(re.search(r'parameters = \["([0-9]+)"\]', line)[1])]
        if name == 'algebra.exec.index_add':
            return [args[0] + args[1]]
        if name == 'algebra.exec.index_equal':
            return [int(args[0] == args[1])]
        if name == 'protocol.receive':
            value = self.receive(self.received, self.challenges)
            self.received += 1
            return [value]
        if name == 'algebra.exec.indices_empty':
            return [0]
        if name == 'crypto.exec.indexed_transcript_observe_data':
            state, value, coordinate = args
            return [(state * 131 + value * 17 + coordinate + 1) % 65521]
        if name == 'crypto.exec.indexed_transcript_challenge':
            state, coordinate = args
            challenge = (state + coordinate) % 97
            self.challenges.append(challenge)
            return [challenge, (state * 137 + coordinate + 3) % 65521]
        if name in ('algebra.field_add', 'algebra.group_add'):
            return [(args[0] + args[1]) % 97]
        if name == 'algebra.field_subtract':
            return [(args[0] - args[1]) % 97]
        if name in ('algebra.field_multiply', 'algebra.group_scale'):
            return [(args[0] * args[1]) % 97]
        if name in ('algebra.field_equal', 'algebra.group_equal', 'arith.cmpi'):
            return [int(args[0] == args[1])]
        if name == 'arith.constant':
            token = re.search(r'value = (true|false|[0-9]+)', line)[1]
            return [int(token == 'true') if token in ('true', 'false') else int(token)]
        if name == 'algebra.field_constant':
            return [int(re.search(r'value = "([0-9]+)"', line)[1]) % 97]
        raise ValueError('native-interpreter-operation: ' + name)

    def call(self, name, inputs):
        formals, lines = self.definitions[name]
        if len(formals) != len(inputs):
            raise ValueError('native-interpreter-arity')
        env = dict(zip(formals, inputs))
        pending = iter(lines)
        for line in pending:
            match = OP.match(line)
            if not match:
                raise ValueError('native-interpreter-syntax: ' + line)
            result, count, operation, operands = match.groups()
            args = [env[r] for r in REF.findall(operands)]
            if operation in ('local.return', 'protocol.finish'):
                return args
            if operation == 'local.if':
                tail = [next(pending) for _ in range(4)]
                if ('"local.yield"()' not in tail[0] or
                        '"local.stop"()' not in tail[2] or 'reason = "reject"' not in tail[2]):
                    raise ValueError('native-interpreter-control')
                if args != [1]:
                    raise Stopped('reject')
                continue
            if operation == 'local.guard':
                if args != [1]:
                    raise Stopped('reject')
                continue
            if operation == 'local.stop':
                raise Stopped(re.search(r'reason = "([^"]+)"', line)[1])
            if operation == 'local.call':
                output = self.call(re.search(r'callee = @([A-Za-z0-9_]+)', line)[1], args)
            else:
                asked = [operation, args]
                if len(self.entries) == self.stop_at:
                    self.entries.append([asked, ['stop', self.stop_reason]])
                    raise Stopped(self.stop_reason)
                try:
                    output = self.primitive(operation, args, line)
                except Stopped as stopped:
                    self.entries.append([asked, ['stop', stopped.reason]])
                    raise
                self.entries.append([asked, ['return', output]])
            expected = int(count) if count else (1 if result else 0)
            if expected != len(output):
                raise ValueError('native-interpreter-result-arity')
            for i, value in enumerate(output):
                env[result + (f'#{i}' if expected > 1 else '')] = value
        raise ValueError('native-interpreter-return')

    def run(self, participant, inputs):
        try:
            return ['returned', self.call(participant, inputs)]
        except Stopped as stopped:
            return ['stopped', stopped.reason]
