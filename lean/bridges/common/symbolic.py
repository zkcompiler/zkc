"""Untrusted selected-role evaluator that proposes a small open-process term.

The generated imported-to-term equality must be checked by Lean reduction.
This evaluator does not decide semantic equivalence or security.
"""
from snapshot import string, ty


class Unsupported(ValueError):
    pass


def operation(op, args):
    if any(arg is None for arg in args):
        return None
    if sum(map(len, args)) > 200_000:
        raise Unsupported('symbolic expression exceeds the expansion budget')
    tag, *parameters = op
    binary = {'field.add': '+', 'field.subtract': '-', 'field.multiply': '*',
              'group.add': '+', 'bool.and': '&&', 'bool.or': '||',
              'bool.equal': '==', 'bool.not_equal': '!='}
    if tag in binary:
        return f'({args[0]} {binary[tag]} {args[1]})'
    if tag in ('field.equal', 'group.equal'):
        return f'(decide ({args[0]} = {args[1]}))'
    if tag == 'group.scale':
        return f'({args[1]} • {args[0]})'
    if tag == 'field.constant':
        # snapshot rendering has already validated canonical natural literals.
        return f'({parameters[1]} : F)'
    if tag == 'group.identity':
        return '(0 : G)'
    if tag == 'bool.constant':
        return str(parameters[0]).lower()
    if tag == 'bool.xor':
        return f'(xor {args[0]} {args[1]})'
    if tag == 'select':
        return f'(if {args[0]} then {args[1]} else {args[2]})'
    raise Unsupported(f'pure operation {tag}')


def process(data, role, initial):
    environment = list(initial)
    nodes = []
    for instruction in data[8]:
        tag, *args = instruction
        if tag == 'pure':
            value = operation(args[0], [environment[i] for i in args[1]])
        elif tag == 'restrict':
            value = environment[args[2]] if role in args[0] else None
        elif tag == 'exchange':
            site, sender, receiver, dtype, index = args
            if role == receiver:
                value = f'reply{len(nodes)}'
                nodes.append(('call', f'.receive ({ty(dtype)}) {string(site)} {sender}', value))
            elif role == sender:
                value = environment[index]
                if value is None:
                    nodes.append(('stop', '.incomplete'))
                else:
                    nodes.append(('call', f'.send (ty := {ty(dtype)}) {string(site)} {receiver} {value}', '_'))
            else:
                value = None
        elif tag == 'draw':
            site, owner, domain, index = args
            value = None
            if role == owner:
                service = environment[index]
                if service is None:
                    nodes.append(('stop', '.incomplete'))
                else:
                    value = f'reply{len(nodes)}'
                    nodes.append(('call', f'.query {string(site)} {string(domain)} (.cons {service} .nil)', value))
        elif tag == 'guard':
            _, owner, index = args
            if role == owner:
                condition = environment[index]
                nodes.append(('stop', '.incomplete') if condition is None else ('guard', condition))
            continue
        elif tag == 'statement':
            # Statement metadata has no runtime effect in this interpretation.
            continue
        else:
            raise Unsupported(f'instruction {tag}')
        environment.insert(0, value)
    result = environment[data[9]] if role in data[7] else None
    body = '.done none' if result is None else f'.done (some {result})'
    for node in reversed(nodes):
        if node[0] == 'call':
            body = f'.call ({node[1]}) fun {node[2]} =>\n{body}'
        elif node[0] == 'guard':
            body = f'if {node[1]} then\n{indent(body)}\nelse .halt .reject'
        else:
            body = f'.halt {node[1]}'
        if len(body) > 1_000_000:
            raise Unsupported('symbolic process exceeds the expansion budget')
    return body


def indent(text):
    return '\n'.join('  ' + line for line in text.splitlines())


def variable(index):
    return '.there (' * index + '.here' + ')' * index


def operands(indices):
    result = '.nil'
    for index in reversed(indices):
        result = f'.cons ({variable(index)}) ({result})'
    return result


def program(data):
    """Transparent typed syntax; its elaboration equation is separately proved."""
    from snapshot import op, seq
    body = f'.ret ({variable(data[9])})'
    for instruction in reversed(data[8]):
        tag, *args = instruction
        if tag == 'pure':
            head = f'.calculate (.letOp ({op(args[0])}) ({operands(args[1])}) (.ret .here))'
        elif tag == 'restrict':
            head = f'.calculate (.restrict (selected {seq(args[0])}) ({variable(args[2])}) (.ret .here))'
        elif tag == 'exchange':
            head = f'.exchange {string(args[0])} {args[1]} {args[2]} ({variable(args[4])})'
        elif tag == 'draw':
            head = f'.query {string(args[0])} {args[1]} {string(args[2])} ({operands([args[3]])})'
        elif tag == 'guard':
            head = f'.guard {string(args[0])} {args[1]} ({variable(args[2])})'
        elif tag == 'statement':
            head = f'.statement {string(args[0])} {seq(args[2])} ({operands(args[3])})'
        else:
            raise Unsupported(tag)
        body = head + ' (\n' + body + ')'
    return body
