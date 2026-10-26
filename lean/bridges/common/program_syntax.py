"""Render transparent typed Common program constructors without evaluating them.

Admission and correspondence with the imported program are checked in Lean.
"""
from snapshot import string


def indent(text):
    return '\n'.join('  ' + line for line in text.splitlines())


def variable(index, context_size):
    if type(index) is not int or not 0 <= index < context_size:
        raise ValueError('program variable is outside the binding context')
    return '.there (' * index + '.here' + ')' * index


def operands(indices, context_size):
    result = '.nil'
    for index in reversed(indices):
        result = f'.cons ({variable(index, context_size)}) ({result})'
    return result


def program(data):
    """Transparent typed syntax; its elaboration equation is separately proved."""
    from snapshot import op, seq
    # Count constructor bindings, independently of participant or runtime values.
    binding_tags = {'pure', 'restrict', 'exchange', 'draw'}
    context_size = len(data[4]) + sum(instruction[0] in binding_tags for instruction in data[8])
    body = f'.ret ({variable(data[9], context_size)})'
    for instruction in reversed(data[8]):
        tag, *args = instruction
        context_size -= tag in binding_tags
        if tag == 'pure':
            head = f'.calculate (.letOp ({op(args[0])}) ({operands(args[1], context_size)}) (.ret .here))'
        elif tag == 'restrict':
            head = f'.calculate (.restrict (selected {seq(args[0])}) ({variable(args[2], context_size)}) (.ret .here))'
        elif tag == 'exchange':
            head = f'.exchange {string(args[0])} {args[1]} {args[2]} ({variable(args[4], context_size)})'
        elif tag == 'draw':
            head = f'.query {string(args[0])} {args[1]} {string(args[2])} ({operands([args[3]], context_size)})'
        elif tag == 'guard':
            head = f'.guard {string(args[0])} {args[1]} ({variable(args[2], context_size)})'
        elif tag == 'statement':
            head = f'.statement {string(args[0])} {seq(args[2])} ({operands(args[3], context_size)})'
        else:
            raise ValueError(f'unsupported program instruction {tag}')
        body = head + ' (\n' + body + ')'
    return body
