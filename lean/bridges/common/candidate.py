"""Restricted pure expression proposals for the reviewed certificate renderer.

A generator never supplies Lean commands, tactics, imports, audit code or subject
bindings. This lexical subset contains only pure constructors and scalar terms;
Lean still checks typing and every semantic equation. Python generator execution,
the renderer, the registry and the selected Lean toolchain remain trusted code.
"""
import json
import re

from request_support import require


TOKEN = re.compile(r'\s+|"(?:[^"\\\x00-\x1f]|\\["\\/bfnrt]|\\u[0-9a-fA-F]{4})*"'
                   r'|\.[A-Za-z][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_.]*|[0-9]+'
                   r'|--|=>|:=|&&|\|\||==|!=|[()\[\],:+*=•-]')
PROGRAM_NAMES = {
    '.ret', '.here', '.there', '.nil', '.cons', '.calculate', '.letOp', '.restrict',
    '.exchange', '.query', '.guard', '.statement', 'selected', 'true', 'false',
    '.fieldConstant', '.fieldAdd', '.fieldSubtract', '.fieldMultiply', '.fieldEqual',
    '.groupIdentity', '.groupAdd', '.groupScale', '.groupEqual', '.booleanConstant',
    '.booleanAnd', '.booleanOr', '.booleanXor', '.booleanEqual', '.booleanNotEqual',
    '.select', '.boolean', '.field', '.group', '.service',
}
PROCESS_NAMES = {
    '.done', '.halt', '.call', '.receive', '.send', '.query', '.cons', '.nil',
    '.boolean', '.field', '.group', '.service', '.incomplete', '.reject',
    'F', 'G', 'ty', '_', 'if', 'then', 'else', 'fun', 'some', 'none', 'true', 'false',
    'decide', 'xor',
}


def expression(text, kind, inputs=()):
    """Reject active Lean syntax before inserting one parenthesized expression.

In particular, comments, escaped identifiers, quotation, macros, attributes,
commands and tactic blocks are absent. No imported or request-selected names
can enlarge this set; input names come only from the reviewed contract registry.
"""
    require(type(text) is str and len(text) <= 1_000_000,
            'candidate-syntax', 'Expected a bounded pure expression proposal')
    names = PROGRAM_NAMES if kind == 'program' else PROCESS_NAMES | set(inputs)
    position = 0
    balance = []
    for match in TOKEN.finditer(text):
        require(match.start() == position, 'candidate-syntax', 'Unrecognized candidate token')
        token = match.group()
        position = match.end()
        if token.isspace():
            continue
        require(token != '--', 'candidate-syntax', 'Candidate comments are not permitted')
        if token.startswith('"'):
            value = json.loads(token)
            require(0 < len(value) <= 512 and all(32 <= ord(c) <= 126 for c in value),
                    'candidate-syntax', 'Invalid candidate string')
        elif token[0].isalpha() or token[0] in '._':
            require(token in names or (kind == 'process' and re.fullmatch(r'reply[0-9]+', token)),
                    'candidate-syntax', 'Candidate identifier is outside the pure expression vocabulary')
        elif token[0].isdigit():
            require(len(token) <= 512, 'candidate-syntax', 'Candidate numeral exceeds the bounded profile')
        elif token in ('(', '['):
            balance.append(token)
        elif token in (')', ']'):
            require(bool(balance) and balance.pop() == {')': '(', ']': '['}[token],
                    'candidate-syntax', 'Unbalanced candidate expression')
    require(position == len(text) and not balance, 'candidate-syntax', 'Incomplete candidate expression')
    # Parentheses prevent a proposal from extending an enclosing declaration.
    return '(\n' + '\n'.join('  ' + line for line in text.splitlines()) + '\n)'


def program_expression(text):
    return expression(text, 'program')
