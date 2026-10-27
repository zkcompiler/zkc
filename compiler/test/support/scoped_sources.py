"""Build test fixtures directly in the scoped Func/Exec source language."""


def invocation(operation, inputs, outputs, attributes, values=None, names=None, label='value'):
    values = values if values is not None else [f'%a{i}' for i in range(len(inputs))]
    names = names if names is not None else ['%r'] if len(outputs) == 1 else [f'%r{i}' for i in range(len(outputs))]
    outcome = f'!exec.outcome<({",".join(outputs)})>' if outputs else '!exec.outcome<>'
    operands = ','.join(['%scope', *values])
    types = ','.join(['!runtime.scope', *inputs])
    arguments = ','.join(f'{name}:{ty}' for name, ty in zip(names, outputs))
    return f'''%{label}_attempt = "{operation}"({operands}) {{{attributes}}} : ({types})->{outcome}
"exec.dispatch"(%{label}_attempt)[^{label},^failed] : ({outcome})->()
^{label}({arguments}):'''


def scoped_function(name, inputs, outputs, body, results, private=False):
    args = ','.join(['%scope:!runtime.scope', *[f'%a{i}:{t}' for i, t in enumerate(inputs)]])
    outs = ','.join(outputs)
    outcome = f'!exec.outcome<({outs})>' if outputs else '!exec.outcome<>'
    failure = f'''^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->{outcome}
func.return %failure : {outcome}''' if '^failed' in body else ''
    return f'''func.func {'private ' if private else ''}@{name}({args})->{outcome} attributes {{no_inline,runtime.origin=["{name}",[]]}} {{
{body}
%done = "exec.returned"({','.join(results)}) : ({outs})->{outcome}
func.return %done : {outcome}
{failure}
}}'''
