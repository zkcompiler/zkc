"""Notation inventory options and diagnostics on the compiler CLI."""
import json

from cases import case, counted
from commands import Commands
from tools import compiler, records

out = records()
commands = Commands(out)
source = out / 'notation.zkc'
source.write_text('''module notation;
pub math fn add<F:Field>(lhs:F,rhs:F)->F{return lhs+rhs;}
pub operator infixl(70) ⊙ = add;
pub math fn shown<F:Field>(lhs:F,rhs:F)->F{return lhs ⊙ rhs;}
math fn hidden<F:Field>(lhs:F,rhs:F)->F{return lhs ⊙ rhs;}
''', encoding='utf-8')
args = ['--source-format=zkc', f'--module=notation={source}']

for options in [[], ['--notation-private'], ['--notation-installation'],
                ['--notation-private', '--notation-installation']]:
    with case(f'notation inventory visibility {options}'):
        report = json.loads(commands.run(
            [compiler, 'language-check', *args, '--notations', *options]))
        view = report['notations']
        assert view['format'] == 'zkc.notations/0'
        assert view['include_private'] == ('--notation-private' in options)
        assert view['include_installation'] == ('--notation-installation' in options)
        owners = {value['owner'] for value in view['occurrences']}
        assert 'notation::shown' in owners
        assert ('notation::hidden' in owners) == ('--notation-private' in options)

for flag in ['--notations', '--notation-private', '--notation-installation']:
    with case(f'duplicate and malformed {flag}'):
        commands.run([compiler, 'language-check', *args, flag, flag],
                     refuses='source.options')
        commands.run([compiler, 'language-check', *args, f'{flag}=true'],
                     refuses='source.options')
    for command in ['language-emit', 'language-interface', 'language-bundle',
                    'language-package']:
        with case(f'{flag} is unavailable on {command}'):
            commands.run([compiler, command, *args, flag], refuses='source.options')

for flag in ['--notation-private', '--notation-installation']:
    with case(f'{flag} requires an inventory request'):
        commands.run([compiler, 'language-check', *args, flag],
                     refuses='source.options')

with case('declaration and notation views may be requested together'):
    report = json.loads(commands.run(
        [compiler, 'language-check', *args, '--notations', '--declarations']))
    assert report['declarations'] and report['notations']['bindings']

counted()
