"""Mathematical notation uses ordinary calls through the source compiler and Host."""

import pytest

from entry import Entry
from input_files import input_files


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('symbolic', [False, True])
def test_notation_operands_execute_once_in_source_order(
    toolchain, journal, directory, flags, symbolic,
):
    source = '''module sample;
fn digits(a:index,b:index,c:index)->index{return a*100+b*10+c;}
fn reversed(a:index,b:index,c:index)->index{return digits(c,b,a);}
fn increment(a:index)->index{return a+1;}
fn pair(a:index)->(index,index){return (a,a+1);}
operator prefix(75) ⊖=increment;
operator postfix(80) ⊤=pair;
notation ⟪ first,second,third ⟫=reversed(first,second,third);
fn work(initial:index)->(index,index,index,index){
  let mut state=initial;
  let result=CALL;
  let unary=UNARY;
  let paired=PAIRED;
  let projected=paired.1;
  return(result,state,unary,projected);
}
protocol Run roles(P)(initial:index@P)->(result:(index,index,index,index)@P){
  return work(initial);
}
run Demo=Run;
'''
    operands = ','.join('{state=state+1;state}' for _ in range(3))
    source = source.replace('CALL', f'⟪{operands}⟫' if symbolic else f'reversed({operands})')
    source = source.replace('UNARY', '⊖state' if symbolic else 'increment(state)')
    source = source.replace('PAIRED', 'state⊤' if symbolic else 'pair(state)')
    entry = Entry(toolchain, journal, directory, source, flags)
    for initial in (0, 2, 5):
        expected = (initial + 3) * 100 + (initial + 2) * 10 + initial + 1
        assert entry.run(f'initial-{initial}', {'initial': str(initial)}) == {
            'result': [str(n) for n in (expected, initial + 3, initial + 4, initial + 4)],
        }


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_unicode_entry_names_survive_execution(toolchain, journal, directory, flags):
    source = '''module sample;
enum 状態:Copy+Drop+Share { 完了(index), 未完了() }
fn 計算(α:index,β₂:index)->状態{return 状態::完了(α+β₂);}
protocol 実行 roles(参加者)(α:index@参加者,β₂:index@参加者)->(結果:状態@参加者){
  return 計算(α,β₂);
}
run Demo=実行;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run_roles('unicode', {'参加者': {'inputs': {'α': '4', 'β₂': '7'}}}) == {
        '参加者': {'結果': {'case': '完了', 'fields': {'0': '11'}}},
    }


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_notation_keeps_stop_and_boolean_short_circuit_behavior(toolchain, journal, directory, flags):
    source = '''module sample;
fn checked(ok:bool)->bool{require ok;return ok;}
fn first(a:bool,b:bool)->bool{return a;}
operator prefix(75) ⊢=checked;
notation ⟪ left,right ⟫=first(left,right);
fn work(go:bool,eager:bool)->bool{
  return if eager { ⟪false,⊢go⟫ } else { false && ⊢go };
}
protocol Run roles(P)(go:bool@P,eager:bool@P)->(result:bool@P){return work(go,eager);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('skipped', {'go': False, 'eager': False}) == {'result': False}
    assert entry.run('accepted', {'go': True, 'eager': True}) == {'result': False}
    entry.run('refused', {'go': False, 'eager': True}, refuses='entry-run-incomplete')


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_published_vector_notation_project(toolchain, journal, directory, flags):
    from pathlib import Path
    import json

    root = Path(__file__).resolve().parents[3]
    package = directory / 'notation.zkpkg'
    built = journal.json([
        toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--project={root}/examples/projects/mathematical-notation/zkc.toml',
        'example::Run', f'--output={package}', *flags,
    ])

    def scalar(n):
        return str(n)

    def vector(values):
        return [str(n) for n in values]

    inputs = input_files(journal, 'notation', session='mathematical_notation', roles={
        'P': {'inputs': {
            'a': vector([2, 3]), 'b': vector([5, 7]),
            'weights': vector([11, 13]), 'α': scalar(2),
        }},
    })
    output = directory / 'output.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f"--sha256={built['package_sha256']}", *inputs, f'--results={output}'])
    assert report['status'] == 'executed'
    assert json.loads(output.read_text())['roles']['P'] == {
        'symbolic': scalar(231), 'named_result': scalar(231),
        'pointwise': vector([10, 21]),
    }


def test_notation_inspection_is_forwarded_by_the_source_cli(toolchain, journal, directory):
    source = directory / 'notation.zkc'
    source.write_text('''module 数学;
pub fn 合成(α:index,β:index)->index{return α+β;}
pub operator infixl(60) ⊕=合成;
pub fn 公開(α:index,β:index)->index{return α⊕β;}
fn 内部(α:index,β:index)->index{return α⊕β;}
''', encoding='utf-8')
    command = [toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
               f'--module=数学={source}', '--notations']
    public = journal.json(command)['notations']
    assert public['format'] == 'zkc.notations/0'
    assert any(value['owner'] == '数学::公開' for value in public['occurrences'])
    assert not any(value['owner'] == '数学::内部' for value in public['occurrences'])
    full = journal.json([*command, '--notation-private', '--notation-installation'])['notations']
    assert full['include_private'] and full['include_installation']
    assert any(value['owner'] == '数学::内部' for value in full['occurrences'])

    human = journal.attempt([arg for arg in command if arg != '--json'])
    assert human.returncode == 0 and '数学::公開' in human.stdout


def test_notation_example_runs_with_its_supplied_inputs(toolchain, journal, directory):
    import json
    from pathlib import Path
    import shutil

    root = Path(__file__).resolve().parents[3]
    project = directory / 'examples/projects/mathematical-notation'
    shutil.copytree(root / 'examples/projects/mathematical-notation', project,
                    ignore=shutil.ignore_patterns('build'))
    shutil.copytree(root / 'libraries', directory / 'libraries')
    runtime = [toolchain.runtime, '--json']
    compiler = f'--compiler={toolchain.compiler}'
    checked = journal.json([*runtime, 'check', '--notations', compiler], cwd=project)
    assert checked['notations']['format'] == 'zkc.notations/0'
    journal.json([*runtime, 'inputs', 'check', '--operation=run', compiler], cwd=project)
    journal.json([*runtime, 'run', compiler], cwd=project)
    results = json.loads((project / 'build/zkc/example.Run.results.json').read_text())
    assert results['roles']['P'] == {
        'symbolic': '231', 'named_result': '231', 'pointwise': ['10', '21'],
    }
