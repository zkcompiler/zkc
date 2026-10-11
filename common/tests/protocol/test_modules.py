"""Unified module scopes through project discovery, compilation and the Host."""

import json

import pytest

from input_files import input_files


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_inline_and_external_generic_modules(toolchain, journal, directory, flags):
    child = '''
type State:Copy+Drop=[F;N];
pub fn first(xs:[F;N])->F where 1<=N {
 let state=State(xs);
 let values=unpack(state);
 return increment(values[0]);
}
'''
    results = []
    for external in (False, True):
        project = directory / ('external' if external else 'inline')
        project.mkdir()
        (project / 'library.zkc').write_text('''module library<F:Field>;
math fn increment(x:F)->F{return x+1;}
pub module Box''' + (';' if external else '<N:nat>{' + child + '}'))
        (project / 'main.zkc').write_text('''module main;
use library::Box as Reader;
domain F=field("koala-bear");
protocol Compute roles(P)(xs:[F;2]@P)->(value:F@P){return Reader::first<F,2>(xs);}
run Demo=Compute;
''')
        manifest = '''format="zkc.project/0"
[modules]
main="main.zkc"
library="library.zkc"
'''
        if external:
            (project / 'child.zkc').write_text('module library::Box<N:nat>;' + child)
            manifest += '"library::Box"="child.zkc"\n'
        (project / 'zkc.toml').write_text(manifest)
        command = [toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                   '--declarations']
        report = journal.json(command, cwd=project)
        modules = {d['name']: d for d in report['declarations'] if d['kind'] == 'module'}
        assert modules['library::Box']['owner']['name'] == 'library'
        assert [p['inherited'] for p in modules['library::Box']['parameters']] == [True, False]
        package = project / 'module.zkpkg'
        built = journal.json([toolchain.runtime, '--json', 'compile',
                              f'--compiler={toolchain.compiler}', f'--output={package}',
                              *flags], cwd=project)
        inputs = input_files(journal, f'{external}.inputs.json', session='module_test',
                             roles={'P': {'inputs': {'xs': ['3', '7']}}})
        output = project / 'results.json'
        executed = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                                 f'--sha256={built["package_sha256"]}', *inputs,
                                 f'--results={output}'])
        assert executed['status'] == 'executed'
        results.append(json.loads(output.read_text())['roles']['P'])
    assert results == [{'value': '4'}, {'value': '4'}]
