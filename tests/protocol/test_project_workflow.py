"""User workflows through the installed CLI, including implicit path authority."""
import json
import os
from hashlib import sha256
from pathlib import Path


def command(toolchain, *arguments):
    return [toolchain.runtime, '--json', *arguments, f'--compiler={toolchain.compiler}']


def test_new_prepare_run_defaults_and_human_reports(toolchain, journal, directory):
    project = directory / 'demo'
    created = journal.json(command(toolchain, 'new', project))
    assert created['status'] == 'initialized'
    assert set(created) == {'format', 'status', 'phase', 'project', 'mode', 'compiler',
                            'files', 'preserved', 'publication', 'entries'}
    assert created['publication']['published'] == created['files']
    assert created['publication']['requested'] == created['files']
    assert len(created['files']) == 4
    value = project / 'inputs/example.Main/P.json'
    assert json.loads(value.read_text()) == {'value': None}
    journal.json(command(toolchain, 'run'), cwd=project, refuses='entry-input-unfilled')
    value.write_text('{"value":"7"}\n')
    prepared = journal.json(command(toolchain, 'prepare'), cwd=project)
    assert prepared['files'] == [] and prepared['preserved'] == [str(value)]
    assert prepared['publication']['published'] == []
    assert not any(key.endswith('_published') for key in prepared)
    assert value.read_text() == '{"value":"7"}\n'
    child = project / 'nested'
    child.mkdir()
    first = journal.json(command(toolchain, 'run'), cwd=child)
    second = journal.json(command(toolchain, 'run'), cwd=child)
    assert first['status'] == second['status'] == 'executed'
    assert len(first['session']) == 32 and first['session'] != second['session']
    assert first['inputs'] == {'P': str(value)}
    result = project / 'build/zkc/example.Main.results.json'
    assert first['results'] == str(result)
    assert json.loads(result.read_text())['roles'] == {'P': {'result': '7'}}
    custom = child / 'custom.json'
    custom.write_text('{"value":"11"}')
    overridden = journal.json(command(toolchain, 'run', '--input=P=custom.json',
                                      '--results=custom-result.json', '--session=chosen'), cwd=child)
    assert overridden['session'] == 'chosen'
    assert json.loads((child / 'custom-result.json').read_text())['roles']['P']['result'] == '11'
    assert json.loads(result.read_text())['roles']['P']['result'] == '7'
    for name in ('check', 'prepare', 'run'):
        output = journal.attempt([toolchain.runtime, name, f'--compiler={toolchain.compiler}'], cwd=child)
        assert output.returncode == 0 and not output.stderr
        assert not output.stdout.startswith('{')
    assert 'Results:' in output.stdout and str(result) in output.stdout
    failed = journal.attempt([toolchain.runtime, 'run', '--input=P=absent.json',
                              f'--compiler={toolchain.compiler}'], cwd=child)
    assert failed.returncode == 1 and not failed.stdout
    assert 'entry-input-document' in failed.stderr and 'absent.json' in failed.stderr
    checked = journal.json(command(toolchain, 'inputs', 'check', '--operation=run'), cwd=child)
    assert checked['status'] == 'inputs-checked' and 'execution' not in checked
    assert 'results' not in checked


def test_init_preserves_existing_directory_and_conflicting_sources(toolchain, journal, directory):
    empty = directory / 'empty'
    empty.mkdir()
    journal.json(command(toolchain, 'new', empty), refuses='source-directory-exists')
    refused = journal.attempt([toolchain.runtime, 'new', empty,
                              f'--compiler={toolchain.compiler}'])
    assert refused.returncode == 1 and not refused.stdout
    assert 'zkc init DIRECTORY' in refused.stderr and 'zkc prepare' not in refused.stderr
    assert list(empty.iterdir()) == []
    directory.joinpath('notes.txt').write_text('keep')
    initialized = journal.json(command(toolchain, 'init'), cwd=directory)
    assert initialized['status'] == 'initialized'
    assert directory.joinpath('notes.txt').read_text() == 'keep'
    before = directory.joinpath('main.zkc').read_bytes()
    journal.json(command(toolchain, 'init'), cwd=directory, refuses='source-project-exists')
    journal.json(command(toolchain, 'new', directory), refuses='source-project-exists')
    assert directory.joinpath('main.zkc').read_bytes() == before
    journal.json(command(toolchain, 'init', directory / 'absent'), refuses='source-project-directory')
    conflict = directory / 'conflict'
    conflict.mkdir()
    (conflict / 'main.zkc').write_text('preserve this source')
    journal.json(command(toolchain, 'init', conflict), refuses='entry-output-exists')
    assert not (conflict / 'zkc.toml').exists()


def test_json_positions_and_human_argument_errors(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    compiler = f'--compiler={toolchain.compiler}'
    for args in [('check', '--json', compiler),
                 ('--json', 'check', compiler, '--', 'Main'),
                 ('--json', 'check', '--json', compiler)]:
        assert journal.json([toolchain.runtime, *args], cwd=directory)['status'] == 'checked'
    failed = journal.attempt([toolchain.runtime, 'check', '--invalid'], cwd=directory)
    assert failed.returncode == 1 and not failed.stdout and 'Error [cli-option]' in failed.stderr


def test_non_utf8_working_directory_refuses_without_a_scaffold(toolchain, journal, directory):
    if os.name != 'posix':
        return
    invalid = directory / os.fsdecode(b'non-utf8-\xff')
    invalid.mkdir()
    journal.json(command(toolchain, 'init'), cwd=invalid, refuses='source-project-format')
    assert list(invalid.iterdir()) == []


def test_role_input_filenames_are_portable_and_explicit_paths_override(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    source = directory / 'main.zkc'
    source.write_text('''module example;
      protocol Test roles(P,p)(left:index@P,right:index@p)->(result:index@P){return left;}
      run Case=Test;
    ''')
    journal.json(command(toolchain, 'prepare'), cwd=directory, refuses='source-output-collision')
    journal.json(command(toolchain, 'run'), cwd=directory, refuses='source-output-collision')
    assert not (directory / 'inputs/example.Case').exists()
    value = directory / 'left.json'
    value.write_text('{"left":"7"}')
    right = directory / 'right.json'
    right.write_text('{"right":"3"}')
    assert journal.json(command(toolchain, 'run', f'--input=P={value}', f'--input=p={right}'),
                        cwd=directory)['status'] == 'executed'
    source.write_text('''module example;
      protocol Test roles(CON)(left:index@CON)->(result:index@CON){return left;}
      run Reserved=Test;
    ''')
    journal.json(command(toolchain, 'prepare'), cwd=directory, refuses='source-output-name')
    journal.json(command(toolchain, 'run'), cwd=directory, refuses='source-output-name')
    assert journal.json(command(toolchain, 'run', f'--input=CON={value}'),
                        cwd=directory)['status'] == 'executed'


def test_prepare_all_entries_preserves_data_and_checks_current_shapes(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    source = directory / 'main.zkc'
    source.write_text(source.read_text() + '\nrun Other = Echo;\n')
    prepared = journal.json(command(toolchain, 'prepare'), cwd=directory)
    assert [entry['name'] for entry in prepared['entries']] == ['example::Main', 'example::Other']
    other = directory / 'inputs/example.Other/P.json'
    assert prepared['files'] == [str(other)]
    assert journal.json(command(toolchain, 'prepare', 'Other'), cwd=directory)['files'] == []
    journal.json(command(toolchain, 'run'), cwd=directory, refuses='source-compilation')
    other.write_text('{"value":"9"}')
    assert journal.json(command(toolchain, 'run', 'Other'), cwd=directory)['entry'] == 'example::Other'
    protocol = directory / 'protocol.zkc'
    protocol.write_text(protocol.read_text().replace('value', 'renamed'))
    assert journal.json(command(toolchain, 'check'), cwd=directory)['status'] == 'checked'
    journal.json(command(toolchain, 'prepare'), cwd=directory)
    assert other.read_text() == '{"value":"9"}'
    failure = journal.json(command(toolchain, 'inputs', 'check', 'Other', '--operation=run'),
                           cwd=directory, refuses='entry-input-names')
    assert failure['status'] == 'refused' and 'execution' not in failure
    other.unlink()
    prepared = journal.json(command(toolchain, 'prepare', 'Other'), cwd=directory)
    assert prepared['files'] == [str(other)]
    assert json.loads(other.read_text()) == {'renamed': None}
    # A source-only library does not need an Entry or input documents.
    source.write_text('module example;\nfn identity(x:index)->index{return x;}\n')
    assert journal.json(command(toolchain, 'check'), cwd=directory)['status'] == 'checked'
    empty = journal.json(command(toolchain, 'prepare'), cwd=directory)
    assert empty['entries'] == [] and empty['files'] == []
    assert other.exists(), 'obsolete user inputs are never removed'


def test_unicode_project_paths_and_explicit_role_inputs(toolchain, journal, directory):
    (directory / 'zkc.toml').write_text('format="zkc.project/0"\n[modules]\n"数学"="main.zkc"\n')
    (directory / 'main.zkc').write_text('''module 数学;
      fn 増加(α:index)->index{return α+1;}
      protocol 計算 roles(参加者)(α:index@参加者)->(結果:index@参加者){return 増加(α);}
      run 実行₂=計算;
    ''')
    assert journal.json(command(toolchain, 'check'), cwd=directory)['status'] == 'checked'
    prepared = journal.json(command(toolchain, 'prepare'), cwd=directory)
    value = directory / 'inputs/数学.実行₂/参加者.json'
    assert prepared['files'] == [str(value)]
    assert json.loads(value.read_text()) == {'α': None}
    # Escaped keys and raw source names address the same port without normalization.
    value.write_text('{"\\u03b1":"7"}')
    assert journal.json(command(toolchain, 'prepare'), cwd=directory)['preserved'] == [str(value)]
    for name in ([], ['実行₂'], ['数学::実行₂']):
        report = journal.json(command(toolchain, 'run', *name), cwd=directory)
        result = directory / 'build/zkc/数学.実行₂.results.json'
        assert report['inputs'] == {'参加者': str(value)}
        assert report['results'] == str(result)
        assert json.loads(result.read_text())['roles'] == {'参加者': {'結果': '8'}}
    package = journal.json(command(toolchain, 'compile'), cwd=directory)
    assert package['output'] == str(directory / 'build/zkc/数学.実行₂.zkpkg')
    alternate = directory / 'alternate.json'
    alternate.write_text('{"α":"10"}')
    report = journal.json(command(toolchain, 'run', '--input=参加者=alternate.json'), cwd=directory)
    assert json.loads(Path(report['results']).read_text())['roles']['参加者']['結果'] == '11'
    journal.json(command(toolchain, 'run', '--input=role00000000=alternate.json'),
                 cwd=directory, refuses='entry-input-roles')
    journal.json(command(toolchain, 'run', '--input=参加者=alternate.json',
                         '--input=参加者=alternate.json'), cwd=directory, refuses='entry-input-roles')


def test_unicode_proof_names_and_service_options(toolchain, journal, directory):
    (directory / 'zkc.toml').write_text('format="zkc.project/0"\n[modules]\n"数学"="main.zkc"\n')
    (directory / 'main.zkc').write_text('''module 数学;
      domain F=field("bls12-381.fr");
      protocol 計算 roles(証明者,検証者)(秘密:bool@証明者,乱数:Random<F>@証明者)
          ->(受理:bool@検証者){
        let nonce=乱数.draw();
        let message=send 証明者->検証者(nonce);
        let ok=send 証明者->検証者(秘密);
        return ok && message==message;
      }
      proof 証明₂=計算{prover 証明者;verifier 検証者;public{};accept 受理;construction authored;}
    ''')
    journal.json(command(toolchain, 'prepare'), cwd=directory)
    witness = directory / 'inputs/数学.証明₂/witness.json'
    witness.write_text('{"秘密":true}')
    options = ['--allow-header-only']
    journal.json(command(toolchain, 'prove', *options, '--service=証明者.乱数=0'),
                 cwd=directory, refuses='exhausted:resource-budget')
    produced = journal.json(command(toolchain, 'prove', *options, '--service=証明者.乱数=1'), cwd=directory)
    assert produced['output'] == str(directory / 'build/zkc/数学.証明₂.zkproof')
    witness.unlink()
    assert journal.json(command(toolchain, 'verify', *options), cwd=directory)['status'] == 'accepted'
    journal.json(command(toolchain, 'verify', *options, '--service=role00000001.乱数=1'),
                 cwd=directory, refuses='entry-service-names')


def test_human_stops_use_source_participant_names(toolchain, journal, directory):
    (directory / 'zkc.toml').write_text('format="zkc.project/0"\n[modules]\nexample="main.zkc"\n')
    (directory / 'main.zkc').write_text('''module example;
      protocol Test roles(証明者,検証者)(ok:bool@証明者)->(accepted:bool@検証者){
        let received=send 証明者->検証者(ok);require received;return received;
      }
      run Interactive=Test;
      proof Proof=Test{prover 証明者;verifier 検証者;public{};accept accepted;construction authored;}
    ''')
    journal.json(command(toolchain, 'prepare'), cwd=directory)
    (directory / 'inputs/example.Interactive/証明者.json').write_text('{"ok":false}')
    (directory / 'inputs/example.Proof/witness.json').write_text('{"ok":false}')
    failed = journal.json(command(toolchain, 'run'), cwd=directory, refuses='entry-run-incomplete')
    assert failed['role_names'] == {'role00000000': '証明者', 'role00000001': '検証者'}
    journal.json(command(toolchain, 'prove', '--allow-header-only'), cwd=directory)
    for operation, options in [('run', []), ('verify', ['--allow-header-only'])]:
        human = journal.attempt([arg for arg in command(toolchain, operation, *options) if arg != '--json'],
                                cwd=directory)
        assert human.returncode > 0
        assert 'Stopped 検証者:' in human.stderr
        assert 'Stopped role00000001:' not in human.stderr


def test_default_proof_paths_do_not_discover_other_files(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    (directory / 'main.zkc').write_text('''module example;
    protocol Test roles(P,V)(accept:bool@P, expected:bool@(P,V))->(accepted:bool@V){
        let received=send P->V(accept);return received && expected;
      }
      proof Proof=Test{prover P;verifier V;public{expected};accept accepted;construction authored;}
      run Interactive=Test;
    ''')
    prepared = journal.json(command(toolchain, 'prepare'), cwd=directory)
    selected = next(e for e in prepared['entries'] if e['name'] == 'example::Proof')
    assert selected['requirements']['allow_header_only'] is True
    witness = directory / 'inputs/example.Proof/witness.json'
    witness.write_text('{"accept":true}')
    public = directory / 'inputs/example.Proof/public.json'
    public.write_text('{"expected":true}')
    proof = directory / 'build/zkc/example.Proof.zkproof'
    options = ['--allow-header-only']
    produced = journal.json(command(toolchain, 'prove', *options), cwd=directory)
    assert produced['inputs'] == {'public': str(public), 'witness': str(witness)}
    assert produced['output'] == str(proof)
    original = proof.read_bytes()
    assert produced['proof_sha256'] == sha256(original).hexdigest()
    checked = journal.json(command(toolchain, 'inputs', 'check', '--operation=prove', *options), cwd=directory)
    assert checked['entry'] == 'example::Proof' and 'execution' not in checked
    run_inputs = directory / 'inputs/example.Interactive'
    (run_inputs / 'P.json').write_text('{"accept":true,"expected":true}')
    (run_inputs / 'V.json').write_text('{"expected":true}')
    assert journal.json(command(toolchain, 'run'), cwd=directory)['entry'] == 'example::Interactive'
    # Verification must not open an available witness, including a FIFO.
    witness.unlink()
    if os.name == 'posix':
        os.mkfifo(witness)
    else:
        witness.write_text('not a document')
    verified = journal.json(command(toolchain, 'verify', *options), cwd=directory)
    assert verified['status'] == 'accepted' and verified['proof_sha256'] == produced['proof_sha256']
    witness.unlink()
    # A file elsewhere with the same name is not a fallback.
    (directory / 'witness.json').write_text('{"accept":true}')
    missing = journal.json(command(toolchain, 'prove', *options), cwd=directory,
                           refuses='entry-input-document')
    assert missing['input_file'] == str(witness) and proof.read_bytes() == original
    witness.write_text('{"accept":false}')
    # Rejecting verification uses the newly produced proof rather than a cached verdict.
    journal.json(command(toolchain, 'prove', *options), cwd=directory)
    journal.json(command(toolchain, 'verify', *options), cwd=directory, refuses='artifact-rejected')


def test_implicit_inputs_are_protected_and_invalid_plans_publish_nothing(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    value = directory / 'inputs/example.Main/P.json'
    value.write_text('{"value":"7"}')
    original = value.read_bytes()
    journal.json(command(toolchain, 'run', f'--results={value}'), cwd=directory,
                 refuses='entry-output-path')
    assert value.read_bytes() == original

    if os.name == 'posix':
        alias = directory / 'alias.json'
        os.link(value, alias)
        journal.json(command(toolchain, 'run', f'--results={alias}'), cwd=directory,
                     refuses='entry-output-path')
    (directory / 'main.zkc').write_text('''module example;
      use example_protocol::{Echo};
      run New = Echo;
      run Broken = Missing;
    ''')
    journal.json(command(toolchain, 'prepare'), cwd=directory, refuses='source-compilation')
    assert not (directory / 'inputs/example.New').exists()
    assert value.read_bytes() == original


def test_prepare_refuses_symlinks_and_case_collisions_before_publication(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    source = directory / 'main.zkc'
    value = directory / 'inputs/example.Main/P.json'
    original = value.read_bytes()
    if os.name == 'posix':
        saved = directory / 'saved.json'
        value.rename(saved)
        value.symlink_to(saved)
        journal.json(command(toolchain, 'prepare'), cwd=directory, refuses='entry-output-exists')
        assert saved.read_bytes() == original
        value.unlink()
        saved.rename(value)
    # Different role filenames cannot hide a collision in their parent directory.
    source.write_text('''module example;
      protocol A roles(P)(x:index@P)->(y:index@P){return x;}
      protocol B roles(Q)(x:index@Q)->(y:index@Q){return x;}
      run Clash=A;
      run clash=B;
    ''')
    journal.json(command(toolchain, 'prepare'), cwd=directory, refuses='source-output-collision')
    assert not (directory / 'inputs/example.Clash').exists()
    assert not (directory / 'inputs/example.clash').exists()
    # A fully explicit invocation does not consult the default input namespace.
    source.write_text('module example; use example_protocol::{Echo}; run Main=Echo;')
    value.write_text('{"value":"7"}')
    conflict = directory / 'inputs/example.main'
    conflict.mkdir()
    journal.json(command(toolchain, 'run'), cwd=directory, refuses='source-output-collision')
    explicit = journal.json(command(toolchain, 'run', f'--input=P={value}'), cwd=directory)
    assert explicit['status'] == 'executed'


def test_run_result_policy_and_unserializable_outputs(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    source = directory / 'main.zkc'
    source.write_text('''module example;
      domain F=field("bls12-381.fr");
      type Poly=builtin("polynomial",F);
      fn polynomial()->Poly{
        let one:F=1;let count:index=1;
        return kernel<F>("poly.from_coefficients",kernel<F>("vector.fill",one,count));
      }
      protocol Compute roles(P,V)()->(p:Poly@P,accepted:bool@V){
        let p@P=polynomial();let accepted@V=true;return(p=p,accepted=accepted);
      }
      run Main=Compute;
      proof Proof=Compute{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    refused = journal.json(command(toolchain, 'run'), cwd=directory, refuses='entry-output-codec')
    assert 'execution' not in refused
    executed = journal.json(command(toolchain, 'run', '--no-results'), cwd=directory)
    assert executed['status'] == 'executed' and 'results' not in executed
    journal.json(command(toolchain, 'run', '--no-results', '--results=result.json'), cwd=directory,
                 refuses='cli-option')
    # Explicit-module mode also checks output codecs before executing.
    refused = journal.json([toolchain.runtime, '--json', 'run', f'--module=example={source}',
                            f'--compiler={toolchain.compiler}', '--results=explicit.json'],
                           cwd=directory, refuses='entry-output-codec')
    assert 'execution' not in refused and not (directory / 'explicit.json').exists()
    refused = journal.json(command(toolchain, 'prove', '--allow-header-only', '--results=producer.json'),
                           cwd=directory, refuses='entry-output-codec')
    assert 'execution' not in refused
    journal.json(command(toolchain, 'prove', '--allow-header-only'), cwd=directory)
    # Only this invocation's participant outputs require a file codec.
    verified = journal.json(command(toolchain, 'verify', '--allow-header-only', '--results=verifier.json'),
                            cwd=directory)
    assert verified['status'] == 'accepted'
    assert json.loads((directory / 'verifier.json').read_text())['values'] == {'accepted': True}


def test_explicit_modes_require_proof_paths_before_file_access(toolchain, journal, directory):
    for operation in ('prove', 'verify'):
        for target in (["--package=absent.zkpkg", "--sha256=" + '0' * 64],
                       ["--module=absent=absent.zkc"]):
            report = journal.json([toolchain.runtime, '--json', operation, *target],
                                  cwd=directory, refuses='cli-usage')
            assert report['phase'] == 'arguments'
    assert not (directory / 'build').exists()


def test_generated_commands_use_defaults_and_empty_roles_need_no_file(toolchain, journal, directory):
    journal.json(command(toolchain, 'init'), cwd=directory)
    (directory / 'main.zkc').write_text('''module example;
      protocol Exchange roles(P,V)(accept:bool@P)->(accepted:bool@V){
        let actual=send P->V(accept);return actual;
      }
      run Interactive=Exchange;
      proof Proof=Exchange{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    for name in ('Interactive', 'Proof'):
        templates = journal.json(command(toolchain, 'inputs', 'init', name), cwd=directory)
        group = 'P' if name == 'Interactive' else 'witness'
        (directory / f'inputs/example.{name}/{group}.json').write_text('{"accept":true}')
        for argv in templates['commands']:
            assert not any(arg.startswith('--session=') for arg in argv)
            assert not any(arg.startswith(('--proof=', '--output=')) for arg in argv)
            flags = ['--allow-header-only'] if name == 'Proof' else []
            result = journal.json([toolchain.runtime, '--json', *argv[1:], *flags], cwd=directory)
            assert result['status'] in ('executed', 'produced', 'accepted')
        if name == 'Interactive':
            assert not (directory / 'inputs/example.Interactive/V.json').exists()
            assert list(result['inputs']) == ['P']
