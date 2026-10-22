"""Separate CLI jobs adapt authenticated source packages to the shared Host."""

from entry import compile_named_entry, joint_execution

from input_files import input_files, invocation_file
import hashlib
import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = ROOT / 'compiler/test/fixtures/language'


def compile_entry(toolchain, journal, directory, entry, source=None):
    return compile_named_entry(toolchain, journal, directory, entry,
                               source or FIXTURES / 'attempts.zkc')


def write(path, value):
    path.write_text(json.dumps(value))
    return path


@pytest.mark.parametrize('entry,suite', [('Derived', None), ('Derived', 'spongefish0.8.0.keccak.bls12-381.fr64be/0'),
                                         ('Derived', 'hash-chain.keccak256.bls12-381.fr64be/0'), ('Plain', None)])
def test_independent_named_proof_calls(toolchain, journal, directory, entry, suite):
    source = directory / 'source.zkc'
    text = (FIXTURES / 'attempts.zkc').read_text()
    source.write_text(text.replace('merlin3.bls12-381.fr64be/0', suite) if suite else text)
    package, pin = compile_entry(toolchain, journal, directory, entry, source)
    witness = write(directory / 'witness.json', {'done': True})
    proof = directory / 'proof.bin'
    results = directory / 'results.json'
    target = [f'--package={package}', f'--sha256={pin}']
    flags = ['--allow-authored'] if entry == 'Plain' else []
    proving = [toolchain.runtime, '--json', 'prove', *target, f'--witness={witness}', f'--output={proof}', *flags]
    def verify(path=proof, *extra):
        return [toolchain.runtime, '--json', 'verify', *target, f'--proof={path}', *flags, *extra]
    if entry == 'Plain':
        journal.run(proving[:-1], refuses='entry-proof-binding-policy')
    produced = journal.json([*proving, f'--results={results}'])
    assert produced['status'] == 'produced' and produced['proof_published']
    assert produced['execution']['attempts'][0]['decision'] == 'complete'
    values = json.loads(results.read_text())['values']
    assert values['result']['ready'] is True
    assert json.dumps(values['padding']) not in json.dumps(produced)
    accepted = journal.json(verify())
    assert accepted['status'] == 'accepted'
    assert accepted['binding_scope'] == ('header' if flags else 'transcript')
    sentinel = proof.read_bytes()
    bad = directory / 'bad-proof.bin'
    changed = bytearray(sentinel)
    changed[0] ^= 1
    bad.write_bytes(changed)
    unchanged_results = results.read_bytes()
    rejection = journal.json(verify(bad, f'--results={results}'), refuses='proof-header')
    assert rejection['status'] == 'refused' and 'execution' in rejection
    assert results.read_bytes() == unchanged_results
    bad.write_bytes(sentinel + b'\x00')
    journal.run(verify(bad, f'--results={results}'), refuses='proof-trailing')
    if entry == 'Derived':
        changed = bytearray(sentinel)
        changed[-32] ^= 1
        bad.write_bytes(changed)
        rejected = journal.json(verify(bad, f'--results={results}'), refuses='artifact-rejected')
        assert rejected['status'] == 'refused' and 'execution' in rejected
    assert results.read_bytes() == unchanged_results
    rejected_context = journal.json(verify(proof, '--context=01', f'--results={results}'), refuses='proof-header')
    assert rejected_context['status'] == 'refused' and results.read_bytes() == unchanged_results
    journal.run([*proving, '--attempts=0'], refuses='native-attempt-limits')
    assert proof.read_bytes() == sentinel
    journal.run([*proving, f'--results={proof}'], refuses='entry-output-path')
    alias = directory / 'directory-alias'
    alias.symlink_to(directory, target_is_directory=True)
    for protected in [alias / proof.name, package, witness]:
        journal.run([*proving, f'--results={protected}'], refuses='entry-output-path')
    write(witness, {'done': False})
    refused = journal.json(proving, refuses='native-attempt-limit')
    assert len(refused['execution']['attempts']) == 1
    refused = journal.json([*proving, '--attempts=3'], refuses='native-attempt-limit')
    assert len(refused['execution']['attempts']) == 3
    assert proof.read_bytes() == sentinel
    write(witness, {'done': True})
    journal.run([*proving, '--service=P.coins=0'], refuses='exhausted:resource-budget')
    assert proof.read_bytes() == sentinel
    witness.write_text('{"done":true,"done":false}')
    journal.run(proving, refuses='entry-request-format')
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={"00" * 32}',
                 f'--witness={witness}', f'--output={proof}', *flags], refuses='entry-package-identity')
    write(witness, {'done': True})
    if entry == 'Derived':
        journal.run([*proving, '--transcript-budget=0'], refuses='exhausted:resource-budget')
    failed_publication = journal.json([*proving, f'--results={directory / "missing" / "results"}'], refuses='entry-output-path')
    assert failed_publication['phase'] == 'invocation' and 'execution' not in failed_publication
    assert proof.read_bytes() == sentinel


def test_named_run_defaults_and_private_result_files(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    inputs = write(directory / 'P.json', {'inputs': {'P': {'done': True}, 'V': {}}})
    outputs = directory / 'outputs.json'
    command = [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
               f'--input={inputs}', f'--results={outputs}']
    report = journal.json(command)
    assert report['status'] == 'executed'
    values = json.loads(outputs.read_text())['value']
    assert values['V']['accepted'] is True
    assert values['P']['result']['ready'] is True
    assert json.dumps(values['P']['padding']) not in json.dumps(report)
    assert all('outputs' not in role for role in joint_execution(report)['roles'])
    sentinel = outputs.read_bytes()
    binding = invocation_file(journal, 'limited.invocations.json', package,
                              role_services={'V': {'challenges': 0}})
    journal.run([*command, binding], refuses='entry-host-run-failed')
    assert outputs.read_bytes() == sentinel
    binding = invocation_file(journal, 'unknown.invocations.json', package,
                              role_services={'V': {'unknown': 1}})
    journal.run([*command, binding], refuses='entry-service-names')
    write(inputs, {'inputs': {'P': {'done': True, 'extra': True}, 'V': {}}})
    refused = journal.json(command, refuses='entry-input-fields')
    assert refused['input_path'] == 'arguments.inputs.P.extra'
    assert outputs.read_bytes() == sentinel and 'execution' not in refused
    journal.run([*command, '--results=duplicate'], refuses='cli-option')


@pytest.mark.parametrize('done', [False, True])
def test_conditional_completion_preserves_logical_result_order(toolchain, journal, directory, done):
    source = directory / 'completion.zkc'
    source.write_text("""module sample;
protocol Complete<T:Type> roles(P)(done:bool@P,value:T@P)->(first:bool@P,second:T@P) completes {
  let(first,second)=finish_if @P(done)(second=value,first=true);
  return(first=false,second=second);
}
entry fn Demo(inputs: Complete<bool>::Inputs) { return Complete<bool>::run(inputs); }
""")
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    inputs = write(directory / 'P.json', {'inputs': {'P': {'done': done, 'value': False}}})
    results = directory / 'results.json'
    report = journal.json([toolchain.runtime, '--json', 'run',
                           f'--package={package}', f'--sha256={pin}',
                           f'--input={inputs}',
                           f'--results={results}'])
    assert report['status'] == 'executed'
    assert json.loads(results.read_text())['value']['P'] == {'first': done, 'second': False}


def test_aggregate_file_roundtrip_and_schema_refusals(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', FIXTURES / 'host_values.zkc')
    payload = {'choice': {'case': 'Data', 'fields': {
        '0': {'case': 'Pair', 'fields': {'0': '7', '1': '11'}},
        '1': [False, None], '2': ['13', '17']}}, 'marker': True}
    inputs = write(directory / 'P.json', {'inputs': {'P': {'payload': payload, 'empty': None}, 'V': {}}})
    results = directory / 'results.json'
    command = [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
               f'--input={inputs}', f'--results={results}']
    journal.run(command)
    outputs = json.loads(results.read_text())['value']
    assert outputs['V'] == {'received': payload, 'empty': None}
    assert outputs['P']['sent'] == payload
    mutations = [
        ({'choice': {'case': 'Absent', 'fields': {}}, 'marker': True}, 'entry-input-alternative'),
        ({'choice': {'case': 'Empty', 'fields': {'extra': True}}, 'marker': True}, 'entry-input-fields'),
        ({'choice': {'case': 'Empty', 'fields': {}}, 'marker': 1}, 'entry-input-shape'),
        ({'choice': {'case': 'Empty', 'fields': {}}}, 'entry-input-fields'),
    ]
    for changed, code in mutations:
        write(inputs, {'inputs': {'P': {'payload': changed, 'empty': None}, 'V': {}}})
        journal.run(command, refuses=code)


def test_input_numbers_keep_their_json_shape(toolchain, journal, directory):
    source = directory / 'indices.zkc'
    source.write_text("module sample; protocol Index roles(P)(n:index@P)->(n:index@P){return(n=n);} entry fn Demo(inputs: Index::Inputs) { return Index::run(inputs); }")
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    inputs = write(directory / 'P.json', {'inputs': {'P': {'n': '7'}}})
    command = [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
               f'--input={inputs}']
    journal.run(command)
    for value in [7, {'$serde_json::private::Number': '7'}, '07', '+7', '18446744073709551616']:
        write(inputs, {'inputs': {'P': {'n': value}}})
        journal.run(command, refuses='entry-input-shape' if not isinstance(value, str) else 'entry-input-decimal')
    for number in [-1, 1.0, 2 ** 64]:
        write(inputs, {'inputs': {'P': {'n': number}}})
        journal.run(command, refuses='entry-request-format')


@pytest.mark.skipif(not hasattr(os, 'mkfifo'), reason='POSIX file descriptors')
def test_file_jobs_refuse_unconnected_streams(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    fifo = directory / 'fifo'
    os.mkfifo(fifo)
    # There is no writer. Refusal precedes any protocol resource issuance.
    report = json.loads(journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', f'--input={fifo}'],
                                   refuses='entry-input-document', timeout=10))
    assert report['phase'] == 'inputs' and 'execution' not in report
    journal.run([toolchain.runtime, '--json', 'run', f'--package={fifo}', f'--sha256={pin}', f'--input={fifo}'], refuses='artifact-io', timeout=10)


def test_source_entry_refuses_outputs_without_host_export(toolchain, journal, directory):
    source = directory / 'restricted.zkc'
    source.write_text('module sample; #[affine] struct Restricted{pub b:bool}'
                      'fn make()->Restricted{return Restricted{b:true};}'
                      'protocol Run roles(P)()->(r:Restricted@P){'
                      'let r @P =make();return(r=r);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }')
    package = directory / 'restricted.zkpkg'
    refused = journal.json([toolchain.runtime, '--json', 'compile',
                           f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                           'sample::Demo', f'--output={package}'], refuses='source-compilation')
    assert 'source.host-data' in refused['diagnostics']
    assert 'Copy and Drop' in refused['diagnostics']
    assert not package.exists(), 'an affine source return escaped into a Host package'


def test_compilation_preserves_the_selected_executable(toolchain, journal, directory):
    compiler = directory / 'compiler'
    # Refusal must precede spawning, so this intentionally failing child is a
    # discriminator even without a successful package on stdout.
    compiler.write_text('#!/bin/sh\nexit 7\n')
    compiler.chmod(0o755)
    alias = directory / 'compiler-link'
    alias.symlink_to(compiler)
    original = compiler.read_bytes()
    for selected, output in [(compiler, compiler), (alias, compiler), (alias, alias),
                             (compiler, alias)]:
        journal.run([toolchain.runtime, '--json', 'compile', 'sample::Derived',
                     f'--module=sample={FIXTURES / "attempts.zkc"}', f'--compiler={selected}',
                     f'--output={output}'], refuses='entry-output-path')
        assert compiler.read_bytes() == original and alias.is_symlink()


def test_compiler_failures_are_bounded_and_do_not_publish(toolchain, journal, directory):
    compiler = directory / 'compiler'
    compiler.write_text(f'#!{sys.executable}\nimport sys\nsys.stderr.write("X" * 70000)\nsys.exit(1)\n')
    compiler.chmod(0o755)
    output = directory / 'existing.zkpkg'
    output.write_bytes(b'unchanged')
    args = [toolchain.runtime, '--json', 'compile', 'sample::Derived',
            f'--module=sample={FIXTURES / "attempts.zkc"}', f'--output={output}']
    report = json.loads(journal.run([*args, f'--compiler={compiler}'], refuses='source-compilation'))
    assert report['diagnostics_truncated'] and len(report['diagnostics']) == 65536
    assert output.read_bytes() == b'unchanged'
    journal.run([*args, f'--compiler={directory / "missing"}'], refuses='source-compiler-missing')


def test_proof_file_public_inputs_are_authoritative(toolchain, journal, directory):
    source = directory / 'public.zkc'
    source.write_text((FIXTURES / 'attempts.zkc').read_text()
                      .replace('Round roles(P,V)(done:bool@P,', 'Round roles(P,V)(done:bool@P,tag:bool@(P,V),')
                      .replace('public{};accept accepted;complete result.ready;', 'public{tag};accept accepted;complete result.ready;', 1))
    package, pin = compile_entry(toolchain, journal, directory, 'Derived', source)
    producer = input_files(journal, (directory / 'producer.json').name, public={'tag': True}, witness={'done': True})
    verifier = input_files(journal, (directory / 'verifier.json').name, public={'tag': True})
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    verifying = [toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}']
    journal.run(verifying)
    witness = write(directory / 'duplicate-public.json', {'done': True, 'tag': True})
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}',
                 f'--public={directory / "producer.public.json"}', f'--witness={witness}',
                 f'--output={proof}'], refuses='entry-input-names')
    journal.run([*verifying, f'--witness={witness}'], refuses='cli-option')
    write(directory / 'verifier.public.json', {})
    journal.run(verifying, refuses='entry-input-names')
    write(directory / 'verifier.public.json', {'tag': False})
    journal.run(verifying, refuses='proof-header')
    original = source.read_bytes()
    journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                 f'--module=sample={source}', 'sample::Derived', f'--output={source}'],
                refuses='entry-output-path')
    assert source.read_bytes() == original


def test_compiler_lookup_and_positional_arguments(toolchain, journal, directory):
    source = directory / 'source.zkc'
    source.write_text('module sample; protocol Run roles(P)(b:bool@P)->(b:bool@P){return(b=b);} entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }')
    args = [toolchain.runtime, '--json', 'compile', '--module=sample=source.zkc', 'sample::Demo', '--output=demo.zkpkg']
    env = dict(os.environ, PATH=str(toolchain.compiler.parent))
    result = journal.attempt(args, cwd=directory, env=env)
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'compiled'
    # A bare compiler name refers to trusted PATH, not this same-named output.
    local_output = directory / 'zkc-compile'
    same_name = journal.attempt([*args[:-1], '--output=zkc-compile'], cwd=directory, env=env)
    assert same_name.returncode == 0, same_name.stdout + same_name.stderr
    assert json.loads(local_output.read_text())['format'] == 'zkc.entry/0'
    local_output.unlink()
    (directory / 'zkc-compile').symlink_to(toolchain.compiler)
    for path in (None, '', '.'):
        env = dict(os.environ)
        if path is None:
            env.pop('PATH', None)
        else:
            env['PATH'] = path
        result = journal.attempt(args, cwd=directory, env=env)
        assert result.returncode == 1 and json.loads(result.stdout)['code'] == 'source-compiler-missing'
    package = directory / 'demo.zkpkg'
    for command in ('prove', 'bindings'):
        args = [toolchain.runtime, '--json', command, package, report['package_sha256']]
        if command == 'prove':
            args.append('request.json')
        journal.run(args, refuses='cli-usage')
        journal.run([*args, '--results=output.json'],
                    refuses='cli-usage' if command == 'prove' else 'cli-option')


def test_results_encoding_failure_preserves_previous_files(toolchain, journal, directory):
    source = directory / 'source.zkc'
    source.write_text('''module sample;
domain Fr=field("bls12-381.fr");
type Vector<F:Field>=builtin("vector",F);
fn filled(x:Fr)->Vector<Fr>{let n:index=3;return kernel<Fr>("vector.fill",x,n);}
protocol Run roles(P,V)(done:bool@P)->(large:Vector<Fr>@P,accepted:bool@V){
  let large @P =filled(1);
  let actual=send P->V(done);
  return(large=large,accepted=actual);
}
proof Demo=Run{prover P;verifier V;public{};accept accepted;construction authored;}
''')
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    producer = input_files(journal, (directory / 'producer.json').name, public={}, witness={'done': True})
    verifier = input_files(journal, (directory / 'verifier.json').name, public={})
    proof = directory / 'proof.bin'
    results = directory / 'results.json'
    results.write_bytes(b'unchanged')
    baseline = json.loads(journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}', '--allow-authored']))
    accepted_proof = proof.read_bytes()
    proof.write_bytes(b'existing proof')
    limits = baseline['capacity']
    limits[3] = '64'
    capacity = write(directory / 'capacity.json', limits)
    report = json.loads(journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}', '--allow-authored', f'--capacity={capacity}', f'--results={results}'], refuses='entry-output-encoding'))
    assert report['phase'] == 'results' and not report.get('proof_published', False)
    assert proof.read_bytes() == b'existing proof'
    assert results.read_bytes() == b'unchanged'
    proof.write_bytes(accepted_proof)
    journal.run([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}', '--allow-authored', f'--results={results}'])
    assert json.loads(results.read_text())['values']['accepted'] is True


def test_interface_publication_and_host_share_resource_boundaries(toolchain, journal, directory):
    source = directory / 'source.zkc'
    def program(count):
        ports = ','.join(f'a{i}:[bool;128]@P' for i in range(count))
        return f'module sample;protocol Run roles(P)({ports})->(){{return();}}entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}'
    source.write_text(program(7))
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={package}', f'--sha256={pin}', f'--output={directory / 'bindings.rs'}'])
    request = input_files(journal, (directory / 'inputs.json').name, session='bounded_interface', package=package, arguments={'inputs': {'P': {f'a{i}': [False] * 128 for i in range(7)}}})
    executed = json.loads(journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', *request]))
    assert executed['status'] == 'executed'
    source.write_text(program(9))
    refused = directory / 'oversized.zkpkg'
    result = json.loads(journal.run([
        toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--module=sample={source}', 'sample::Demo', f'--output={refused}',
    ], refuses='source-compilation'))
    assert 'source.limit' in result['diagnostics']
    assert not refused.exists()


@pytest.mark.parametrize('entry,kind', [('Derived', 'proof'), ('Plain', 'proof'), ('Run', 'function')])
def test_inspect_authenticates_without_execution(toolchain, journal, directory, entry, kind):
    package, pin = compile_entry(toolchain, journal, directory, entry)
    sentinel = package.read_bytes()
    report = journal.json([toolchain.runtime, '--json', 'inspect', f'--package={package}', f'--sha256={pin}'])
    assert report['format'] == 'zkc.entry-inspection/0' and report['status'] == 'inspected'
    assert report['phase'] == 'complete' and report['package_sha256'] == pin
    interface = report['interface']
    assert interface['entry'] == f'sample::{entry}' and interface['kind'] == kind
    assert len(interface['toolchain']) == 64
    if kind == 'proof':
        assert interface['setups'] == []
        roles = {role['name']: role for role in interface['roles']}
        assert set(roles) == {'P', 'V'}
        assert any(port['name'] == 'done' and port['type'] == 'bool' for port in roles['P']['inputs'])
        proof = interface['proof']
        assert proof['prover'] == 'P' and proof['verifier'] == 'V'
        assert proof['acceptance'] == {'port': 'accepted', 'path': [], 'role': 'V'}
        assert proof['completion'] == {'port': 'result', 'path': [0], 'role': 'P'}
        assert proof['public'] == []
        assert (proof['transcript_suite'] is not None) == (entry == 'Derived')
    else:
        parameters = interface['signature']['parameters']
        assert [parameter['name'] for parameter in parameters] == ['inputs']
        roles = {field['name']: field['schema'] for field in parameters[0]['schema']['fields']}
        assert set(roles) == {'P', 'V'}
        assert any(field['name'] == 'done' and field['schema']['kind'] == 'boolean'
                   for field in roles['P']['fields'])
    assert 'execution' not in report and 'capacity' not in report
    refused = journal.json([toolchain.runtime, '--json', 'inspect', f'--package={package}', f'--sha256={'0' * 64}'],
                           refuses='entry-package-identity')
    assert 'interface' not in refused
    assert package.read_bytes() == sentinel
    missing = directory / 'missing.zkpkg'
    refused = journal.json([toolchain.runtime, '--json', 'inspect', f'--package={missing}', f'--sha256={pin}', '--results=unused'],
                           refuses='cli-option')
    assert refused['phase'] == 'arguments' and refused['message']
    assert not (directory / 'unused').exists()


def test_run_work_limits_apply_and_configuration_files_are_protected(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    inputs = input_files(journal, (directory / 'inputs.json').name, session='limited', package=package, arguments={'inputs': {'P': {'done': True}, 'V': {}}})
    limits = write(directory / 'limits.json', ['zkc.bundle-limits/0', '0', '1024', '1024', '100000'])
    sentinel = limits.read_bytes()
    command = [toolchain.runtime, '--json', 'run', f'--limits={limits}', f'--package={package}', f'--sha256={pin}', *inputs]
    refused = journal.json(command, refuses='entry-host-dispatch-limit')
    assert refused['phase'] == 'execution'
    execution = refused['execution']
    assert not execution['completed'] and execution['usage']['dispatches'] == 0
    assert execution['failure']['code'] == 'entry-host-dispatch-limit'
    assert not any(call['completed'] for call in execution['calls'])
    journal.run([*command, f'--results={limits}'], refuses='entry-output-path')
    assert limits.read_bytes() == sentinel


@pytest.mark.parametrize('local', [False, True])
def test_require_proof_outcome_and_unpublished_prefix(toolchain, journal, directory, local):
    def condition(name):
        return f'checked({name})' if local else name
    source = directory / 'require.zkc'
    source.write_text(f'''module sample;
fn checked(go:bool)->bool{{require go;return go;}}
protocol Check roles(P,V)(produce:bool@P,accept:bool@P)->(accepted:bool@V){{
  require {condition('produce')};
  let actual=send P->V(accept);
  require {condition('actual')};
  let final=send P->V(true);
  return true;
}}
proof Proof=Check{{prover P;verifier V;public{{}};accept accepted;construction authored;}}
''')
    package, pin = compile_entry(toolchain, journal, directory, 'Proof', source)
    producer = input_files(journal, (directory / 'producer.json').name, public={}, witness={'produce': True, 'accept': True})
    verifier = input_files(journal, (directory / 'verifier.json').name, public={}, witness={})
    proof = directory / 'proof.bin'
    proving = [toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}', '--allow-authored']
    verifying = [toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}', '--allow-authored']
    assert journal.json(proving)['status'] == 'produced'
    assert journal.json(verifying)['status'] == 'accepted'
    input_files(journal, 'producer', public={}, witness={'produce': True, 'accept': False})
    assert journal.json(proving)['status'] == 'produced'
    report = journal.json(verifying, refuses='artifact-stopped')
    assert report['execution']['stop']['kind'] == 'Explicit("reject")'
    assert report['execution']['stop']['role'] == 'role00000001'
    input_files(journal, 'producer', public={}, witness={'produce': False, 'accept': True})
    proof.unlink()
    report = journal.json(proving, refuses='artifact-stopped')
    assert not proof.exists(), 'producer rejection published a partial proof'
    assert 'Explicit("reject")' in str(report)


def numerical_project(directory):
    source = directory / 'numerical.zkc'
    source.write_text('''module application;
fn increment(value:index)->index{return value+1;}
entry fn Next(value:index){return increment(value);}
entry fn Twice(value:index){let next=Next(value);return Next(next);}
entry fn Checked(value:index,valid:bool){require valid;return increment(value);}
''')
    manifest = directory / 'zkc.toml'
    manifest.write_text('format="zkc.project/0"\n[modules]\napplication="numerical.zkc"\n')
    return manifest


@pytest.mark.parametrize('selector,value', [('Echo', False), ('Echo', True),
                                          ('Echo<bool>', False), ('Echo<index>', '17')])
def test_automatic_protocol_and_closed_generic_selectors(toolchain, journal, directory, selector, value):
    generic = '<T:Type>' if '<' in selector else ''
    kind = 'T' if generic else 'bool'
    source = directory / 'echo.zkc'
    source.write_text(f'''module sample;
protocol Echo{generic} roles(P,V)(value:{kind}@P)->(received:{kind}@V){{
  let received=send P->V(value);return received;
}}
''')
    package, pin = compile_entry(toolchain, journal, directory, selector, source)
    target = [f'--package={package}', f'--sha256={pin}']
    view = journal.json([toolchain.runtime, '--json', 'inspect', *target])['interface']
    assert view['entry'] == f'sample::{selector}' and view['kind'] == 'function'
    inputs = write(directory / 'arguments.json', {'inputs': {'P': {'value': value}, 'V': {}}})
    output = directory / 'result.json'
    report = journal.json([toolchain.runtime, '--json', 'run', *target,
                           f'--input={inputs}', f'--results={output}'])
    assert report['status'] == 'executed'
    assert json.loads(output.read_text())['value'] == {'P': {}, 'V': {'received': value}}


def test_numerical_source_value_and_execution_failure(toolchain, journal, directory):
    manifest = numerical_project(directory)
    target = [f'--project={manifest}', f'--compiler={toolchain.compiler}']
    view = journal.json([toolchain.runtime, '--json', 'inspect', 'Twice', *target])['interface']
    assert view['kind'] == 'function'
    assert [p['name'] for p in view['signature']['parameters']] == ['value']
    inputs = write(directory / 'arguments.json', {'value': '7'})
    output = directory / 'result.json'
    report = journal.json([toolchain.runtime, '--json', 'run', 'Twice', *target,
                           f'--input={inputs}', f'--results={output}'])
    assert json.loads(output.read_text())['value'] == '9'
    assert report['execution']['usage']['instructions'] > 0
    sentinel = output.read_bytes()
    write(inputs, {'value': '7', 'valid': False})
    failed = journal.json([toolchain.runtime, '--json', 'run', 'Checked', *target,
                           f'--input={inputs}', f'--results={output}'], refuses='entry-host-require')
    assert failed['phase'] == 'execution' and failed['execution']['failure']
    assert not failed['execution']['completed'] and output.read_bytes() == sentinel


def test_proof_entry_calls_keep_independent_statements_and_withhold_stopped_results(toolchain, journal, directory):
    source = directory / 'entry-proofs.zkc'
    source.write_text('''module sample;
protocol Equality roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(accepted:bool@V){
  let received=send P->V(candidate);
  let accepted@V=received==expected;
  return(accepted=accepted);
}
proof Core=Equality{prover P;verifier V;public{expected};accept accepted;construction authored;}
entry fn Produce(public:Core::Public,witness:Core::Witness){
  let produced=Core::prove(public,witness);return produced.proof;
}
entry fn Validate(public:Core::Public,candidate:Core::Proof){return Core::verify(public,candidate);}
entry fn Withhold(public:Core::Public,witness:Core::Witness,complete:bool){
  let produced=Core::prove(public,witness);require complete;return produced.proof;
}
''')
    targets = {}
    for entry in ('Produce', 'Validate', 'Withhold', 'Core'):
        package, pin = compile_entry(toolchain, journal, directory, entry, source)
        targets[entry] = [f'--package={package}', f'--sha256={pin}', '--allow-authored']

    def call(entry, arguments, *, refuses=None):
        inputs = write(directory / f'{entry}.json', arguments)
        output = directory / f'{entry}.result.json'
        # Existing output must survive a later refusal, too.
        sentinel = output.read_bytes() if output.exists() else None
        report = journal.json([toolchain.runtime, '--json', 'run', *targets[entry],
                               f'--input={inputs}', f'--results={output}'], refuses=refuses)
        if refuses:
            assert (output.read_bytes() if output.exists() else None) == sentinel
            assert not report['execution']['completed']
            return report
        assert report['status'] == 'executed' and report['execution']['completed']
        return json.loads(output.read_text())['value']

    positive = call('Produce', {'public': {'expected': True}, 'witness': {'candidate': True}})
    accepted = call('Validate', {'public': {'expected': True}, 'candidate': positive})
    assert accepted == {'case': 'Accepted', 'fields': {'outputs': {'accepted': True}}}
    negative = call('Produce', {'public': {'expected': True}, 'witness': {'candidate': False}})
    rejected = call('Validate', {'public': {'expected': True}, 'candidate': negative})
    assert rejected == {'case': 'Rejected', 'fields': {}}
    call('Validate', {'public': {'expected': False}, 'candidate': positive}, refuses='proof-header')
    withheld = call('Withhold', {'public': {'expected': True}, 'witness': {'candidate': True},
                                 'complete': False}, refuses='entry-host-require')
    assert any(c['operation'] == 'prove' and c['completed'] for c in withheld['execution']['calls'])
    assert not (directory / 'Withhold.result.json').exists()
    # Independent file APIs bind a nonempty statement to the same proof deployment.
    public = write(directory / 'public.json', {'expected': True})
    witness = write(directory / 'witness.json', {'candidate': True})
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *targets['Core'],
                             f'--public={public}', f'--witness={witness}', f'--output={proof}'])
    assert produced['status'] == 'produced' and produced['proof_published']
    independent = write(directory / 'verifier-public.json', {'expected': True})
    checked = journal.json([toolchain.runtime, '--json', 'verify', *targets['Core'],
                            f'--public={independent}', f'--proof={proof}'])
    assert checked['status'] == 'accepted'


def test_input_documents_confine_references_and_refuse_symlink_and_parent_escape(toolchain, journal, directory):
    manifest = numerical_project(directory)
    target = [f'--project={manifest}', f'--compiler={toolchain.compiler}']
    wire = b'ZKCV\x00\x1f' + (7).to_bytes(8, 'little')
    data = directory / 'data'
    data.mkdir()
    leaf = data / 'index.zkcv'
    leaf.write_bytes(wire)
    pin = hashlib.sha256(wire).hexdigest()
    arguments = write(data / 'arguments.json', {'value': {'file': leaf.name, 'sha256': pin}})
    output = directory / 'result.json'
    command = [toolchain.runtime, '--json', 'run', 'Twice', *target, f'--results={output}']
    journal.json([*command, f'--input={arguments}'])
    assert json.loads(output.read_text())['value'] == '9'
    sentinel = output.read_bytes()
    alias = data / 'alias.json'
    alias.symlink_to(arguments.name)
    journal.json([*command, f'--input={alias}'], refuses='entry-input-document')
    # A real outside value and a symlink to it must both remain inaccessible.
    outside = directory / 'outside.zkcv'
    outside.write_bytes(wire)
    (data / 'alias.zkcv').symlink_to(outside)
    for reference in ('../outside.zkcv', 'alias.zkcv'):
        write(arguments, {'value': {'file': reference, 'sha256': pin}})
        journal.json([*command, f'--input={arguments}'], refuses='entry-input-reference')
        assert output.read_bytes() == sentinel
