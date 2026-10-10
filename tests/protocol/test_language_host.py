"""Separate CLI jobs adapt authenticated source packages to the shared Host."""

from input_files import input_files
import hashlib
import json
import os
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / 'compiler/test/fixtures/language'


def compile_entry(toolchain, journal, directory, entry, source=None):
    package = directory / f'{entry}.zkpkg'
    args = [toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
            f'--module=sample={source or FIXTURES / "attempts.zkc"}',
            f'sample::{entry}', f'--output={package}']
    report = json.loads(journal.run(args))
    assert report['status'] == 'compiled'
    assert Path(report['compiler']).is_absolute() and len(report['toolchain']) == 64
    assert report['package_sha256'] == hashlib.sha256(package.read_bytes()).hexdigest()
    return package, report['package_sha256']


def write(path, value):
    path.write_text(json.dumps(value))
    return path


@pytest.mark.parametrize('entry,suite', [('Derived', None), ('Derived', 'spongefish0.7.4.keccak.bls12-381.fr64be/0'), ('Plain', None)])
def test_independent_named_proof_calls(toolchain, journal, directory, entry, suite):
    source = directory / 'source.zkc'
    text = (FIXTURES / 'attempts.zkc').read_text()
    source.write_text(text.replace('merlin3.bls12-381.fr64be/0', suite) if suite else text)
    package, pin = compile_entry(toolchain, journal, directory, entry, source)
    witness = write(directory / 'witness.json', {'done': True})
    proof = directory / 'proof.bin'
    results = directory / 'results.json'
    target = [f'--package={package}', f'--sha256={pin}']
    flags = ['--allow-header-only'] if entry == 'Plain' else []
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
    inputs = write(directory / 'P.json', {'done': True})
    outputs = directory / 'outputs.json'
    command = [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
               '--session=cli_controls', f'--input=P={inputs}', f'--results={outputs}']
    report = journal.json(command)
    assert report['status'] == 'executed'
    values = json.loads(outputs.read_text())['roles']
    assert values['V']['accepted'] is True
    assert values['P']['result']['ready'] is True
    assert json.dumps(values['P']['padding']) not in json.dumps(report)
    assert all(role['outputs'] is None for role in report['execution']['roles'])
    sentinel = outputs.read_bytes()
    journal.run([*command, '--service=V.challenges=0'], refuses='entry-run-incomplete')
    assert outputs.read_bytes() == sentinel
    journal.run([*command, '--service=V.unknown=1'], refuses='entry-service-names')
    write(inputs, {'done': True, 'extra': True})
    journal.run(command, refuses='entry-input-names')
    journal.run([*command, '--results=duplicate'], refuses='cli-option')


def test_aggregate_file_roundtrip_and_schema_refusals(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', FIXTURES / 'host_values.zkc')
    payload = {'choice': {'case': 'Data', 'fields': {
        '0': {'case': 'Pair', 'fields': {'0': '7', '1': '11'}},
        '1': [False, None], '2': ['13', '17']}}, 'marker': True}
    inputs = write(directory / 'P.json', {'payload': payload, 'empty': None})
    results = directory / 'results.json'
    command = [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
               '--session=aggregate_files', f'--input=P={inputs}', f'--results={results}']
    journal.run(command)
    outputs = json.loads(results.read_text())['roles']
    assert outputs['V'] == {'received': payload, 'empty': None}
    assert outputs['P']['sent'] == payload
    mutations = [
        ({'choice': {'case': 'Absent', 'fields': {}}, 'marker': True}, 'entry-input-alternative'),
        ({'choice': {'case': 'Empty', 'fields': {'extra': True}}, 'marker': True}, 'entry-input-fields'),
        ({'choice': {'case': 'Empty', 'fields': {}}, 'marker': 1}, 'entry-input-shape'),
        ({'choice': {'case': 'Empty', 'fields': {}}}, 'entry-input-fields'),
    ]
    for changed, code in mutations:
        write(inputs, {'payload': changed, 'empty': None})
        journal.run(command, refuses=code)


def test_generated_bindings_are_an_independent_rust_consumer(toolchain, journal, directory):
    run_package, run_pin = compile_entry(toolchain, journal, directory, 'Demo', FIXTURES / 'host_values.zkc')
    proof_package, proof_pin = compile_entry(toolchain, journal, directory, 'Derived')
    shapes_dir = directory / 'shapes'
    shapes_dir.mkdir()
    collision = shapes_dir / 'p.zkc'
    collision.write_text('module p;pub struct Outputs {pub flag:bool}')
    shapes_package = shapes_dir / 'Demo.zkpkg'
    shapes_report = json.loads(journal.run([
        toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--module=sample={FIXTURES / "host_bindings.zkc"}', f'--module=p={collision}',
        'sample::Demo', f'--output={shapes_package}',
    ]))
    shapes_pin = shapes_report['package_sha256']
    pcs_package, pcs_pin = compile_entry(toolchain, journal, directory, 'Prove', FIXTURES / 'pcs_setup.zkc')
    for name, package, pin in [('run', run_package, run_pin), ('proof', proof_package, proof_pin), ('shapes', shapes_package, shapes_pin), ('pcs', pcs_package, pcs_pin)]:
        journal.run([toolchain.runtime, '--json', 'bindings', f'--package={package}', f'--sha256={pin}', f'--output={directory / f'{name}.rs'}'])
    original = run_package.read_bytes()
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={run_package}', f'--sha256={run_pin}', f'--output={run_package}'], refuses='entry-output-path')
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={run_package}', f'--sha256={run_pin}', f'--output={directory / 'unused.rs'}', '--setups=missing'], refuses='cli-option')
    assert run_package.read_bytes() == original
    # This is a consumer crate, not a module compiled under zkc-tools internals.
    (directory / 'Cargo.toml').write_text(f'''[package]
name = "entry-bindings-consumer"
version = "0.0.0"
edition = "2018"
[workspace]
[dependencies]
zkc-tools = {{ path = {json.dumps(str(ROOT / 'crates/zkc-tools'))} }}
[[bin]]
name = "entry-bindings-consumer"
path = "main.rs"
''')
    shutil.copyfile(ROOT / 'Cargo.lock', directory / 'Cargo.lock')
    (directory / 'main.rs').write_text(r'''#![deny(warnings)]
#[allow(dead_code)] mod run { include!("run.rs"); }
#[allow(dead_code)] mod proof { include!("proof.rs"); }
#[allow(dead_code)] mod pcs { include!("pcs.rs"); }
#[allow(dead_code, non_camel_case_types)] mod shapes {
    struct String; struct Box; struct From; struct TryFrom; #[allow(non_camel_case_types)] struct entry;
    type Result<T> = ::core::result::Result<T, ()>;
    struct Ok; struct Err;
    struct bool; struct u64; struct u8; struct str;
    #[allow(unused_macros)] macro_rules! Debug { ($($items:tt)*) => { compile_error!("shadowed Debug") }; }
    #[allow(unused_macros)] macro_rules! vec { ($($items:tt)*) => { compile_error!("shadowed vec") }; }
    include!("shapes.rs");
}
use zkc_tools::entry::{RoleInputs,RunRequest,ProofRequest};
use std::convert::{TryFrom,TryInto};
fn main() {
    let args:Vec<_>=std::env::args().collect();
    let scalar = |n:u8| -> zkc_tools::entry::Value {
        let mut frame=b"ZKCV\x00\x01".to_vec();
        let mut bytes=[0u8;32]; bytes[0]=n; frame.extend_from_slice(&bytes);
        zkc_tools::execution::InputValue::Wire(frame).into()
    };
    // Public API construction, independent of private zkc-tools modules. The
    // actual setup-bearing calls are separately exercised across CLI processes.
    let key=||zkc_tools::entry::Value::from(zkc_tools::execution::InputValue::ProverKeyFile {
        path:"prover.key".into(), fingerprint:[0;32],
    });
    let input=pcs::PInputs{pk0:key(),pk1:key(),data0:scalar(0),data1:scalar(0)};
    let input:zkc_tools::entry::NamedValues=input.into();
    assert!(matches!(input.get("pk0").unwrap(),zkc_tools::entry::Value::Leaf(zkc_tools::execution::InputValue::ProverKeyFile{..})));
    let _public=pcs::PublicInputs{claim:pcs::SampleClaim{c:scalar(0),tag:true},point:scalar(0)};
    let _verifier=pcs::VInputs{};
    assert_eq!(pcs::setups::first,"first");
    let malformed=zkc_tools::entry::Value::Array(vec![zkc_tools::entry::Value::Record([("extra".into(),true.into())].into())]);
    assert_eq!(<[shapes::SampleEmpty;1]>::try_from(malformed).err().unwrap(),"entry-binding-fields");
    let named:zkc_tools::entry::Value=shapes::SampleCases::a__b{}.into();
    let zkc_tools::entry::Value::Variant{alternative,..}=named else{panic!()};
    assert_eq!(alternative,"a__b");
    assert_eq!(pcs::PROVER,"P"); assert_eq!(pcs::VERIFIER,"V");
    assert_eq!(proof::services::coins,"coins");
    let bytes=std::fs::read(&args[3]).unwrap();
    let host=shapes::admit(&bytes,Default::default(),Default::default()).unwrap();
    let input=shapes::PInputs {
        empty:shapes::SampleEmpty{}, choice:shapes::SampleCases::__zkc_53656c66{},
        names:shapes::SampleNames{r#async:true,__zkc_73656c66:false,Foo:true,foo:false,__zkc_5f:true},
        zero:[], collision:shapes::POutputs2{flag:true},
    };
    let mut named:zkc_tools::entry::NamedValues=input.into();
    let zkc_tools::entry::Value::Record(fields)=named.get("names").unwrap() else {panic!()};
    assert!(fields.contains_key("Foo") && fields.contains_key("foo") && fields.contains_key("_"));
    let zkc_tools::entry::Value::Record(mut fields)=named.remove("names").unwrap() else {panic!()};
    assert!(bool::try_from(fields.remove("Foo").unwrap()).unwrap());
    assert!(!bool::try_from(fields.remove("foo").unwrap()).unwrap());
    fields.insert("Foo".into(),true.into()); fields.insert("foo".into(),false.into());
    named.insert("names".into(),zkc_tools::entry::Value::Record(fields));
    let restored:shapes::PInputs=std::mem::take(&mut named).try_into().unwrap();
    assert!(restored.names.Foo && !restored.names.foo);
    let mut result=host.prepare(RunRequest{session:"binding_shapes".into(),setups:Default::default(),
        roles:[("P".into(),RoleInputs{inputs:restored.into(),..Default::default()})].into(),
    }).unwrap().execute();
    assert!(result.is_success());
    let output:shapes::POutputs=result.outputs.as_mut().unwrap().remove("P").unwrap().try_into().unwrap();
    assert!(output.wrapped.value);
    assert!(matches!(output.choice,shapes::SampleCases::__zkc_53656c66{}));
    let mut invalid:zkc_tools::entry::NamedValues=output.into();
    invalid.insert("extra".into(),true.into());
    assert_eq!(shapes::POutputs::try_from(invalid).err().unwrap(),"entry-binding-fields");

    let bytes=std::fs::read(&args[1]).unwrap();
    let host=run::admit(&bytes,Default::default(),Default::default()).unwrap();
    let inputs=run::PInputs {
        payload:run::SamplePayload {choice:run::SampleChoice::Data {
            item_0:run::SampleInner::Pair{item_0:scalar(7),item_1:scalar(11)},
            item_1:run::PInputsPayloadChoiceData1{item_0:false,item_1:()},
            item_2:[scalar(13),scalar(17)],
        },marker:true},
        empty:(),
    };
    let mut report=host.prepare(RunRequest {
        session:"generated_bindings".into(),setups:Default::default(),roles:[
            inputs.into_role(),
            run::VInputs{}.into_role(),
        ].into(),
    }).unwrap().execute();
    let received=run::VOutputs::take(report.outputs.as_mut().unwrap()).unwrap();
    assert!(received.received.marker);
    assert!(matches!(received.received.choice,run::SampleChoice::Data{..}));
    let bytes=zkc_tools::entry::files::proof_outputs(&received.into(),Default::default(),Default::default()).unwrap();
    assert!(std::str::from_utf8(&bytes).unwrap().contains(r#""7""#));
    let mut tampered=bytes;tampered.push(b' ');
    assert_eq!(run::admit(&tampered,Default::default(),Default::default()).err().unwrap().code(),"entry-package-identity");

    let bytes=std::fs::read(&args[2]).unwrap();
    let prover=proof::admit(&bytes,Default::default(),Default::default()).unwrap();
    let verifier=proof::admit(&bytes,Default::default(),Default::default()).unwrap();
    let produced=prover.prove(ProofRequest{public:proof::PublicInputs{}.into(),
        private:RoleInputs{inputs:proof::PInputs{done:true}.into(),..Default::default()},..Default::default()}).unwrap();
    assert!(produced.is_success());
    let returned:proof::POutputs=produced.outputs.unwrap().try_into().unwrap();
    assert!(returned.result.ready);
    let checked=verifier.verify(ProofRequest{public:proof::PublicInputs{}.into(),
        private:RoleInputs{inputs:proof::VInputs{}.into(),..Default::default()},..Default::default()},&produced.native.outcome.unwrap()).unwrap();
    assert!(checked.is_success());
    let checked:proof::VOutputs=checked.outputs.unwrap().try_into().unwrap();
    assert!(checked.accepted);
}
''')
    journal.run(['cargo', 'run', '--offline', '--quiet', '--manifest-path', directory / 'Cargo.toml',
                 '--target-dir', ROOT / 'target', '--', run_package, proof_package, shapes_package], timeout=600)


def test_input_numbers_keep_their_json_shape(toolchain, journal, directory):
    source = directory / 'indices.zkc'
    source.write_text("module sample; protocol Index roles(P)(n:index@P)->(n:index@P){return(n=n);} run Demo=Index;")
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    inputs = write(directory / 'P.json', {'n': '7'})
    command = [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
               '--session=index_files', f'--input=P={inputs}']
    journal.run(command)
    for value in [7, {'$serde_json::private::Number': '7'}, '07', '+7', '18446744073709551616']:
        write(inputs, {'n': value})
        journal.run(command, refuses='entry-input-shape' if not isinstance(value, str) else 'entry-input-decimal')
    for number in [-1, 1.0, 2 ** 64]:
        write(inputs, {'n': number})
        journal.run(command, refuses='entry-request-format')


@pytest.mark.skipif(not hasattr(os, 'mkfifo'), reason='POSIX file descriptors')
def test_file_jobs_refuse_unconnected_streams(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    fifo = directory / 'fifo'
    os.mkfifo(fifo)
    # There is no writer. Refusal precedes any protocol resource issuance.
    report = json.loads(journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', '--session=fifo', f'--input=P={fifo}'],
                                   refuses='entry-input-document', timeout=10))
    assert report['phase'] == 'inputs' and 'execution' not in report
    journal.run([toolchain.runtime, '--json', 'run', f'--package={fifo}', f'--sha256={pin}', '--session=fifo', f'--input=P={fifo}'], refuses='artifact-io', timeout=10)


def test_bindings_refuse_outputs_without_host_export(toolchain, journal, directory):
    source = directory / 'restricted.zkc'
    source.write_text('module sample; struct Restricted:Drop{pub b:bool}'
                      'fn make()->Restricted{return Restricted{b:true};}'
                      'protocol Run roles(P)()->(r:Restricted@P){'
                      'let r @P =make();return(r=r);}run Demo=Run;')
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    bindings = directory / 'bindings.rs'
    bindings.write_bytes(b'unchanged')
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={package}', f'--sha256={pin}', f'--output={bindings}'],
                refuses='entry-output-custody')
    assert bindings.read_bytes() == b'unchanged'
    journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', '--session=restricted'],
                refuses='entry-output-custody')


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
    source.write_text('module sample; protocol Run roles(P)(b:bool@P)->(b:bool@P){return(b=b);} run Demo=Run;')
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
    baseline = json.loads(journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}', '--allow-header-only']))
    accepted_proof = proof.read_bytes()
    proof.write_bytes(b'existing proof')
    limits = baseline['capacity']
    limits[3] = '64'
    capacity = write(directory / 'capacity.json', limits)
    report = json.loads(journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}', '--allow-header-only', f'--capacity={capacity}', f'--results={results}'], refuses='entry-output-encoding'))
    assert report['phase'] == 'results' and not report.get('proof_published', False)
    assert proof.read_bytes() == b'existing proof'
    assert results.read_bytes() == b'unchanged'
    proof.write_bytes(accepted_proof)
    journal.run([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}', '--allow-header-only', f'--results={results}'])
    assert json.loads(results.read_text())['values']['accepted'] is True


def test_interface_publication_and_host_share_resource_boundaries(toolchain, journal, directory):
    source = directory / 'source.zkc'
    def program(count):
        ports = ','.join(f'a{i}:[();1024]@P' for i in range(count))
        return f'module sample;protocol Run roles(P)({ports})->(){{return();}}run Demo=Run;'
    source.write_text(program(7))
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={package}', f'--sha256={pin}', f'--output={directory / 'bindings.rs'}'])
    request = input_files(journal, (directory / 'inputs.json').name, session='bounded_interface', roles={'P': {'inputs': {f'a{i}': [None] * 1024 for i in range(7)}}})
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


@pytest.mark.parametrize('entry,kind', [('Derived', 'proof'), ('Plain', 'proof'), ('Run', 'run')])
def test_inspect_authenticates_without_execution(toolchain, journal, directory, entry, kind):
    package, pin = compile_entry(toolchain, journal, directory, entry)
    sentinel = package.read_bytes()
    report = journal.json([toolchain.runtime, '--json', 'inspect', f'--package={package}', f'--sha256={pin}'])
    assert report['format'] == 'zkc.entry-inspection/0' and report['status'] == 'inspected'
    assert report['phase'] == 'complete' and report['package_sha256'] == pin
    interface = report['interface']
    assert interface['entry'] == f'sample::{entry}' and interface['kind'] == kind
    assert len(interface['toolchain']) == 64 and interface['setups'] == []
    roles = {role['name']: role for role in interface['roles']}
    assert set(roles) == {'P', 'V'}
    assert any(port['name'] == 'done' and port['type'] == 'bool' for port in roles['P']['inputs'])
    if kind == 'proof':
        proof = interface['proof']
        assert proof['prover'] == 'P' and proof['verifier'] == 'V'
        assert proof['acceptance'] == {'port': 'accepted', 'path': [], 'role': 'V'}
        assert proof['completion'] == {'port': 'result', 'path': [0], 'role': 'P'}
        assert proof['public'] == []
        assert (proof['transcript_suite'] is not None) == (entry == 'Derived')
    else:
        assert interface['proof'] is None
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
    inputs = input_files(journal, (directory / 'inputs.json').name, session='limited', roles={'P': {'inputs': {'done': True}}, 'V': {'inputs': {}}})
    limits = write(directory / 'limits.json', ['zkc.bundle-limits/0', '0', '1024', '1024', '100000'])
    sentinel = limits.read_bytes()
    command = [toolchain.runtime, '--json', 'run', f'--limits={limits}', f'--package={package}', f'--sha256={pin}', *inputs]
    refused = journal.json(command, refuses='entry-run-incomplete')
    assert refused['phase'] == 'execution'
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
    proving = [toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}', '--allow-header-only']
    verifying = [toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}', '--allow-header-only']
    assert journal.json(proving)['status'] == 'produced'
    assert journal.json(verifying)['status'] == 'accepted'
    input_files(journal, 'producer', public={}, witness={'produce': True, 'accept': False})
    assert journal.json(proving)['status'] == 'produced'
    report = journal.json(verifying, refuses='artifact-stopped')
    assert report['execution']['stop']['kind'] == 'Explicit("reject")'
    assert report['execution']['stop']['role'] == 'V'
    input_files(journal, 'producer', public={}, witness={'produce': False, 'accept': True})
    proof.unlink()
    report = journal.json(proving, refuses='artifact-stopped')
    assert not proof.exists(), 'producer rejection published a partial proof'
    assert 'Explicit("reject")' in str(report)
