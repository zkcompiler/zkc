"""Separate CLI jobs adapt authenticated source packages to the shared Host."""
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
    package = directory / f'{entry}.entry'
    args = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
            f'--module=sample={source or FIXTURES / "attempts.zkc"}',
            f'--entry=sample::{entry}', f'--output={package}']
    report = json.loads(journal.run(args))
    assert report['status'] == 'compiled'
    assert Path(report['compiler']).is_absolute() and len(report['toolchain']) == 64
    assert report['package_sha256'] == hashlib.sha256(package.read_bytes()).hexdigest()
    return package, report['package_sha256']


def write(path, value):
    path.write_text(json.dumps(value))
    return path


@pytest.mark.parametrize('entry,suite', [('Derived', None), ('Derived', 'spongefish0.7.4.keccak.bls12-381.fr64be/1'), ('Plain', None)])
def test_independent_named_proof_calls(toolchain, journal, directory, entry, suite):
    source = directory / 'source.zkc'
    text = (FIXTURES / 'attempts.zkc').read_text()
    source.write_text(text.replace('merlin3.bls12-381.fr64be/1', suite) if suite else text)
    package, pin = compile_entry(toolchain, journal, directory, entry, source)
    producer = write(directory / 'producer.json', {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {'done': True}})
    verifier = write(directory / 'verifier.json', {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {}})
    proof = directory / 'proof.bin'
    results = directory / 'results.json'
    flags = ['--allow-header-only'] if entry == 'Plain' else []
    proving = [toolchain.runtime, 'prove', package, pin, producer, proof, *flags]
    verifying = [toolchain.runtime, 'verify', package, pin, verifier, proof, *flags]
    if entry == 'Plain':
        journal.run(proving[:-1], refuses='entry-proof-binding-policy')
    produced = json.loads(journal.run([*proving, f'--results={results}']))
    assert produced['status'] == 'produced' and produced['proof_published']
    assert produced['execution']['attempts'][0]['decision'] == 'complete'
    values = json.loads(results.read_text())['values']
    assert values['result']['ready'] is True
    # A secret result is available only in the explicitly selected file.
    assert values['padding'] not in json.dumps(produced)
    accepted = json.loads(journal.run(verifying))
    assert accepted['status'] == 'accepted'
    assert accepted['binding_scope'] == ('header' if flags else 'transcript')
    sentinel = proof.read_bytes()
    bad = directory / 'bad-proof.bin'
    changed = bytearray(sentinel)
    changed[0] ^= 1
    bad.write_bytes(changed)
    unchanged_results = results.read_bytes()
    rejection = json.loads(journal.run([*verifying[:5], bad, *flags, f'--results={results}'], refuses='proof-header'))
    assert rejection['status'] == 'refused' and 'execution' in rejection
    assert results.read_bytes() == unchanged_results
    bad.write_bytes(sentinel + b'\x00')
    journal.run([*verifying[:5], bad, *flags, f'--results={results}'], refuses='proof-trailing')
    if entry == 'Derived':
        changed = bytearray(sentinel)
        changed[-32] ^= 1  # Change the canonical response scalar, preserving its frame.
        bad.write_bytes(changed)
        rejected = json.loads(journal.run([*verifying[:5], bad, *flags, f'--results={results}'], refuses='artifact-rejected'))
        assert rejected['status'] == 'refused' and 'execution' in rejected
    assert results.read_bytes() == unchanged_results
    write(verifier, {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {}, 'context': '01'})
    rejected_context = json.loads(journal.run([*verifying, f'--results={results}'], refuses='proof-header'))
    assert rejected_context['status'] == 'refused' and results.read_bytes() == unchanged_results
    write(verifier, {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {}})
    journal.run([*proving, '--attempts=0'], refuses='native-attempt-limits')
    assert proof.read_bytes() == sentinel
    collision = json.loads(journal.run([*proving, f'--results={proof}'], refuses='entry-output-path'))
    assert collision['phase'] == 'arguments' and 'execution' not in collision
    journal.run([*verifying, f'--results={proof}'], refuses='entry-output-path')
    alias = directory / 'directory-alias'
    alias.symlink_to(directory, target_is_directory=True)
    journal.run([*proving, f'--results={alias / proof.name}'], refuses='entry-output-path')
    assert proof.read_bytes() == sentinel
    journal.run([*proving, f'--results={package}'], refuses='entry-output-path')
    journal.run([*proving, f'--results={producer}'], refuses='entry-output-path')
    write(producer, {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {'done': False}})
    refused = json.loads(journal.run(proving, refuses='native-attempt-limit'))
    assert len(refused['execution']['attempts']) == 1
    assert proof.read_bytes() == sentinel
    refused = json.loads(journal.run([*proving, '--attempts=3'], refuses='native-attempt-limit'))
    assert len(refused['execution']['attempts']) == 3
    assert proof.read_bytes() == sentinel
    write(producer, {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {'done': True}, 'services': {'coins': 0}})
    journal.run(proving, refuses='exhausted:resource-budget')
    assert proof.read_bytes() == sentinel
    producer.write_text('{"format":"zkc.entry-proof","public":{},"inputs":{"done":true,"done":false}}')
    journal.run(proving, refuses='entry-request-format')
    wrong_pin = '00' * 32
    journal.run([toolchain.runtime, 'prove', package, wrong_pin, producer, proof, *flags], refuses='entry-package-identity')
    if entry == 'Derived':
        write(producer, {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {'done': True}, 'transcript_budget': 0})
        journal.run(proving, refuses='exhausted:resource-budget')
    write(producer, {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {'done': True}})
    failed_publication = json.loads(journal.run([*proving, f'--results={directory / "missing" / "results"}'], refuses='entry-output-path'))
    assert failed_publication['phase'] == 'arguments' and 'execution' not in failed_publication
    assert proof.read_bytes() == sentinel


def test_named_run_defaults_and_private_result_files(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    request = {'format': 'zkc.entry-run', 'session': 'cli_controls',
               'roles': {'P': {'inputs': {'done': True}}, 'V': {'inputs': {}}}}
    inputs = write(directory / 'inputs.json', request)
    outputs = directory / 'outputs.json'
    command = [toolchain.runtime, 'run', package, pin, inputs, f'--results={outputs}']
    report = json.loads(journal.run(command))
    assert report['status'] == 'executed'
    values = json.loads(outputs.read_text())['roles']
    assert values['V']['accepted'] is True
    assert values['P']['result']['ready'] is True
    assert values['P']['padding'] not in json.dumps(report)
    assert all(role['outputs'] is None for role in report['execution']['roles'])
    sentinel = outputs.read_bytes()
    request['roles']['V']['services'] = {'challenges': 0}
    write(inputs, request)
    journal.run(command, refuses='entry-run-incomplete')
    assert outputs.read_bytes() == sentinel
    request['roles']['V']['services'] = {'unknown': 1}
    write(inputs, request)
    journal.run(command, refuses='entry-service-names')
    request['roles']['V'].pop('services')
    request['roles']['P']['inputs']['extra'] = True
    write(inputs, request)
    journal.run(command, refuses='entry-input-names')
    journal.run([*command, '--results=duplicate'], refuses='entry-option')


def test_aggregate_file_roundtrip_and_schema_refusals(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', FIXTURES / 'host_values.zkc')
    # Installed scalar messages carry the ZKCV version/type frame.
    def scalar(value):
        return (b'ZKCV\x01\x01' + value.to_bytes(32, 'little')).hex()
    payload = {'choice': {'case': 'Data', 'fields': {
        '0': {'case': 'Pair', 'fields': {'0': scalar(7), '1': scalar(11)}},
        '1': [False, None], '2': [scalar(13), scalar(17)]}}, 'marker': True}
    request = {'format': 'zkc.entry-run', 'session': 'aggregate_files', 'roles': {
        'P': {'inputs': {'payload': payload, 'empty': None}}, 'V': {'inputs': {}}}}
    inputs = write(directory / 'inputs.json', request)
    results = directory / 'results.json'
    command = [toolchain.runtime, 'run', package, pin, inputs, f'--results={results}']
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
        request['roles']['P']['inputs']['payload'] = changed
        write(inputs, request)
        journal.run(command, refuses=code)


def test_generated_bindings_are_an_independent_rust_consumer(toolchain, journal, directory):
    run_package, run_pin = compile_entry(toolchain, journal, directory, 'Demo', FIXTURES / 'host_values.zkc')
    proof_package, proof_pin = compile_entry(toolchain, journal, directory, 'Derived')
    shapes_dir = directory / 'shapes'
    shapes_dir.mkdir()
    collision = shapes_dir / 'p.zkc'
    collision.write_text('module p;pub struct Outputs {pub flag:bool}')
    shapes_package = shapes_dir / 'Demo.entry'
    shapes_report = json.loads(journal.run([
        toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
        f'--module=sample={FIXTURES / "host_bindings.zkc"}', f'--module=p={collision}',
        '--entry=sample::Demo', f'--output={shapes_package}',
    ]))
    shapes_pin = shapes_report['package_sha256']
    pcs_package, pcs_pin = compile_entry(toolchain, journal, directory, 'Prove', FIXTURES / 'pcs_setup.zkc')
    for name, package, pin in [('run', run_package, run_pin), ('proof', proof_package, proof_pin), ('shapes', shapes_package, shapes_pin), ('pcs', pcs_package, pcs_pin)]:
        journal.run([toolchain.runtime, 'bindings', package, pin, directory / f'{name}.rs'])
    original = run_package.read_bytes()
    journal.run([toolchain.runtime, 'bindings', run_package, run_pin, run_package], refuses='entry-output-path')
    journal.run([toolchain.runtime, 'bindings', run_package, run_pin, directory / 'unused.rs', '--setups=missing'], refuses='entry-option')
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
        let mut frame=b"ZKCV\x01\x01".to_vec();
        let mut bytes=[0u8;32]; bytes[0]=n; frame.extend_from_slice(&bytes);
        zkc_tools::run::InputValue::Wire(frame).into()
    };
    // Public API construction, independent of private zkc-tools modules. The
    // actual setup-bearing calls are separately exercised across CLI processes.
    let key=||zkc_tools::entry::Value::from(zkc_tools::run::InputValue::ProverKeyFile {
        path:"prover.key".into(), fingerprint:[0;32],
    });
    let input=pcs::PInputs{pk0:key(),pk1:key(),data0:scalar(0),data1:scalar(0)};
    let input:zkc_tools::entry::NamedValues=input.into();
    assert!(matches!(input.get("pk0").unwrap(),zkc_tools::entry::Value::Leaf(zkc_tools::run::InputValue::ProverKeyFile{..})));
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
    assert!(std::str::from_utf8(&bytes).unwrap().contains("5a4b4356010107000000"));
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
    source.write_text("module sample; protocol Index roles(P)(n:index@P)->(n:index@P){return(n=n);} entry Demo=Index;")
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    request = {'format': 'zkc.entry-run', 'session': 'index_files', 'roles': {'P': {'inputs': {'n': 7}}}}
    inputs = write(directory / 'inputs.json', request)
    command = [toolchain.runtime, 'run', package, pin, inputs]
    journal.run(command)
    request['roles']['P']['inputs']['n'] = {'$serde_json::private::Number': '7'}
    write(inputs, request)
    journal.run(command, refuses='entry-input-shape')
    for number in [-1, 1.0, 2 ** 64]:
        request['roles']['P']['inputs']['n'] = number
        write(inputs, request)
        journal.run(command, refuses='entry-request-format')


@pytest.mark.skipif(not hasattr(os, 'mkfifo'), reason='POSIX file descriptors')
def test_file_jobs_refuse_unconnected_streams(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    fifo = directory / 'fifo'
    os.mkfifo(fifo)
    # There is no writer. Refusal precedes any protocol resource issuance.
    report = json.loads(journal.run([toolchain.runtime, 'run', package, pin, fifo],
                                   refuses='artifact-io', timeout=10))
    assert report['phase'] == 'inputs' and 'execution' not in report
    journal.run([toolchain.runtime, 'run', fifo, pin, fifo], refuses='artifact-io', timeout=10)


def test_bindings_refuse_outputs_without_host_export(toolchain, journal, directory):
    source = directory / 'restricted.zkc'
    source.write_text('module sample; struct Restricted:Drop{pub b:bool}'
                      'fn make()->Restricted{return Restricted{b:true};}'
                      'protocol Run roles(P)()->(r:Restricted@P){'
                      'local P let r=make();return(r=r);}entry Demo=Run;')
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    bindings = directory / 'bindings.rs'
    bindings.write_bytes(b'unchanged')
    journal.run([toolchain.runtime, 'bindings', package, pin, bindings],
                refuses='entry-output-custody')
    assert bindings.read_bytes() == b'unchanged'
    journal.run([toolchain.runtime, 'run', package, pin, directory / 'unused'],
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
        journal.run([toolchain.runtime, 'compile', f'--compiler={selected}',
                     f'--output={output}'], refuses='entry-output-path')
        assert compiler.read_bytes() == original and alias.is_symlink()


def test_compiler_failures_are_bounded_and_do_not_publish(toolchain, journal, directory):
    compiler = directory / 'compiler'
    compiler.write_text(f'#!{sys.executable}\nimport sys\nsys.stderr.write("X" * 70000)\nsys.exit(1)\n')
    compiler.chmod(0o755)
    output = directory / 'existing.entry'
    output.write_bytes(b'unchanged')
    report = json.loads(journal.run([toolchain.runtime, 'compile', f'--compiler={compiler}', f'--output={output}'], refuses='entry-compilation'))
    assert report['diagnostics_truncated'] and len(report['diagnostics']) == 65536
    assert output.read_bytes() == b'unchanged'
    journal.run([toolchain.runtime, 'compile', f'--compiler={directory / "missing"}', f'--output={output}'], refuses='entry-compiler-missing')


def test_proof_file_public_inputs_are_authoritative(toolchain, journal, directory):
    source = directory / 'public.zkc'
    source.write_text((FIXTURES / 'attempts.zkc').read_text()
                      .replace('Round roles(P,V)(done:bool@P)', 'Round roles(P,V)(done:bool@P,tag:bool@(P,V))')
                      .replace('public{};accept accepted;complete result.ready;', 'public{tag};accept accepted;complete result.ready;', 1))
    package, pin = compile_entry(toolchain, journal, directory, 'Derived', source)
    producer = write(directory / 'producer.json', {'format': 'zkc.entry-proof', 'public': {'tag': True}, 'inputs': {'done': True}})
    verifier = write(directory / 'verifier.json', {'format': 'zkc.entry-proof', 'public': {'tag': True}})
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    verifying = [toolchain.runtime, 'verify', package, pin, verifier, proof]
    journal.run(verifying)
    write(verifier, {'format': 'zkc.entry-proof', 'public': {'tag': True}, 'inputs': {'tag': True}})
    journal.run(verifying, refuses='entry-input-names')
    write(verifier, {'format': 'zkc.entry-proof', 'public': {}})
    journal.run(verifying, refuses='entry-input-names')
    write(verifier, {'format': 'zkc.entry-proof', 'public': {'tag': False}})
    journal.run(verifying, refuses='proof-header')
    original = source.read_bytes()
    journal.run([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                 f'--module=sample={source}', '--entry=sample::Derived', f'--output={source}'],
                refuses='entry-output-path')
    assert source.read_bytes() == original


def test_compiler_lookup_and_positional_arguments(toolchain, journal, directory):
    source = directory / 'source.zkc'
    source.write_text('module sample; protocol Run roles(P)(b:bool@P)->(b:bool@P){return(b=b);} entry Demo=Run;')
    args = [toolchain.runtime, 'compile', '--module=sample=source.zkc', '--entry=sample::Demo', '--output=demo.entry']
    env = dict(os.environ, PATH=str(toolchain.compiler.parent))
    result = journal.attempt(args, cwd=directory, env=env)
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'compiled'
    # A bare compiler name refers to trusted PATH, not this same-named output.
    local_output = directory / 'zkc-compile'
    same_name = journal.attempt([*args[:-1], '--output=zkc-compile'], cwd=directory, env=env)
    assert same_name.returncode == 0, same_name.stdout + same_name.stderr
    assert json.loads(local_output.read_text())['format'] == 'zkc.entry'
    local_output.unlink()
    (directory / 'zkc-compile').symlink_to(toolchain.compiler)
    for path in (None, '', '.'):
        env = dict(os.environ)
        if path is None:
            env.pop('PATH', None)
        else:
            env['PATH'] = path
        result = journal.attempt(args, cwd=directory, env=env)
        assert result.returncode == 1 and json.loads(result.stdout)['code'] == 'entry-compiler-missing'
    package = directory / 'demo.entry'
    for command in ('prove', 'bindings'):
        args = [toolchain.runtime, command, package, report['package_sha256']]
        if command == 'prove':
            args.append('request.json')
        journal.run([*args, '--results=output.json'], refuses='entry-usage')


def test_results_encoding_failure_preserves_previous_files(toolchain, journal, directory):
    source = directory / 'source.zkc'
    source.write_text('''module sample;
domain Fr=field("bls12-381.fr");
type Vector<F:Field>=builtin("vector",F);
fn filled(x:Fr)->Vector<Fr>{let n:index=3;return kernel<Fr>("vector.fill",x,n);}
protocol Run roles(P,V)(done:bool@P)->(large:Vector<Fr>@P,accepted:bool@V){
  local P let large=filled(1);
  let actual=send P->V(done);
  return(large=large,accepted=actual);
}
entry Demo=Run{prover P;verifier V;public{};accept accepted;construction authored;}
''')
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    producer = write(directory / 'producer.json', {'format': 'zkc.entry-proof', 'public': {}, 'inputs': {'done': True}})
    verifier = write(directory / 'verifier.json', {'format': 'zkc.entry-proof', 'public': {}})
    proof = directory / 'proof.bin'
    results = directory / 'results.json'
    results.write_bytes(b'unchanged')
    baseline = json.loads(journal.run([toolchain.runtime, 'prove', package, pin, producer, proof, '--allow-header-only']))
    accepted_proof = proof.read_bytes()
    proof.write_bytes(b'existing proof')
    limits = baseline['capacity']
    limits[3] = '64'
    capacity = write(directory / 'capacity.json', limits)
    report = json.loads(journal.run([toolchain.runtime, 'prove', package, pin, producer, proof,
        '--allow-header-only', f'--capacity={capacity}', f'--results={results}'], refuses='entry-output-encoding'))
    assert report['phase'] == 'results' and not report.get('proof_published', False)
    assert proof.read_bytes() == b'existing proof'
    assert results.read_bytes() == b'unchanged'
    proof.write_bytes(accepted_proof)
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, proof, '--allow-header-only', f'--results={results}'])
    assert json.loads(results.read_text())['values']['accepted'] is True


def test_interface_publication_and_host_share_resource_boundaries(toolchain, journal, directory):
    source = directory / 'source.zkc'
    def program(count):
        ports = ','.join(f'a{i}:[();1024]@P' for i in range(count))
        return f'module sample;protocol Run roles(P)({ports})->(){{return();}}entry Demo=Run;'
    source.write_text(program(7))
    package, pin = compile_entry(toolchain, journal, directory, 'Demo', source)
    journal.run([toolchain.runtime, 'bindings', package, pin, directory / 'bindings.rs'])
    request = write(directory / 'inputs.json', {
        'format': 'zkc.entry-run', 'session': 'bounded_interface',
        'roles': {'P': {'inputs': {f'a{i}': [None] * 1024 for i in range(7)}}},
    })
    executed = json.loads(journal.run([toolchain.runtime, 'run', package, pin, request]))
    assert executed['status'] == 'executed'
    source.write_text(program(9))
    refused = directory / 'oversized.entry'
    result = json.loads(journal.run([
        toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
        f'--module=sample={source}', '--entry=sample::Demo', f'--output={refused}',
    ], refuses='entry-compilation'))
    assert 'source.limit' in result['diagnostics']
    assert not refused.exists()
