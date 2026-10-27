"""Generated Rust bindings exercise the normal-feature SDK outside the checkout."""

import json
from pathlib import Path
import shutil

from entry import compile_named_entry

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = ROOT / 'compiler/test/fixtures/language'


def test_generated_bindings_are_an_independent_rust_consumer(toolchain, journal, directory, monkeypatch):
    numerical = directory / 'numerical.zkc'
    numerical.write_text('''module sample;
fn increment(value:index)->index{return value+1;}
entry fn Next(value:index){return increment(value);}
entry fn Twice(value:index){let next=Next(value);return Next(next);}
entry fn Checked(value:index,valid:bool){require valid;return increment(value);}
protocol Echo<T:Type> roles(P)(value:T@P)->(out:T@P){return value;}
''')
    numerical_package, numerical_pin = compile_named_entry(toolchain, journal, directory, 'Twice', numerical)
    generic_package, generic_pin = compile_named_entry(toolchain, journal, directory, 'Echo<index>', numerical)
    checked_package, checked_pin = compile_named_entry(toolchain, journal, directory, 'Checked', numerical)
    run_package, run_pin = compile_named_entry(toolchain, journal, directory, 'Demo', FIXTURES / 'host_values.zkc')
    proof_source = directory / 'statement.zkc'
    proof_text = (FIXTURES / 'attempts.zkc').read_text()
    proof_text = proof_text.replace('(done:bool@P, coins:', '(expected:bool@(P,V), done:bool@P, coins:', 1)
    proof_text = proof_text.replace('accepted=ok);', 'accepted=ok && expected);', 1)
    proof_text = proof_text.replace('prover P;verifier V;public{};accept accepted;complete result.ready;',
                                    'prover P;verifier V;public{expected};accept accepted;complete result.ready;', 1)
    proof_source.write_text(proof_text)
    proof_package, proof_pin = compile_named_entry(toolchain, journal, directory, 'Derived', proof_source)
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
    pcs_package, pcs_pin = compile_named_entry(toolchain, journal, directory, 'Prove', FIXTURES / 'pcs_setup.zkc')
    for name, package, pin in [
        ('run', run_package, run_pin), ('proof', proof_package, proof_pin),
        ('shapes', shapes_package, shapes_pin), ('pcs', pcs_package, pcs_pin),
        ('numerical', numerical_package, numerical_pin), ('generic', generic_package, generic_pin),
        ('checked', checked_package, checked_pin),
    ]:
        journal.run([toolchain.runtime, '--json', 'bindings', f'--package={package}', f'--sha256={pin}', f'--output={directory / f'{name}.rs'}'])
    original = run_package.read_bytes()
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={run_package}', f'--sha256={run_pin}', f'--output={run_package}'], refuses='entry-output-path')
    journal.run([toolchain.runtime, '--json', 'bindings', f'--package={run_package}', f'--sha256={run_pin}', f'--output={directory / 'unused.rs'}', '--setups=missing'], refuses='cli-option')
    assert run_package.read_bytes() == original
    # This is a consumer crate, not a module compiled under zkc internals.
    (directory / 'Cargo.toml').write_text(f'''[package]
name = "entry-bindings-consumer"
version = "0.0.0"
edition = "2018"
[workspace]
[dependencies]
zkc = {{ path = {json.dumps(str(ROOT / 'crates/zkc'))} }}
[[bin]]
name = "entry-bindings-consumer"
path = "main.rs"
''')
    shutil.copyfile(ROOT / 'Cargo.lock', directory / 'Cargo.lock')
    (directory / 'main.rs').write_text(r'''#![deny(warnings)]
#[allow(dead_code)] mod numerical { include!("numerical.rs"); }
#[allow(dead_code)] mod generic { include!("generic.rs"); }
#[allow(dead_code)] mod checked { include!("checked.rs"); }
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
use zkc::entry::{RoleInputs,ProofRequest,FunctionEntry,FunctionInterface,
    InvocationContext,InvocationBinding,RunContext,Package,SetupAuthority};
fn authority(bytes:&[u8],pin:&[u8;32])->std::collections::BTreeMap<String,SetupAuthority> {
    let package=Package::capture(bytes,pin,Package::MAX_BYTES).unwrap();
    let children=FunctionInterface::deployment_interfaces(&package).unwrap();
    children.iter().map(|child|{
        assert_eq!(child.operation(),"run");
        assert_eq!(child.interface().setup_names().len(),0);
        (child.id().into(),Default::default())
    }).collect()
}
fn context(host:&FunctionEntry,session:&str)->InvocationContext {
    InvocationContext{deployments:host.deployments().map(|(id,operation)|{
        assert_eq!(operation,"run");
        (id.into(),InvocationBinding::Run(RunContext{session:Some(session.into()),..Default::default()}))
    }).collect()}
}
use std::convert::{TryFrom,TryInto};
fn main() {
    assert!(!zkc::EXECUTION_COUNTS_ENABLED);
    let args:Vec<_>=std::env::args().collect();
    let bytes=std::fs::read(&args[4]).unwrap();
    let cpu=zkc::execution::CpuExecution::new(2).unwrap();
    let host=numerical::admit_with_cpu(&bytes,Default::default(),Default::default(),cpu.clone()).unwrap();
    assert_eq!(host.cpu().workers(),2);
    let prepared=host.prepare(zkc::entry::FunctionRequest {
        arguments:numerical::Arguments{value:7}.into(),context:Default::default(),
    }).unwrap();
    assert!(prepared.execute().is_success());
    for _ in 0..2 {
        let result=numerical::call(&host,numerical::Arguments{value:7},Default::default()).unwrap();
        assert_eq!(result.value,Some(9));
        assert!(result.report.is_success() && result.conversion_error.is_none());
        assert!(result.report.usage.execution.instructions>0);
    }
    let bytes=std::fs::read(&args[5]).unwrap();
    let host=generic::admit_with_cpu(&bytes,Default::default(),authority(&bytes,&generic::PACKAGE_SHA256),cpu.clone()).unwrap();
    for value in [17u64,23] {
        let arguments=zkc::entry::NamedValues::from([("inputs".into(),zkc::entry::Value::Record(
            [("P".into(),zkc::entry::Value::Record([("value".into(),value.into())].into()))].into()))]);
        let result=generic::call(&host,generic::Arguments::try_from(arguments).unwrap(),context(&host,"generic")).unwrap();
        assert!(result.report.is_success() && result.conversion_error.is_none());
        let zkc::entry::Value::Record(mut roles)=result.value.unwrap().into() else{panic!()};
        let zkc::entry::Value::Record(mut values)=roles.remove("P").unwrap() else{panic!()};
        assert_eq!(u64::try_from(values.remove("out").unwrap()).unwrap(),value);
    }
    let bytes=std::fs::read(&args[6]).unwrap();
    let host=checked::admit(&bytes,Default::default(),Default::default()).unwrap();
    let result=checked::call(&host,checked::Arguments{value:7,valid:false},Default::default()).unwrap();
    assert!(result.value.is_none() && result.conversion_error.is_none());
    assert!(!result.report.is_success());
    assert_eq!(result.report.failure.unwrap().code,"entry-host-require");
    // Generated bindings must refuse another admitted Host, even with matching shapes.
    let error=numerical::call(&host,numerical::Arguments{value:7},Default::default()).unwrap_err();
    assert_eq!(error.code(),"entry-binding-package");
    assert_eq!(error.phase,zkc::entry::EntryPhase::Binding);
    let scalar = |n:u8| -> zkc::entry::Value {
        let mut frame=b"ZKCV\x00\x01".to_vec();
        let mut bytes=[0u8;32]; bytes[0]=n; frame.extend_from_slice(&bytes);
        zkc::execution::InputValue::Wire(frame.into()).into()
    };
    // Public API construction, independent of private zkc modules. The
    // actual setup-bearing calls are separately exercised across CLI processes.
    let key=||zkc::entry::Value::from(zkc::execution::InputValue::ProverKeyFile {
        path:"prover.key".into(), fingerprint:[0;32],
    });
    let input=pcs::PInputs{pk0:key(),pk1:key(),data0:scalar(0),data1:scalar(0)};
    let input:zkc::entry::NamedValues=input.into();
    assert!(matches!(input.get("pk0").unwrap(),zkc::entry::Value::Leaf(zkc::execution::InputValue::ProverKeyFile{..})));
    let _public=pcs::PublicInputs{claim:pcs::SampleClaim{c:scalar(0),tag:true},point:scalar(0)};
    let _verifier=pcs::VInputs{};
    assert_eq!(pcs::setups::first,"first");
    let malformed=zkc::entry::Value::Array(vec![zkc::entry::Value::Record([("extra".into(),true.into())].into())]);
    assert_eq!(<[shapes::SampleEmpty;1]>::try_from(malformed).err().unwrap(),"entry-binding-fields");
    let named:zkc::entry::Value=shapes::SampleCases::a__b{}.into();
    let zkc::entry::Value::Variant{alternative,..}=named else{panic!()};
    assert_eq!(alternative,"a__b");
    assert_eq!(pcs::PROVER,"P"); assert_eq!(pcs::VERIFIER,"V");
    assert_eq!(proof::services::coins,"coins");
    let bytes=std::fs::read(&args[3]).unwrap();
    let host=shapes::admit(&bytes,Default::default(),authority(&bytes,&shapes::PACKAGE_SHA256)).unwrap();
    let input=shapes::SampleShapesInputsP {
        empty:shapes::SampleEmpty{}, choice:shapes::SampleCases::__zkc_53656c66{},
        names:shapes::SampleNames{__zkc_6173796e63:true,__zkc_73656c66:false,Foo:true,foo:false,__zkc_5f:true},
        zero:[], collision:shapes::POutputs{flag:true},
    };
    let zkc::entry::Value::Record(mut named)=input.into() else {panic!()};
    let zkc::entry::Value::Record(fields)=named.get("names").unwrap() else {panic!()};
    assert!(fields.contains_key("Foo") && fields.contains_key("foo") && fields.contains_key("_"));
    let zkc::entry::Value::Record(mut fields)=named.remove("names").unwrap() else {panic!()};
    assert!(bool::try_from(fields.remove("Foo").unwrap()).unwrap());
    assert!(!bool::try_from(fields.remove("foo").unwrap()).unwrap());
    fields.insert("Foo".into(),true.into()); fields.insert("foo".into(),false.into());
    named.insert("names".into(),zkc::entry::Value::Record(fields));
    let restored:shapes::SampleShapesInputsP=zkc::entry::Value::Record(std::mem::take(&mut named)).try_into().unwrap();
    assert!(restored.names.Foo && !restored.names.foo);
    let result=shapes::call(&host,shapes::Arguments{
        inputs:shapes::SampleShapesInputs{P:restored},
    },context(&host,"binding_shapes")).unwrap();
    assert!(result.report.is_success(),"{}",result.report.diagnostics());
    assert!(result.conversion_error.is_none());
    let output=result.value.unwrap().P;
    assert!(output.wrapped.value);
    assert!(matches!(output.choice,shapes::SampleCases::__zkc_53656c66{}));
    let zkc::entry::Value::Record(mut invalid)=output.into() else {panic!()};
    invalid.insert("extra".into(),true.into());
    assert_eq!(shapes::SampleShapesRunResultP::try_from(zkc::entry::Value::Record(invalid)).err().unwrap(),"entry-binding-fields");

    let bytes=std::fs::read(&args[1]).unwrap();
    let host=run::admit(&bytes,Default::default(),authority(&bytes,&run::PACKAGE_SHA256)).unwrap();
    let inputs=run::SampleEchoInputsP {
        payload:run::SamplePayload {choice:run::SampleChoice::Data {
            item_0:run::SampleInner::Pair{item_0:scalar(7),item_1:scalar(11)},
            item_1:run::ArgumentsInputsPPayloadChoiceData1{item_0:false,item_1:()},
            item_2:[scalar(13),scalar(17)],
        },marker:true},
        empty:(),
    };
    let result=run::call(&host,run::Arguments{
        inputs:run::SampleEchoInputs{P:inputs,V:run::SampleEchoInputsV{}},
    },context(&host,"generated_bindings")).unwrap();
    assert!(result.report.is_success(),"{}",result.report.diagnostics());
    assert!(result.conversion_error.is_none());
    let received=result.value.unwrap().V;
    assert!(received.received.marker);
    assert!(matches!(received.received.choice,run::SampleChoice::Data{..}));
    let zkc::entry::Value::Record(values)=received.into() else {panic!()};
    let output=zkc::entry::outputs::proof_outputs(&values,Default::default(),Default::default()).unwrap();
    assert!(std::str::from_utf8(&output).unwrap().contains(r#""7""#));
    let mut tampered=bytes;tampered.push(b' ');
    assert_eq!(run::admit(&tampered,Default::default(),Default::default()).err().unwrap().code(),"entry-package-identity");

    let bytes=std::fs::read(&args[2]).unwrap();
    let prover=proof::admit(&bytes,Default::default(),Default::default()).unwrap();
    let verifier=proof::admit(&bytes,Default::default(),Default::default()).unwrap();
    let produced=prover.prove(ProofRequest{public:proof::PublicInputs{expected:true}.into(),
        private:RoleInputs{inputs:proof::PInputs{done:true}.into(),..Default::default()},..Default::default()}).unwrap();
    assert!(produced.is_success());
    let returned:proof::POutputs=produced.outputs.unwrap().try_into().unwrap();
    assert!(returned.result.ready);
    let checked=verifier.verify(ProofRequest{public:proof::PublicInputs{expected:true}.into(),
        private:RoleInputs{inputs:proof::VInputs{}.into(),..Default::default()},..Default::default()},&produced.native.outcome.unwrap()).unwrap();
    assert!(checked.is_success());
    let checked:proof::VOutputs=checked.outputs.unwrap().try_into().unwrap();
    assert!(checked.accepted);
    let produced=prover.prove(ProofRequest{public:proof::PublicInputs{expected:true}.into(),
        private:RoleInputs{inputs:proof::PInputs{done:true}.into(),..Default::default()},..Default::default()}).unwrap();
    let changed=verifier.verify(ProofRequest{public:proof::PublicInputs{expected:false}.into(),
        private:RoleInputs{inputs:proof::VInputs{}.into(),..Default::default()},..Default::default()},&produced.native.outcome.unwrap()).unwrap();
    assert!(!changed.is_success());
    assert_eq!(changed.native.outcome.as_ref().err().map(String::as_str),Some("proof-header"));
}
''')
    for key, value in dict(CARGO_BUILD_JOBS='4', CARGO_INCREMENTAL='0',
                           CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0').items():
        monkeypatch.setenv(key, value)
    metadata = json.loads(journal.run(['cargo', 'metadata', '--offline', '--format-version=1',
                                      '--manifest-path', directory / 'Cargo.toml']))
    names = {package['id']: package['name'] for package in metadata['packages']}
    for node in metadata['resolve']['nodes']:
        if names[node['id']] in ('zkc', 'zkc-cpu', 'zkc-runtime', 'zkc-kernels'):
            assert not {'test-utils', 'execution-counts'} & set(node['features']), node
    target = directory / 'consumer-target'
    journal.run(['cargo', 'build', '--offline', '--quiet', '--manifest-path', directory / 'Cargo.toml',
                 '--target-dir', target], timeout=600)
    execution = directory / 'execution'
    execution.mkdir()
    binary = execution / 'entry-bindings-consumer'
    shutil.copyfile(target / 'debug/entry-bindings-consumer', binary)
    binary.chmod(0o700)
    monkeypatch.setenv('PATH', '')
    for key in ('ZKC_COMPILER_BIN', 'ZKC_NATIVE_BIN', 'ZKC_COMPILER'):
        monkeypatch.setenv(key, '/unavailable')
    journal.run([binary, run_package, proof_package, shapes_package, numerical_package,
                 generic_package, checked_package], cwd=execution)
