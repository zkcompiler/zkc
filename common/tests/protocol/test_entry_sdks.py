"""Source, CLI, Python and generated Rust calls share the admitted Entry Host."""

import json
from pathlib import Path

from zkc import Client

ROOT = Path(__file__).resolve().parents[3]


def source(directory):
    path = directory / "main.zkc"
    path.write_text('''module application;
fn increment(value: index) -> index { return value + 1; }
entry fn Next(value: index) { return increment(value); }
entry fn Twice(value: index) {
  let next = Next(value);
  return Next(next);
}
entry fn Checked(value: index, valid: bool) {
  require valid;
  return increment(value);
}
''')
    manifest = directory / "zkc.toml"
    manifest.write_text('format = "zkc.project/0"\n[modules]\napplication = "main.zkc"\n')
    return path, manifest


def test_python_and_cli_return_the_same_source_value(toolchain, journal, directory):
    _, manifest = source(directory)
    client = Client(manifest, executable=toolchain.runtime, compiler=toolchain.compiler)
    view = client.inspect("Twice").require_success().value
    assert view["kind"] == "function"
    assert [parameter["name"] for parameter in view["signature"]["parameters"]] == ["value"]
    outcome = client.run({"value": "7"}, entry="Twice").require_success()
    assert outcome.value == "9"
    inputs = journal.write("arguments.json", {"value": "7"})
    output = directory / "cli-result.json"
    cli = journal.json([toolchain.runtime, "--json", "run", "Twice", f"--project={manifest}",
                        f"--compiler={toolchain.compiler}", f"--input={inputs}", f"--results={output}"])
    assert json.loads(output.read_text())["value"] == outcome.value
    assert cli["execution"]["usage"] == outcome.report["execution"]["usage"]
    failure = client.run({"value": "7", "valid": False}, entry="Checked")
    assert not failure.ok and failure.value is None
    assert failure.report["execution"]["failure"]


def test_generated_rust_calls_the_same_host_and_keeps_reports(toolchain, journal, directory):
    _, manifest = source(directory)
    package = directory / "twice.zkpkg"
    compiled = journal.json([toolchain.runtime, "--json", "compile", "Twice",
                             f"--project={manifest}", f"--compiler={toolchain.compiler}",
                             f"--output={package}"])
    bindings = directory / "bindings.rs"
    journal.json([toolchain.runtime, "--json", "bindings", f"--package={package}",
                  f"--sha256={compiled['package_sha256']}", f"--output={bindings}"])
    (directory / "Cargo.toml").write_text(f'''[package]
name = "entry-function-consumer"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
zkc-tools = {{path = {str(ROOT / 'crates/zkc-tools')!r}}}
''')
    (directory / "src").mkdir()
    (directory / "src/main.rs").write_text('''mod bindings { include!(concat!(env!("CARGO_MANIFEST_DIR"), "/bindings.rs")); }
fn main() -> Result<(), Box<dyn std::error::Error>> {
  let bytes = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/twice.zkpkg"));
  let host = bindings::admit(bytes, Default::default(), Default::default())?;
  let result = bindings::call(&host, bindings::Arguments { value: 7 }, Default::default())?;
  assert_eq!(result.value, Some(9));
  assert!(result.conversion_error.is_none());
  assert!(result.report.is_success());
  assert!(result.report.usage.execution.instructions > 0);
  Ok(())
}
''')
    journal.run(["cargo", "run", "--offline", "--quiet", "--jobs=2", "--manifest-path",
                 directory / "Cargo.toml", "--target-dir", ROOT / "target"])


def test_python_calls_generated_proof_apis_with_independent_public_inputs(toolchain, directory):
    (directory / 'main.zkc').write_text('''module application;
protocol Equality roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(accepted:bool@V){
  let received = send P->V(candidate);
  let accepted@V = received == expected;
  return(accepted=accepted);
}
proof Core = Equality {
  prover P; verifier V; public{expected}; accept accepted; construction authored;
}
entry fn Produce(public:Core::Public,witness:Core::Witness){
  let result=Core::prove(public,witness);
  return result.proof;
}
entry fn Validate(public:Core::Public,candidate:Core::Proof){
  return Core::verify(public,candidate);
}
entry fn Withhold(public:Core::Public,witness:Core::Witness,complete:bool){
  let produced=Core::prove(public,witness);
  require complete;
  return produced.proof;
}
''')
    manifest = directory / 'zkc.toml'
    manifest.write_text('format="zkc.project/0"\n[modules]\napplication="main.zkc"\n')
    client = Client(manifest, executable=toolchain.runtime, compiler=toolchain.compiler)
    options = ['--allow-authored']
    positive = client.run({'public': {'expected': True}, 'witness': {'candidate': True}},
                          entry='Produce', options=options).require_success()
    accepted = client.run({'public': {'expected': True}, 'candidate': positive.value},
                          entry='Validate', options=options).require_success()
    assert accepted.value == {'case': 'Accepted', 'fields': {'outputs': {'accepted': True}}}
    negative = client.run({'public': {'expected': True}, 'witness': {'candidate': False}},
                          entry='Produce', options=options).require_success()
    rejected = client.run({'public': {'expected': True}, 'candidate': negative.value},
                          entry='Validate', options=options).require_success()
    assert rejected.value == {'case': 'Rejected', 'fields': {}}
    wrong_statement = client.run({'public': {'expected': False}, 'candidate': positive.value},
                                 entry='Validate', options=options)
    assert not wrong_statement.ok and wrong_statement.value is None
    withheld = client.run({'public': {'expected': True}, 'witness': {'candidate': True},
                            'complete': False}, entry='Withhold', options=options)
    assert not withheld.ok and withheld.value is None
    assert any(call['operation'] == 'prove' and call['completed']
               for call in withheld.report['execution']['calls'])
    public_file = directory / 'public.json'
    witness_file = directory / 'witness.json'
    public_file.write_text(json.dumps({'expected': True}))
    witness_file.write_text(json.dumps({'candidate': True}))
    proof = client.prove(public_file, witness_file, entry='Core', options=options).require_success().proof
    assert proof is not None
    assert client.verify(public_file, proof, entry='Core', options=options).require_success().ok


def test_python_input_documents_keep_confined_file_references(toolchain, directory):
    import hashlib

    _, manifest = source(directory)
    wire = b'ZKCV\x00\x1f' + (7).to_bytes(8, 'little')
    data = directory / 'data'
    data.mkdir()
    (data / 'index.zkcv').write_bytes(wire)
    arguments = data / 'arguments.json'
    arguments.write_text(json.dumps({'value': {
        'file': 'index.zkcv', 'sha256': hashlib.sha256(wire).hexdigest(),
    }}))
    client = Client(manifest, executable=toolchain.runtime, compiler=toolchain.compiler)
    result = client.run(arguments, entry='Twice').require_success()
    assert result.value == '9'
    alias = data / 'alias.json'
    alias.symlink_to(arguments.name)
    refused = client.run(alias, entry='Twice')
    assert not refused.ok and refused.report['code'] == 'entry-input-document'
    arguments.write_text(json.dumps({'value': {'file': '../index.zkcv', 'sha256': '0' * 64}}))
    refused = client.run(arguments, entry='Twice')
    assert not refused.ok and refused.value is None
    assert refused.report['code'] == 'entry-input-reference'
