"""Preparation distinguishes logical unknowns from checked child policies."""

import json
from pathlib import Path

import pytest

from zkc import Client


@pytest.fixture
def policy_project(directory):
    (directory / 'main.zkc').write_text('''module application;
protocol Equality roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(accepted:bool@V){
  let received=send P->V(candidate);
  let accepted@V=received==expected;
  return(accepted=accepted);
}
proof Core=Equality{
  prover P;verifier V;public{expected};accept accepted;construction authored;
}
entry fn Produce(inputs:Equality::Inputs,public:Core::Public,witness:Core::Witness){
  let joint=Equality::run(inputs);
  let produced=Core::prove(public,witness);
  return produced.proof;
}
''')
    manifest = directory / 'zkc.toml'
    manifest.write_text('format="zkc.project/0"\n[modules]\napplication="main.zkc"\n')
    return manifest


def arguments():
    return {'inputs': {'P': {'expected': True, 'candidate': True}, 'V': {'expected': True}},
            'public': {'expected': True}, 'witness': {'candidate': True}}


def check_command(toolchain, entry):
    command = entry['requirements']['check_command']
    assert command == [*entry['commands'][0], '--dry-run']
    assert '--allow-authored' not in command
    return [toolchain.runtime, '--json', *command[1:]]


def test_source_prepare_reports_unresolved_children_and_checks_policy(
        toolchain, journal, directory, policy_project):
    prepared = journal.json([toolchain.runtime, '--json', 'prepare', 'Produce',
        f'--project={policy_project}', f'--compiler={toolchain.compiler}'])
    entry = prepared['entries'][0]
    assert entry['requirements']['allow_authored'] is None
    assert entry['requirements']['unresolved'] == ['child_policies']
    Path(prepared['files'][0]).write_text(json.dumps(arguments()))
    command = check_command(toolchain, entry)
    journal.json(command, refuses='entry-proof-binding-policy')
    checked = journal.json([*command, '--allow-authored'])
    assert checked['status'] == 'inputs-checked' and 'execution' not in checked
    assert {child['operation'] for child in checked['invocations']} == {'run', 'prove'}
    assert len(checked['invocations']) == 2


@pytest.mark.parametrize('selector,expected', [('Equality', False), ('Produce', True)])
def test_package_prepare_resolves_each_child_policy(
        toolchain, journal, directory, policy_project, selector, expected):
    package = directory / 'entry.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', selector,
        f'--project={policy_project}', f'--compiler={toolchain.compiler}', f'--output={package}'])
    prepared = journal.json([toolchain.runtime, '--json', 'prepare', f'--package={package}',
        f'--sha256={compiled["package_sha256"]}', f'--output={directory / "inputs"}'])
    entry = prepared['entries'][0]
    requirements = entry['requirements']
    assert requirements['allow_authored'] is expected
    assert 'unresolved' not in requirements
    children = requirements['deployments']
    assert len(children) == (2 if expected else 1)
    assert len({child['id'] for child in children}) == len(children)
    assert all(child['setups'] == [] for child in children)
    assert all(child['allow_authored'] == (child['operation'] == 'prove') for child in children)
    values = arguments() if expected else {'inputs': arguments()['inputs']}
    Path(prepared['files'][0]).write_text(json.dumps(values))
    command = check_command(toolchain, entry)
    if expected:
        journal.json(command, refuses='entry-proof-binding-policy')
        command.append('--allow-authored')
    assert journal.json(command)['status'] == 'inputs-checked'


def test_python_dry_runs_preserve_native_input_and_policy_validation(toolchain, policy_project):
    client = Client(policy_project, executable=toolchain.runtime, compiler=toolchain.compiler)
    refused = client.run(arguments(), entry='Produce', options=['--dry-run'])
    assert not refused.ok and refused.report['code'] == 'entry-proof-binding-policy'
    options = ['--dry-run', '--allow-authored']
    checked = client.run(arguments(), entry='Produce', options=options).require_success()
    assert checked.report['status'] == 'inputs-checked'
    assert checked.value is None and checked.proof is None
    invalid = arguments() | {'public': {'expected': None}}
    refused = client.run(invalid, entry='Produce', options=options)
    assert not refused.ok and refused.report['code'] == 'entry-input-unfilled'
    public, witness = {'expected': True}, {'candidate': True}
    checked = client.prove(public, witness, entry='Core', options=options).require_success()
    assert checked.report['status'] == 'inputs-checked' and checked.proof is None
    proof = client.prove(public, witness, entry='Core', options=['--allow-authored']).require_success().proof
    checked = client.verify(public, proof, entry='Core', options=options).require_success()
    assert checked.report['status'] == 'inputs-checked' and checked.value is None
