"""Compile a .zkc Entry and run it through the ordinary common Host commands."""

from input_files import input_files, invocation_file

import hashlib
import json
from pathlib import Path


def joint_package(package):
    """Read the exact native child of a function with one joint invocation."""
    assert package['format'] == 'zkc.entry/0'
    host = json.loads(package['artifact'])
    assert host['format'] == 'zkc.host/0'
    children = host['deployments']
    assert len(children) == 1 and children[0]['operation'] == 'run'
    child = json.loads(children[0]['package'])
    assert child['format'] == 'zkc.entry/0'
    interface = json.loads(child['interface'])
    assert interface['format'] == 'zkc.language-interface/0'
    assert interface['job']['kind'] == 'run'
    return child


def joint_artifact(package):
    return json.loads(joint_package(package)['artifact'])


def replace_joint_package(package, child):
    host = json.loads(package['artifact'])
    joint_package(package)  # Check the exact single-child boundary before mutation.
    host['deployments'][0]['package'] = json.dumps(child, separators=(',', ':'))
    package['artifact'] = json.dumps(host, separators=(',', ':'))


def replace_joint_artifact(package, artifact):
    """Keep adversarial mutations inside the current native deployment boundary."""
    child = joint_package(package)
    child['artifact'] = json.dumps(artifact, separators=(',', ':'))
    replace_joint_package(package, child)


def replace_joint_assets(package, assets):
    child = joint_package(package)
    child['assets'] = assets
    replace_joint_package(package, child)
    package['assets'] = assets


def joint_execution(report):
    """The native joint report of a wrapper's one reached protocol call."""
    execution = report['execution']
    assert execution['format'] == 'zkc.entry-function-result/0'
    calls = [call for call in execution['calls'] if call['operation'] == 'run']
    assert len(calls) == 1, 'expected exactly one reached protocol invocation'
    return calls[0]['native']


def project_invocation(toolchain, journal, directory, *, entry=None, project=None):
    """Compile the selected project to bind its exact static child identities."""
    project = project or directory / 'zkc.toml'
    stem = (entry or 'selected').replace('::', '.')
    package = directory / f'{stem}.invocation.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile',
                  f'--compiler={toolchain.compiler}', f'--project={project}',
                  *([entry] if entry else []), f'--output={package}'])
    return invocation_file(journal, f'{stem}.invocations.json', package)


class Entry:
    def __init__(self, toolchain, journal, directory, source, flags=(), *, entry='Demo'):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        path = directory / 'kernels.zkc'
        path.write_text(source)
        self.package = directory / 'kernels.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=sample={path}', f'sample::{entry}',
                               f'--output={self.package}', *flags])
        self.pin = report['package_sha256']

    def run(self, name, inputs, *, refuses=None, capacity=None):
        result = self.run_roles(name, {'P': inputs}, refuses=refuses, capacity=capacity)
        return result if refuses else result['P']

    def run_roles(self, name, roles, *, role_services=None, refuses=None, capacity=None):
        request = input_files(self.journal, f'{name}.inputs.json', package=self.package,
                              session='kernel_controls',
                              arguments={'inputs': roles}, role_services=role_services)
        output = self.directory / f'{name}.outputs.json'
        limits = [f'--capacity={capacity}'] if capacity is not None else []
        report = self.journal.json([self.tools.runtime, '--json', 'run', f'--package={self.package}', f'--sha256={self.pin}', *request, f'--results={output}', *limits], refuses=refuses)
        if refuses:
            assert report['status'] == 'refused'
            assert not output.exists(), 'failed execution published output values'
            return report
        assert report['status'] == 'executed'
        document = json.loads(output.read_text())
        assert document['format'] == 'zkc.entry-outputs/0'
        assert document.keys() == {'format', 'value'}
        return document['value']


def compile_named_entry(toolchain, journal, directory, entry, source):
    package = directory / f'{entry}.zkpkg'
    args = [toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
            f'--module=sample={source}',
            f'sample::{entry}', f'--output={package}']
    report = json.loads(journal.run(args))
    assert report['status'] == 'compiled'
    assert Path(report['compiler']).is_absolute() and len(report['toolchain']) == 64
    assert report['package_sha256'] == hashlib.sha256(package.read_bytes()).hexdigest()
    return package, report['package_sha256']
