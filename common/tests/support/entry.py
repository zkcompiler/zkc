"""Compile a .zkc Entry and run it through the ordinary common Host commands."""

from input_files import input_files

import json


class Entry:
    def __init__(self, toolchain, journal, directory, source, flags=()):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        path = directory / 'kernels.zkc'
        path.write_text(source)
        self.package = directory / 'kernels.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=sample={path}', 'sample::Demo',
                               f'--output={self.package}', *flags])
        self.pin = report['package_sha256']

    def run(self, name, inputs, *, refuses=None):
        result = self.run_roles(name, {'P': {'inputs': inputs}}, refuses=refuses)
        return result if refuses else result['P']

    def run_roles(self, name, roles, *, refuses=None):
        request = input_files(self.journal, f'{name}.inputs.json', session='kernel_controls', roles=roles)
        output = self.directory / f'{name}.outputs.json'
        report = self.journal.json([self.tools.runtime, '--json', 'run', f'--package={self.package}', f'--sha256={self.pin}', *request, f'--results={output}'], refuses=refuses)
        if refuses:
            assert report['status'] == 'refused'
            assert not output.exists(), 'failed execution published output values'
            return report
        assert report['status'] == 'executed'
        return json.loads(output.read_text())['roles']
