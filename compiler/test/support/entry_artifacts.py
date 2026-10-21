"""Read the exact native Run child of an explicitly selected Host wrapper.

Native protocol and structured-export tests inspect this child's authenticated
original/interface/artifact. Their parent Entry remains a real Host function.
"""

import json

from tools import compiler


def single_run_package(package):
    """Require one Run deployment and return its exact current package fields."""
    outer = json.loads(package)
    assert outer['format'] == 'zkc.entry/0'
    interface = json.loads(outer['interface'])
    assert interface['selection']['kind'] == 'function'
    host = json.loads(outer['artifact'])
    assert host['format'] == 'zkc.host/0'
    assert len(host['deployments']) == 1
    deployment, = host['deployments']
    assert deployment['operation'] == 'run'
    child = json.loads(deployment['package'])
    assert child['format'] == 'zkc.entry/0'
    assert json.loads(child['interface'])['job']['kind'] == 'run'
    return child


def compile_run_package(commands, *options):
    """Compile the selected function before inspecting its single native child."""
    return single_run_package(commands.run(
        [compiler, 'language-package', *options]))
