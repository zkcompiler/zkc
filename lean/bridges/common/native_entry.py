"""Select the native protocol subject of a one-call source Entry function.

These bridges compare protocol execution, not the enclosing application. Compile
its current package and retain the exact native Run child's source and interface.
This helper accepts no alternate carrier or source syntax.
"""

import hashlib
import json


def native_run(execute, compiler, flags):
    """Return authenticated source bytes and interface of exactly one Run child."""
    package = json.loads(execute([compiler, 'language-package', *flags]))
    assert package['format'] == 'zkc.entry/0'
    selection = json.loads(package['interface'])
    assert selection['selection']['kind'] == 'function'
    host = json.loads(package['artifact'])
    assert host['format'] == 'zkc.host/0'
    assert len(host['deployments']) == 1, 'bridge requires exactly one native invocation'
    deployment, = host['deployments']
    assert deployment['operation'] == 'run'
    child = json.loads(deployment['package'])
    assert child['format'] == 'zkc.entry/0'
    interface = json.loads(child['interface'])
    assert interface['job']['kind'] == 'run'
    source = child['original']
    assert interface['original'] == hashlib.sha256(source.encode()).hexdigest()
    return source, interface
