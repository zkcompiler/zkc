"""Serialization and checked Lean presentation of the one Structured reader.

Python never lowers or evaluates a source operation. The executable printer
proposes typed bodies and normal forms; compiled modules check every equation.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.structured.snapshot import render
from request_support import require

ROOT = Path(__file__).resolve().parents[2]


def entry(data):
    render(data, 'Shape')
    matches = [d for d in data[7] if d[0] == 'function' and d[1] == data[3]]
    require(len(matches) == 1 and matches[0][2] == 'protocol', 'source-entry',
            'Select exactly one retained protocol')
    return matches[0]


def profile(data, field, group=None):
    """Restrict nominal assignments, including dormant helpers, without evaluation."""
    def walk(value):
        if not isinstance(value, list):
            return
        if value and isinstance(value[0], str):
            tag = value[0]
            if tag in ('field', 'group', 'service') and len(value) == 2:
                expected = {'field': field, 'group': group, 'service': 'random.' + field + '/0'}[tag]
                require(value[1] == expected and expected is not None,
                        'domain-assignment', 'Unassigned nominal scalar domain')
            if tag.startswith('field.'):
                require(tag in ('field.constant', 'field.add', 'field.subtract', 'field.multiply', 'field.equal')
                        and value[1] == field, 'domain-assignment', 'Unsupported field operation or domain')
            if tag.startswith('group.'):
                require(group is not None and value[1] == group and
                        (tag != 'group.scale' or value[2] == field),
                        'domain-assignment', 'Unassigned group or scalar action')
            require(tag not in ('vector', 'index', 'sequence', 'product', 'exec', 'local_call',
                                'protocol_apply', 'protocol_repeat'),
                    'scalar-profile', 'This request requires the retained scalar profile')
        for child in value:
            walk(child)
    # Catalogue and source-origin metadata are not executable sorts.
    for definition in data[7]:
        require(definition[0] == 'function', 'scalar-profile', 'Expected scalar function definitions')
        walk(definition[4:8])
        walk(definition[9])


def views(data, directory, prefix, role, executable=None, timeout=30):
    """Emit data plus Lean-owned phased admission and present-input equations."""
    executable = executable or ROOT / '.lake/build/bin/structured-source'
    directory.mkdir(parents=True, exist_ok=True)
    source = directory / (prefix + '.json')
    config = directory / (prefix + '-views.json')
    source.write_text(json.dumps(data) + '\n')
    config.write_text(json.dumps([prefix + 'Inputs', prefix + 'Data', prefix + 'View', role]))
    result = subprocess.run([str(executable), 'scalar-views', str(source), str(config)],
                            capture_output=True, text=True, timeout=min(30, timeout))
    (directory / (prefix + '-printer.log')).write_text(result.stdout + result.stderr)
    require(result.returncode == 0, 'structured-admission',
            'Structured admission/view printer refused the source; inspect printer log')
    printed = json.loads(result.stdout)
    modules = {prefix + 'Data': render(data, prefix + 'Data'),
               prefix + 'Inputs': printed['inputs'], prefix + 'View': printed['view']}
    for name, source in modules.items():
        path = directory / (name.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
    return list(modules)


def lean_environment(environment, directory, lake='lake'):
    env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_NUM_THREADS': '2'}
    path = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=environment,
                                   env=env, text=True).strip()
    env['LEAN_PATH'] = str(directory.resolve()) + ':' + path
    return env


def compile_modules(directory, modules, environment=ROOT, lake='lake', timeout=180):
    deadline = time.monotonic() + timeout
    env = lean_environment(environment, directory, lake)
    logs = []
    for module in modules:
        path = directory / (module.replace('.', '/') + '.lean')
        result = subprocess.run(['lean', '-j2', '-M16384', '--root=' + str(directory.resolve()),
                                 '-o', str(path.with_suffix('.olean')), str(path.resolve())],
                                cwd=directory, env=env, capture_output=True, text=True, timeout=max(0.001, deadline - time.monotonic()))
        log = directory / (module.replace('.', '_') + '.log')
        log.write_text(result.stdout + result.stderr)
        logs.append(str(log))
        require(result.returncode == 0, 'correspondence-unproved',
                'Lean refused a generated module: ' + str(log))
    return logs
