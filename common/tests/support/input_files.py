"""Write explicit Entry input maps and return ordinary CLI options for tests."""
from pathlib import Path
import json


def decimal_values(value, schema=None):
    """Serialize arithmetic integers while preserving schema-owned byte arrays."""
    if schema is not None:
        if schema['leaves'] == ['bytes'] and schema['kind'] == 'builtin':
            return value
        if schema['kind'] == 'variant' and isinstance(value, dict):
            alternative = next((a for a in schema['alternatives']
                                if a['name'] == value.get('case')), None)
            if alternative is not None and isinstance(value.get('fields'), dict):
                fields = {f['name']: f['schema'] for f in alternative['fields']}
                return value | {'fields': {name: decimal_values(item, fields.get(name))
                                            for name, item in value['fields'].items()}}
        if isinstance(value, dict):
            fields = {f['name']: f['schema'] for f in schema['fields']}
            return {name: decimal_values(item, fields.get(name))
                    for name, item in value.items()}
        if isinstance(value, list) and schema['kind'] in ('array', 'tuple'):
            fields = {f['name']: f['schema'] for f in schema['fields']}
            return [decimal_values(item, fields.get(str(i)))
                    for i, item in enumerate(value)]
    if type(value) is int:
        return str(value)
    if isinstance(value, list):
        return [decimal_values(v) for v in value]
    if isinstance(value, dict):
        return {k: decimal_values(v) for k, v in value.items()}
    return value


def argument_values(arguments, package):
    document = json.loads(Path(package).read_text())
    assert document['format'] == 'zkc.entry/0'
    interface = json.loads(document['interface'])
    assert interface['format'] == 'zkc.language-interface/0'
    assert interface['selection']['kind'] == 'function'
    selected = interface['selection']['function']
    signature, = (f for f in interface['functions'] if f['symbol'] == selected)
    parameters = {p['name']: p['schema'] for p in signature['parameters']}
    return {name: decimal_values(value, parameters.get(name))
            for name, value in arguments.items()}


def invocation_file(journal, name, package, *, session=None, role_services=None,
                    bindings=None):
    """Bind every static child separately from the function's ordinary data."""
    document = json.loads(Path(package).read_text())
    assert document['format'] == 'zkc.entry/0'
    host = json.loads(document['artifact'])
    assert host['format'] == 'zkc.host/0'
    deployments = {}
    for child in host['deployments']:
        operation = child['operation']
        binding = {'operation': operation,
                   'authority': {'format': 'zkc.entry-setups/0', 'keys': {}},
                   'services': {}, 'setups': {}}
        if operation == 'run':
            binding.update(session=session or Path(name).stem,
                           services=role_services or {})
        else:
            assert operation in ('prove', 'verify')
            binding.update(context='', transcript_budget=None)
        deployments[child['id']] = binding
    for identifier, binding in (bindings or {}).items():
        assert identifier in deployments, f'unknown static child: {identifier}'
        deployments[identifier].update(binding)
    path = journal.write(name, {'format': 'zkc.entry-invocations/0',
                                'deployments': deployments})
    return f'--invocations={path}'


def input_files(journal, name, *, public=None, witness=None, arguments=None,
                package=None, session=None, role_services=None, invocations=None,
                services=None, context=None, transcript_budget=None):
    stem = Path(name).stem
    flags = []
    if arguments is not None:
        assert public is None and witness is None
        assert services is None and context is None and transcript_budget is None
        values = argument_values(arguments, package) if package is not None else decimal_values(arguments)
        path = journal.write(f'{stem}.arguments.json', values)
        flags.append(f'--input={path}')
        if package is not None:
            flags.append(invocation_file(journal, f'{stem}.invocations.json', package,
                                         session=session, role_services=role_services,
                                         bindings=invocations))
        else:
            assert session is None and role_services is None and invocations is None
    else:
        for group, values in [('public', public), ('witness', witness)]:
            if values:
                path = journal.write(f'{stem}.{group}.json', decimal_values(values))
                flags.append(f'--{group}={path}')
        for service, budget in (services or {}).items():
            flags.append(f'--service={service}={budget}')
    if context:
        flags.append(f'--context={context}')
    if transcript_budget is not None:
        flags.append(f'--transcript-budget={transcript_budget}')
    return flags
