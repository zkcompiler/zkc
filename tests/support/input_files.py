"""Write explicit Entry input maps and return ordinary CLI options for tests."""
from pathlib import Path


def decimal_values(value):
    """Serialize Python integer inputs using the Entry decimal convention."""
    if type(value) is int:
        return str(value)
    if isinstance(value, list):
        return [decimal_values(v) for v in value]
    if isinstance(value, dict):
        return {k: decimal_values(v) for k, v in value.items()}
    return value


def input_files(journal, name, *, public=None, witness=None, roles=None,
                session=None, services=None, context=None, transcript_budget=None):
    stem = Path(name).stem
    flags = []
    if roles is not None:
        assert public is None and witness is None
        flags.append(f'--session={session or stem}')
        for role, inputs in roles.items():
            if inputs.get('inputs'):
                path = journal.write(f'{stem}.{role}.json', decimal_values(inputs['inputs']))
                flags.append(f'--input={role}={path}')
            for service, budget in inputs.get('services', {}).items():
                flags.append(f'--service={role}.{service}={budget}')
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
