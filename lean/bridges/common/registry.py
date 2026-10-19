"""Maintained semantic contracts and independent property consumers.

Registry entries are reviewed data in the subject manifests' scalar profile. A
request selects entries; it never provides Lean source, tactics, imports or
theorem names. No source hashes occur here.
"""
from dataclasses import dataclass
from pathlib import Path
import sys


@dataclass(frozen=True)
class Property:
    theorem: str
    experiment: str
    premises: tuple[str, ...]
    module: str | None = None
    context: str = ''
    consumer: str | None = None


@dataclass(frozen=True)
class Contract:
    namespace: str
    module: str
    binders: str
    arguments: str
    inputs: dict[str, tuple[str, str]]
    unfold: tuple[str, ...]
    properties: dict[str, Property]
    group: bool = False
    composed: bool = False


PROPERTY_FIELDS = {'theorem', 'experiment', 'premises', 'module', 'context', 'consumer'}


def _contracts():
    """The scalar-profile contracts of the subject manifests (`lean/subjects`).

    Each manifest with the scalar profile names one contract, its inputs and
    the properties a request may select. The manifests are reviewed data; the
    loader refuses unknown fields.
    """
    sys.path.append(str(Path(__file__).resolve().parents[2]))
    from bridges.pipeline import manifest  # noqa: E402

    contracts = {}
    for subject in manifest.load_all():
        if not subject.profile('scalar'):
            continue
        data = subject.table('scalar')
        properties = {}
        for name, value in data.get('properties', {}).items():
            unknown = set(value) - PROPERTY_FIELDS
            if unknown or not {'theorem', 'experiment', 'premises'} <= set(value):
                raise ValueError(f'{subject.name}: malformed scalar property {name}')
            properties[name] = Property(value['theorem'], value['experiment'], tuple(value['premises']),
                                        value.get('module'), value.get('context', ''), value.get('consumer'))
        inputs = {name: tuple(value) for name, value in data.get('inputs', {}).items()}
        if any(len(value) != 2 for value in inputs.values()):
            raise ValueError(f'{subject.name}: scalar inputs are [path, kind] pairs')
        contract = data['contract']
        if contract in contracts:
            raise ValueError(f'duplicate scalar contract {contract}')
        contracts[contract] = Contract(data['namespace'], data['module'], data['binders'], data['arguments'],
                                       inputs, tuple(data.get('unfold', ())), properties,
                                       data.get('group', False), data.get('composed', False))
    return contracts


CONTRACTS = _contracts()
