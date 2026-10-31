"""Closed physical oracle profiles, separate from optimization candidates."""
from dataclasses import dataclass
from enum import Enum
import json

from .io import require


class OracleProfile(Enum):
    CLEAR = 'clear-table'
    OCTIC_KECCAK = 'fri-keccak256-koala-bear-octic'
    KOALA_POSEIDON = 'fri-poseidon2-16-koala-bear-quartic'
    BABY_POSEIDON = 'fri-poseidon2-16-baby-bear-quartic'
    GOLDILOCKS_POSEIDON = 'fri-poseidon2-8-goldilocks-quadratic'


SCHEMES = {
    OracleProfile.CLEAR: '',
    OracleProfile.OCTIC_KECCAK: 'rows.merkle-keccak256.koala-bear.ext8-binomial3/0',
    OracleProfile.KOALA_POSEIDON: 'rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0',
    OracleProfile.BABY_POSEIDON: 'rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0',
    OracleProfile.GOLDILOCKS_POSEIDON: 'rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0',
}


@dataclass(frozen=True)
class OraclePolicy:
    profile: OracleProfile = OracleProfile.CLEAR

    def __post_init__(self):
        require(isinstance(self.profile, OracleProfile), 'invalid oracle profile')

    def selection(self):
        return {'format': 'zkc.oracle-selection/0',
                'roots': {'kind': 'uniform', 'table': {'scheme': SCHEMES[self.profile],
                          'grouping': 'individual', 'order': 'natural'}},
                'order': 'unrestricted', 'authentication': 'per-query'}

    def flag(self):
        return '--oracle-realization=' + json.dumps(self.selection(), separators=(',', ':'))

    def record(self):
        return {'format': 'zkc.benchmark-oracle-policy/0', 'profile': self.profile.value,
                'selection': self.selection()}


OCTIC_KECCAK = OraclePolicy(OracleProfile.OCTIC_KECCAK)
LIBRARY_POLICIES = {
    'koala-bear': OraclePolicy(OracleProfile.KOALA_POSEIDON),
    'baby-bear': OraclePolicy(OracleProfile.BABY_POSEIDON),
    'goldilocks': OraclePolicy(OracleProfile.GOLDILOCKS_POSEIDON),
}


def read_policy(record):
    require(isinstance(record, dict) and set(record) == {'format', 'profile', 'selection'},
            'invalid oracle policy fields')
    require(isinstance(record['profile'], str) and record['profile'] in {p.value for p in OracleProfile},
            'unknown oracle profile')
    policy = OraclePolicy(OracleProfile(record['profile']))
    require(record == policy.record(), 'oracle policy differs from its exact profile')
    return policy


def workload_policy(family, shape):
    require(isinstance(shape, dict), 'invalid oracle workload dimensions')
    if family in ('fri', 'air', 'machine'):
        require(shape.get('field', 'koala-bear') == 'koala-bear', 'octic oracle workload requires KoalaBear')
        return OCTIC_KECCAK
    if family == 'stark':
        field = shape.get('field', 'koala-bear')
        require(isinstance(field, str) and field in LIBRARY_POLICIES, 'unsupported STARK oracle field')
        configuration = {'koala-bear': 'koala_bear_quartic', 'baby-bear': 'baby_bear_quartic',
                         'goldilocks': 'goldilocks_quadratic'}[field]
        require(shape.get('profile', configuration) == configuration, 'STARK field and configuration must match')
        return LIBRARY_POLICIES[field]
    return OraclePolicy()


def validate_selection(options, policy):
    require(isinstance(options, dict) and options.get('oracle_realization') == policy.selection(),
            'published oracle selection differs from workload policy')


def validate_workload(contract, compilations, *, require_control=True, control_receipts=None):
    policy = read_policy(contract.get('oracle_realization'))
    require(policy == workload_policy(contract['protocol'], contract['dimensions']),
            'oracle profile differs from workload field/family')
    require(isinstance(compilations, list) and compilations, 'missing oracle compilation evidence')
    for compilation in compilations:
        require(compilation.get('oracle_realization') == policy.record(),
                'compilation oracle policy differs from workload contract')
        validate_selection(compilation.get('published_options'), policy)
    if contract['protocol'] == 'fri' and (require_control or 'semantic_control' in contract):
        control = contract.get('semantic_control')
        fields = {'stage', 'code', 'role', 'source_function', 'proof_published'}
        require(isinstance(control, dict) and control.keys() == fields
                and control['stage'] == 'prover' and control['code'] == 'artifact-stopped:Explicit("reject")'
                and control['role'] == 'role00000000' and control['source_function'] == 'fri::padded'
                and control['proof_published'] is False,
                'missing exact FRI prover padding control')
        require(isinstance(control_receipts, list) and len(control_receipts) == 1,
                'missing FRI prover control receipt')
        receipt = control_receipts[0]
        require(isinstance(receipt, dict) and receipt.keys() == fields | {'function', 'report'}
                and {k: receipt[k] for k in fields} == control
                and all(isinstance(receipt[k], str) and receipt[k] for k in ('function', 'report')),
                'invalid FRI prover control receipt')
