"""Maintained library closures leave explicit headroom in source checking budgets."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from project import project_arguments, project_source_format
from tools import compiler, records

ROOT = Path(__file__).resolve().parents[2]
OUT = records()
commands = Commands(OUT)
# The implementation admits 32M charged units per independent allowance. These
# maintained closures must fit half of it. This is a deterministic capacity
# gate, not a timing benchmark or a claim about native preparation costs.
HEADROOM_CEILING = 16_000_000
CASES = [
    ('schnorr', 'examples/projects/schnorr', 'example::Proof'),
    ('sumcheck', 'examples/projects/sumcheck', 'example::Proof'),
    ('gkr', 'examples/projects/gkr', 'example::Proof'),
    ('fri', 'examples/projects/fri', 'example::Proof'),
    ('stark-clean', 'examples/projects/stark', 'example::CleanProof'),
    ('stark-plonky3', 'examples/projects/stark', 'example::Plonky3Proof'),
    ('accumulator-logup', 'common/tests/fixtures/projects/accumulator-machine',
     'accumulator_machine::ProofLogUp'),
    ('accumulator-product', 'common/tests/fixtures/projects/accumulator-machine',
     'accumulator_machine::ProofProduct'),
    ('logup-rows', 'common/tests/fixtures/projects/logup-rows', 'logup_rows::Inspect'),
]


def check_ledger(ledger):
    assert ledger['total'] == sum(ledger['subphases'].values()), ledger
    assert ledger['subphases']['unscoped'] == 0, ledger
    assert 0 < ledger['total'] <= HEADROOM_CEILING, ledger


def check_observation(observation):
    check_ledger(observation['charged'])
    for budget in observation['separate_budgets']:
        check_ledger(budget['work'])
        assert budget['work']['subphases'][budget['phase']] == budget['work']['total']
    # A parent's charged work includes children; inspect their allowances, do
    # not add them a second time to the parent's total.
    for child in observation.get('children', []):
        check_observation(child)


for name, project, subject in CASES:
    with case(name):
        manifest = ROOT / project / 'zkc.toml'
        report = OUT / f'{name}.json'
        commands.run([compiler, 'language-check',
                      '--source-format=' + project_source_format(manifest),
                      '--subject=' + subject, f'--diagnostics={report}',
                      *project_arguments(manifest)])
        observation = json.loads(report.read_text())
        assert observation['completed'], observation
        work = observation['source_work']
        assert work['check_completed'] and work['closure'] is not None
        check_observation(work['check'])
        check_observation(work['closure'])

counted()
