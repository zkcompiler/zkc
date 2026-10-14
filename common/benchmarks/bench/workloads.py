"""Maintained workload definitions. No scheduling, timing or statistics here."""
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Callable

from .io import require


def schnorr_inputs(root, size, capture):
    inputs = root / 'examples/projects/schnorr/spongefish/inputs/example.Proof'
    for name in ('public.json', 'witness.json'):
        capture.add(inputs / name, Path('inputs/schnorr') / name)
    public = json.loads((inputs / 'public.json').read_text())
    witness = json.loads((inputs / 'witness.json').read_text())
    return public, witness, public | {'point': public['base']}


def monero_inputs(root, size, capture):
    path = root / 'common/tests/fixtures/bulletproofs-plus/corpus.json'
    capture.add(path, 'inputs/monero-corpus.json')
    corpus = json.loads(path.read_text())
    cases = {c['name']: c for c in corpus['cases']}
    require(f'{size}-mixed' in cases and f'{size}-max' in cases, 'Monero corpus is missing required cases')
    case, other = cases[f'{size}-mixed'], cases[f'{size}-max']
    public = {'commitments': list(bytes.fromhex(case['commitments'])), 'rounds': str(6+(size-1).bit_length())}
    witness = {'values': list(map(str, case['values'])), 'masks': case['masks']}
    return public, witness, public | {'commitments': list(bytes.fromhex(other['commitments']))}


def monero_environment(args, root, capture, journal, manifest):
    require(args.monero_source is not None, 'Monero requires --monero-source')
    path = root / 'common/tests/fixtures/bulletproofs-plus/corpus.json'
    capture.add(path, 'inputs/monero-corpus.json')
    revision = json.loads(path.read_text())['revision']
    source = args.monero_source.resolve()
    record = journal.command(['git', '-C', source, 'rev-parse', 'HEAD'], cwd=source)
    require(Path(record['stdout']).read_text().strip() == revision, 'Monero source revision mismatch')
    record = journal.command(['git', '-C', source, 'status', '--porcelain', '--untracked-files=all'], cwd=source)
    require(not Path(record['stdout']).read_bytes(), 'modified Monero sources')
    manifest.setdefault('references', {})['monero'] = {'source': str(source), 'revision': revision}


def sumcheck_inputs(root, size, capture):
    values = [str((i*i+17*i+3) % 65521) for i in range(size)]
    public = {'values': values, 'claim': str(sum(map(int, values))), 'rounds': str(size.bit_length()-1),
              'tag': list(b'zkc sumcheck'), 'session': list(b'benchmark')}
    return public, {}, public | {'claim': str(int(public['claim'])+1)}


@dataclass(frozen=True)
class Protocol:
    name: str
    project: str
    sizes: tuple
    field: str
    transcript: str
    encoding: str
    inputs: Callable
    randomized: bool = True
    witness: bool = True
    reference_tool: str = 'worker'
    environment: Callable | None = None
    verification: str = 'single proof'
    notes: tuple = ()

    def case_name(self, size):
        return self.name if self.sizes == (1,) else f'{self.name}-{size}'


PROTOCOLS = (
    Protocol('schnorr', 'examples/projects/schnorr/spongefish', (1,),
             'bls12-381.g1/fr', 'spongefish-0.7.4-shake128', 'g1-48/fr-be-32', schnorr_inputs),
    Protocol('monero', 'examples/projects/bulletproofs-plus', (1, 2, 4, 8, 16),
             'edwards25519', 'monero-bulletproofs-plus', 'monero-binary-archive', monero_inputs,
             reference_tool='monero', environment=monero_environment,
             notes=('Retained conformance amounts and small fixture masks; not a sampled wallet workload.',
                    'Upstream PROVE derives commitments inside the timer.',
                    'Upstream generator and multiexponentiation precomputation persists within each process; first-call timing includes initialization.')),
    Protocol('sumcheck', 'common/benchmarks/projects/sumcheck', (16, 64, 256, 1024, 4096),
             'bls12-381.fr', 'spongefish-0.7.4-shake128', 'round-pairs-fr-be-32', sumcheck_inputs,
             randomized=False, witness=False, verification='public-table terminal evaluation is included',
             notes=('Both calls bind the complete ordered table: O(n) transcript work.',
                    'Both implementations encode and absorb the table as one ordered buffer.')),
)


def catalog():
    return [(protocol.case_name(size), protocol, size) for protocol in PROTOCOLS for size in protocol.sizes]
