"""Selected deployment forks and common compiler policies cross the EVM driver."""
import json
from pathlib import Path

from cases import case
from commands import Commands
from project import project_arguments
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
ROOT = Path(__file__).resolve().parents[2]
inputs = ['--source-format=zkc', '--entry=example::Proof',
          *project_arguments(ROOT / 'examples/projects/sumcheck-keccak/zkc.toml')]

with case('deployment fork is exact and belongs only to EVM compilation'):
    for value in ('', 'Cancun', 'Prague', 'shanghai', 'latest', 'prague, cancun'):
        commands.run([compiler, 'language-evm', *inputs, f'--evm-version={value}'],
                     refuses='evm.fork')
    commands.run([compiler, 'language-evm', *inputs,
                  '--evm-version=cancun', '--evm-version=prague'], refuses='evm.fork')
    commands.run([compiler, 'language-package', *inputs, '--evm-version=prague'],
                 refuses='evm.fork')

with case('CPU physical and storage selections refuse at the EVM boundary'):
    for option in ('--cpu-target=portable', '--release-storage', '--dump=closed'):
        commands.run([compiler, 'language-evm', *inputs, option], refuses='evm.options')

oracle = {'format': 'zkc.oracle-selection/0', 'roots': {'kind': 'exact', 'entries': []},
          'order': 'after-final-draw', 'authentication': 'per-query'}
flags = ['--no-simplify', '--no-finite-bulk', '--fuse-vector-reductions',
         '--fuse-collect-fold', '--no-calculation-batching',
         '--oracle-realization=' + json.dumps(oracle)]

with case('both deployment forks retain exact source and effective common options'):
    original = commands.run([compiler, 'language-emit', *inputs])
    for fork in ('cancun', 'prague'):
        response = json.loads(commands.run([compiler, 'language-evm', *inputs,
                                            f'--evm-version={fork}', *flags]))
        assert response['fork'] == response['manifest']['fork'] == fork
        assert response['options'] == response['manifest']['options'] == {
            'simplify': False, 'release_storage': False, 'finite_bulk': False,
            'fuse_vector_reductions': True, 'fuse_collect_fold': True,
            'calculation_batching': False, 'oracle_realization': oracle,
            'numerical_expressions': 'prefer-native'}
        assert response['original'] == response['source_sha256']
        assert response['descriptor'][1] == response['policy']
        assert json.loads(response['descriptor'][8]) == oracle
        assert commands.run([compiler, 'language-emit', *inputs]) == original
    default = json.loads(commands.run([compiler, 'language-evm', *inputs]))
    assert default['fork'] == default['manifest']['fork'] == 'cancun'
    assert default['options']['simplify'] is True

with case('authored zero-transcript Entry retains framed common construction'):
    source = OUT / 'authored.zkc'
    source.write_text('''module authored;
domain Fr=field("bls12-381.fr");
protocol Echo roles(P,V)(value:Fr@(P,V))->(accepted:bool@V) {
  let received=send P->V(value);
  let accepted=received==value;
  return(accepted=accepted);
}
proof Proof=Echo{prover P;verifier V;public{value};accept accepted;construction authored;}
''')
    response = json.loads(commands.run([compiler, 'language-evm', '--source-format=zkc',
                                        f'--module=authored={source}', '--entry=authored::Proof']))
    policy = response['policy']
    assert policy[5:7] == ['', []]
    assert policy[8:12] == [[], 'zkc.framed/0', '', []]
    assert response['descriptor'][1] == policy
    assert response['descriptor'][6] == []
