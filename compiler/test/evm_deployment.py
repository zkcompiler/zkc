"""Selected deployment forks and common compiler policies cross the EVM driver."""
import hashlib
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
DECLARATION_BYTES = (ROOT / 'common/targets/evm.json').read_bytes()
DECLARATION = json.loads(DECLARATION_BYTES)
FORKS = [fork['name'] for fork in DECLARATION['forks']]
IDENTITY = 'zkc.evm-target/0:' + hashlib.sha256(DECLARATION_BYTES).hexdigest()

with case('deployment fork is exact and belongs only to EVM compilation'):
    for value in ('', 'shanghai', 'latest', ', '.join(FORKS),
                  *(name.capitalize() for name in FORKS)):
        commands.run([compiler, 'language-evm', *inputs, f'--evm-version={value}'],
                     refuses='evm.fork')
    commands.run([compiler, 'language-evm', *inputs,
                  f'--evm-version={FORKS[0]}', f'--evm-version={FORKS[-1]}'], refuses='evm.fork')
    commands.run([compiler, 'language-package', *inputs, f'--evm-version={FORKS[-1]}'],
                 refuses='evm.fork')

with case('help names the declared forks and their default'):
    help_text = commands.run([compiler, '--help'])
    assert (f"--evm-version={'|'.join(FORKS)} (default {DECLARATION['default_fork']})"
            in help_text), help_text

with case('CPU physical and storage selections refuse at the EVM boundary'):
    for option in ('--cpu-target=portable', '--release-storage', '--dump=closed'):
        commands.run([compiler, 'language-evm', *inputs, option], refuses='evm.options')

oracle = {'format': 'zkc.oracle-selection/0', 'roots': {'kind': 'exact', 'entries': []},
          'order': 'after-final-draw', 'authentication': 'per-query'}
flags = ['--no-simplify', '--no-finite-bulk', '--fuse-vector-reductions',
         '--fuse-collect-fold', '--no-calculation-batching',
         '--oracle-realization=' + json.dumps(oracle)]

# The one producer's keys. Tool facts (solc, its settings, the ABI) belong to
# the declaration and the SDK; no key is restated in an inner record.
KEYS = {'format', 'declaration', 'fork', 'options', 'limits', 'entry', 'capture',
        'installation', 'original', 'source_format', 'compiler', 'policy', 'descriptor',
        'yul'}

with case('every declared fork retains exact source and effective common options'):
    original = commands.run([compiler, 'language-emit', *inputs])
    for fork in FORKS:
        response = json.loads(commands.run([compiler, 'language-evm', *inputs,
                                            f'--evm-version={fork}', *flags]))
        assert set(response) == KEYS, sorted(response)
        assert response['fork'] == fork
        assert response['declaration'] == IDENTITY
        assert response['options'] == {
            'simplify': False, 'release_storage': False, 'finite_bulk': False,
            'fuse_vector_reductions': True, 'fuse_collect_fold': True,
            'calculation_batching': False, 'oracle_realization': oracle}
        assert response['original'] == hashlib.sha256(original.encode()).hexdigest()
        assert response['descriptor'][1] == response['policy']
        assert json.loads(response['descriptor'][8]) == oracle
        assert commands.run([compiler, 'language-emit', *inputs]) == original
        # The CPU package publishes the same options for the same flags.
        package = json.loads(commands.run([compiler, 'language-package', *inputs, *flags]))
        assert response['options'] == package['options']
    default = json.loads(commands.run([compiler, 'language-evm', *inputs]))
    assert set(default) == KEYS
    assert default['fork'] == DECLARATION['default_fork']
    assert default['declaration'] == IDENTITY
    assert default['limits'] == {row['name']: row['maximum'] for row in DECLARATION['limits']}
    assert default['options']['simplify'] is True
    assert default['options'] == json.loads(
        commands.run([compiler, 'language-package', *inputs]))['options']

with case('the source Entry and the policy entry keep distinct keys'):
    response = json.loads(commands.run([compiler, 'language-evm', *inputs]))
    # The selected source Entry; the policy keeps the protocol's entry symbol.
    assert response['entry'] == 'example::Proof'
    assert response['policy'][1] != response['entry']
    assert response['source_format'] == 'zkc.original-mlir/0'
    # The same identities the checked project reports for the same selection.
    checked = json.loads(commands.run([compiler, 'language-check', *inputs]))
    for key in ('entry', 'capture', 'installation', 'original'):
        assert response[key] == checked[key], key

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

with case('source-selected gates remain native and refuse unsupported EVM construction'):
    source = OUT / 'gated.zkc'
    source.write_text('''module gated;
domain Q=field("koala-bear.ext4-binomial3");
protocol Queries roles(P,V)(coins:Random<Q>@V)->(accepted:bool@V) {
  #[site(positions)] let positions=coins.indices(2,16);
  let delivered=send V->P(positions);
  return true;
}
proof Proof=Queries {
  prover P; verifier V; public{}; accept accepted;
  construction fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",coins);
  gate positions bits 0;
}
''')
    selection = ['--source-format=zkc', f'--module=gated={source}', '--entry=gated::Proof']
    native = json.loads(commands.run([compiler, 'language-package', *selection]))
    policy = json.loads(native['artifact'])[2][1]
    assert len(policy[11]) == 1 and policy[11][0][1] == '0'
    commands.run([compiler, 'language-evm', *selection], refuses='evm.construction')

with case('a Yul export refusal joins the diagnostics captured before it'):
    # Every message site adds its origin template to the static invocation
    # root, so 512 sites exceed the declared root ceiling only at Yul export.
    sites = 512
    sends = ''.join(f'  let r{i}=send P->V(flag);\n' for i in range(sites))
    source = OUT / 'wide-root.zkc'
    source.write_text(f'''module wide;
protocol Echo roles(P,V)(flag:bool@(P,V))->(accepted:bool@V) {{
{sends}  let accepted=r{sites - 1}==flag;
  return(accepted=accepted);
}}
proof Proof=Echo{{prover P;verifier V;public{{flag}};accept accepted;construction authored;}}
''')
    observation = OUT / 'wide-root.json'
    commands.run([compiler, 'language-evm', '--source-format=zkc', f'--module=wide={source}',
                  '--entry=wide::Proof', f'--diagnostics={observation}'], refuses='evm.root-limit')
    diagnostics = json.loads(observation.read_text())['diagnostics']
    assert [d['code'] for d in diagnostics[:2]] == ['evm.yul', 'evm.diagnostics'], diagnostics
    assert '[evm.root-limit]' in diagnostics[1]['message'], diagnostics
