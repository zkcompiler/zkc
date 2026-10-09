"""Changing numeric shapes compose with structured proof messages and attempts."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
source = Path(__file__).parent / 'fixtures/mathematical/composed-state.mlir'
suites = ['merlin3.bls12-381.fr64be/1', 'spongefish0.7.4.keccak.bls12-381.fr64be/1']
manifest = []
for family in ['fold', 'batch']:
    for suite_index, suite in enumerate(suites):
        policy = ['zkc.native-proof-policy', family, 'P', 'V', '0', suite,
                  '5', ['0', '1', '2'], [['draw', 'challenge']]]
        for mode, options in [('normal', []), ('plain', ['--no-simplify']),
                              ('release', ['--release-storage']),
                              ('plain_release', ['--no-simplify', '--release-storage'])]:
            name = f'{family}_{suite_index}_{mode}'
            with case(name):
                pol = OUT / f'{name}.policy'
                pol.write_text(json.dumps(policy))
                deployment = commands.run([compiler, 'protocol-proof', source, pol, *options])
                (OUT / f'{name}.deployment').write_text(deployment)
                envelope = json.loads(deployment)
                # Count remains an input and the body remains a single loop in
                # each participant. No host-sized specialization is generated.
                carrier = json.loads(envelope[4])
                assert carrier[0] == 'zkc.program'
                def loops(value):
                    if not isinstance(value, list):
                        return []
                    return ([value] if value and value[0] == 'loop' else []) + [
                        loop for item in value for loop in loops(item)]
                repeat = loops(carrier)
                assert len(repeat) == 2, len(repeat)
                assert all(loop[2][0] == 'value' for loop in repeat)
                if suite_index == 0:
                    (OUT / f'{family}_{mode}.bundle').write_text(commands.run([
                        compiler, 'protocol-bundle', source, f'--entry={family}', *options]))
                manifest.append(dict(name=name, family=family, suite=suite_index, mode=mode))
(OUT / 'manifest.json').write_text(json.dumps(manifest))
counted()
