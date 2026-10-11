"""Prover-only cheating against the imported AIR argument, stopped at exact guards.

Each case changes only what the prover computes or commits, so the resulting
proof has its own consistent commitments, folds and transcript, and rejection
has to come from the verifier obligation under test. Guard sites are read from
each variant's own emitted program. These are regression controls for specific
obligations, not a soundness bound.
"""
from pathlib import Path
import re
from typing import NamedTuple


from air_proofs import (EXAMPLE, FIXTURE, ROOT, STARK, TABLE, frames, request)

POLYNOMIAL = ROOT / 'libraries/air/polynomial.zkc'
FRI = ROOT / 'libraries/fri/lib.zkc'
# The guards of TableArgument and of LowDegree in source order, each named by
# its native owner and the number of loops around it, as the FRI tests name theirs.
# Both source rosters are (P,V), so their native owners have ordinals 0 and 1.
TABLE_GUARDS = [('profile', 'role00000001', 0), ('prover_profile', 'role00000000', 0),
                ('identity', 'role00000001', 0), ('fri', 'role00000001', 0),
                ('trace', 'role00000001', 1), ('quotient', 'role00000001', 1),
                ('deep', 'role00000001', 1)]
FRI_GUARDS = [('schedule', 'role00000001', 0), ('input', 'role00000000', 0),
              ('final_degree', 'role00000001', 0), ('low', 'role00000001', 2),
              ('high', 'role00000001', 2), ('chain', 'role00000001', 2),
              ('terminal', 'role00000001', 1)]
GUARD = re.compile(r'"protocol\.guard"\(%\d+(?:#\d+)?\) <\{owner = "(\w+)", site = "(s\d+)"\}>')
APPLY = re.compile(r'"protocol\.apply"\(.*\) <\{callee = @(\w+), roles = \[[^\]]*\], site = "(s\d+)"\}>')
FUNCTION = re.compile(r'"(protocol|local)\.func"\(\) <\{.*sym_name = "(\w+)"')
ORIGIN = re.compile(r'^\}\) \{logical_origin = \["(\w+)", \[\]\]\}')


class Variant(NamedTuple):
    package: Path
    pin: str
    guards: dict  # guard name -> source-site chain from the entry's apply
    functions: dict  # local function origin -> generated symbol


def emitted_sites(emitted):
    """The guard chains of TableArgument and LowDegree, read from the emitted program.

    A verifier stop names the chain of source sites from the entry's apply of
    TableArgument down to the guard, so each guard is keyed by that chain.
    Both protocols must keep the library's guard shape, which also shows that
    a prover-only variant left the verifier's checks in place.
    """
    functions, symbols, regions, current, symbol = {}, {}, [], None, None
    for line in emitted.splitlines():
        text = line.strip()
        header = FUNCTION.search(text)
        if header:
            symbol = header.group(2)
            if header.group(1) == 'protocol':
                current = functions[symbol] = {'guards': [], 'applies': []}
        origin = ORIGIN.match(text)
        if origin:
            symbols[origin.group(1)] = symbol
        guard = GUARD.search(text)
        if guard:
            current['guards'].append((guard.group(1), guard.group(2), regions.count('repeat')))
        applied = APPLY.search(text)
        if applied:
            current['applies'].append(applied.groups())
        if text.endswith('({'):
            regions.append('repeat' if '"protocol.repeat"' in text else 'other')
        elif text.startswith('})'):
            regions.pop()
    assert not regions

    def shaped(callee, expected):
        return ([(owner, depth) for owner, _, depth in functions[callee]['guards']]
                == [(owner, depth) for _, owner, depth in expected])
    (entry,) = [f for f in functions.values() if not f['guards'] and len(f['applies']) == 1]
    ((table, table_site),) = entry['applies']
    assert shaped(table, TABLE_GUARDS)
    ((fri, fri_site),) = [a for a in functions[table]['applies'] if shaped(a[0], FRI_GUARDS)]
    guards = {name: f'{table_site}_{site}' for (name, _, _), (_, site, _)
              in zip(TABLE_GUARDS, functions[table]['guards'], strict=True)}
    guards.update({'fri.' + name: f'{table_site}_{fri_site}_{site}' for (name, _, _), (_, site, _)
                   in zip(FRI_GUARDS, functions[fri]['guards'], strict=True)})
    return guards, symbols


def local_symbol(variant, module, name):
    """The generated symbol of one source function, by its retained origin."""
    expected = 's' + ''.join(f'{len(part.encode())}h{part.encode().hex()}'
                             for part in (module, name))
    (symbol,) = [symbol for origin, symbol in variant.functions.items() if origin == expected]
    return symbol


def rejected(report, guards):
    """The guard at which V stopped, 'name' or 'fri.name', and the loop iterations around it."""
    stop = report['execution']['stop']
    assert report['status'] == 'refused' and stop['role'] == 'role00000001', stop
    assert stop['kind'] == 'Explicit("reject")', stop
    path = stop['origin'][4]
    assert path[-1] == ['if', 'guard_control', 'else'], path
    chain = re.fullmatch(r'(?:apply_\d+_)+((?:s\d+_)*s\d+)', stop['site']).group(1)
    names = {chain: name for name, chain in guards.items()}
    return names[chain], [frame[2] for frame in path if frame[0] == 'loop']


def build(toolchain, journal, directory, name, *, main=None, asset=None, edits=(), appended=()):
    """One package from the example and the libraries, and its guard chains.

    Exact single-hit substitutions and appended helper text are the variant's
    only difference from the shipped sources, so a drifted library fails here
    rather than building something else.
    """
    where = directory / name
    where.mkdir()
    texts = {'air_stark_example': EXAMPLE.read_text() if main is None else main,
             'air_stark': STARK.read_text(), 'air_table': TABLE.read_text(),
             'air_polynomial': POLYNOMIAL.read_text(), 'fri': FRI.read_text()}
    for module, old, new in edits:
        assert texts[module].count(old) == 1, (module, old)
        texts[module] = texts[module].replace(old, new)
    for module, extra in appended:
        texts[module] += '\n' + extra
    arguments = []
    for module, text in texts.items():
        path = where / f'{module}.zkc'
        path.write_text(text)
        arguments.append(f'--module={module}={path}')
    label, bundle = asset or ('recurrence', FIXTURE / 'bundle.json')
    arguments.append(f'--asset={label}=relation-bundle-json={bundle}')
    package = where / 'Proof.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           *arguments, 'air_stark_example::Proof', f'--output={package}'])
    emitted = journal.run([toolchain.compiler, 'language-emit', '--source-format=zkc',
                           '--entry=air_stark_example::Proof', *arguments])
    return Variant(package, report['package_sha256'], *emitted_sites(emitted))


def prove(toolchain, journal, variant, name, public, private):
    """A proof the variant's prover must produce, with the honest message count."""
    label = f'{variant.package.parent.name}-{name}'
    producer = request(journal, label + '-producer', public, private)
    proof = variant.package.with_name(name + '.bin')
    made = journal.json([toolchain.runtime, '--json', 'prove', f'--package={variant.package}', f'--sha256={variant.pin}', *producer, f'--output={proof}'])
    assert made['status'] == 'produced'
    assert len(frames(proof.read_bytes())) == 8 + 16 * public['query_count']
    return proof


def verify(toolchain, journal, variant, name, public, proof, *, refuses=None):
    label = f'{variant.package.parent.name}-{name}'
    verifier = request(journal, label + '-verifier', public)
    return journal.json([toolchain.runtime, '--json', 'verify', f'--package={variant.package}', f'--sha256={variant.pin}', *verifier, f'--proof={proof}'],
                        refuses=refuses)
