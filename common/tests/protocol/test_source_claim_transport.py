"""Bind genuine native claim exports through the formal bridge transport."""
import json
from pathlib import Path

import pytest

from harness import load


@pytest.mark.parametrize('proof', [False, True])
def test_native_claim_admission_shape(toolchain, journal, directory, proof):
    bridge = load('native_source_claim_transport', 'lean/bridges/pipeline/source_claims.py')
    root = Path(__file__).resolve().parents[3]
    parser_fixture = root / 'compiler/test/fixtures/source-claims/sumcheck.zkc'
    # Native proof construction requires each verifier draw to be delivered.
    # The parser fixture deliberately does not impose that deployment profile.
    fixture = directory / 'claims.zkc'
    fixture.write_text(parser_fixture.read_text().replace(
        'let accepted@V=message+challenge==claimed+challenge;',
        'let delivered=send V->P(challenge);\n'
        '  let accepted@V=message+challenge==claimed+challenge;'))
    entry = 'claims::Demo' if proof else 'claims::Sumcheck'
    selector = '--entry=' if proof else '--subject='
    flags = ['--source-format=zkc', selector + entry, f'--module=claims={fixture}']
    source = journal.run([toolchain.compiler, 'language-emit', *flags])
    path = directory / 'original.mlir'
    path.write_text(source)
    interface_text = journal.run([toolchain.compiler, 'language-interface', *flags])
    interface = json.loads(interface_text)
    export = journal.json([toolchain.compiler, 'language-check', *flags,
                           '--source-claims'])['source_claims']
    original = journal.run([toolchain.compiler, 'protocol-structured', path,
                            f'--symbol={interface["protocol"]}'])
    participant = program = None
    if proof:
        bundle = journal.json([toolchain.compiler, 'language-bundle', *flags])
        policy = journal.write('policy.json', bundle[2][1])
        candidate = directory / 'candidate.mlir'
        candidate.write_text(journal.run([toolchain.compiler, 'protocol-construct-proof', path, policy]))
        participant = journal.run([toolchain.compiler, 'protocol-constructed-participant',
                                   path, policy, candidate])
        program = bundle[4].encode()
    bound = bridge.bind_export(export, entry=interface['entry'], source=source.encode(),
        interface_text=interface_text, original_text=original,
        participant_text=participant, program=program)
    assert len(bound['claims']) == (2 if proof else 0)
    assert all(claim['resolution'] == 'pending-lean' for claim in bound['claims'])
    assert set(export['admission']) == {'format', 'original_sha256', 'interface_sha256',
                                       'protocol_symbol', 'capture', 'installation'}
    assert 'original_identity' not in export['admission']
