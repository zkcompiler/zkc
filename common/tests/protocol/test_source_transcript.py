"""Source-authored byte transcripts retain exact values and ordered failures.

The frozen vector is from Spongefish 0.7.4, arkworks 0.6, BLS12-381 G1,
SHAKE128, protocol "schnorr proof", session "spongefish examples", secret 7
and typed nonce 11. Both native framing and raw external proofs use the CLI.
"""
from pathlib import Path

import pytest
from source_modules import library_modules

ROOT = Path(__file__).resolve().parents[3]
SOURCE = '''module sample;
use zkc::bytes::{Bytes};
use spongefish::schnorr as schnorr;
domain G=group("bls12-381.g1");
protocol Fixed roles(P,V)
    (tag:Bytes@(P,V),session:Bytes@(P,V),base:G@(P,V),point:G@(P,V),
     scalar:G::Scalar@P,nonce:G::Scalar@P)->(accepted:bool@V) {
  let proof@P=schnorr::produce(tag,session,base,point,scalar,nonce);
  let actual=send P->V(proof);
  let accepted@V=schnorr::verify(tag,session,base,point,actual);
  return(accepted=accepted);
}
proof Demo=Fixed {
  prover P;verifier V;public{tag,session,base,point};accept accepted;
  construction authored;
}
'''
VECTOR = bytes.fromhex(
    '80fd75ebcc0a21649e3177bcce15426da0e4f25d6828fbf4038d4d7ed3bd4421'
    'de3ef61d70f794687b12b2d571971a5507859bf81b92da0eb8accebb822293ad'
    '013c05507925f6c9cc280f9155853a7e')
PUBLIC = {
    'tag': list(b'schnorr proof'), 'session': list(b'spongefish examples'),
    'base': {'bytes': '97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb'},
    'point': {'bytes': 'b928f3beb93519eecf0145da903b40a4c97dca00b21f12ac0df3be9116ef2ef27b2ae6bcd4c5bc2d54ef5a70627efcb7'},
}


@pytest.mark.parametrize('raw', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage', '--fuse-vector-reductions']])
def test_source_transcript_vector_and_decode_effect_order(toolchain, journal, directory, flags, raw):
    source = directory / 'main.zkc'
    text = SOURCE
    if raw:
        text = text.replace('construction authored;', 'construction ExternalWire;')
        text += 'construction ExternalWire for Fixed {base authored;format RawBytes;}\n'
    source.write_text(text)
    modules = {'sample': source, 'spongefish': ROOT / 'libraries/spongefish/lib.zkc',
               'spongefish::schnorr': ROOT / 'libraries/spongefish/schnorr.zkc'}
    modules.update({f'zkc::{name}': ROOT / f'libraries/zkc/{name}.zkc'
                    for name in ['bytes', 'shake128', 'encoding']})
    package = directory / 'proof.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile',
                           f'--compiler={toolchain.compiler}',
                           *library_modules('spongefish', 'sumcheck', overrides=modules),
                           'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', PUBLIC)
    witness = journal.write('witness.json', {'scalar': '7', 'nonce': '11'})
    args = [f'--package={package}', f'--sha256={report["package_sha256"]}',
            f'--public={public}', '--allow-authored']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    framed = proof.read_bytes()
    size = 80 if raw else 138
    assert len(framed) == size and framed[-80:] == VECTOR
    assert produced['binding_scope'] == ('authored' if raw else 'header')
    assert produced['execution']['external_work'] == 841
    accepted = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert accepted['status'] == 'accepted'
    assert accepted['execution']['external_work'] == 841  # Includes final response observation.
    assert not accepted['execution']['cleanup_errors']

    # The selected format never follows a header found (or absent) in the proof.
    if not flags:
        other = directory / 'other-format.bin'
        other.write_bytes(b'ZKCPRF00' + bytes(32) + (90).to_bytes(8, 'little') + VECTOR
                          if raw else VECTOR)
        journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={other}'],
                     refuses='artifact-stopped' if raw else 'proof-header')

    invalid_point = bytes([255]) * 48 + VECTOR[48:]
    modulus = int('73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001', 16)
    invalid_scalar = VECTOR[:48] + modulus.to_bytes(32, 'big')
    wrong_response = VECTOR[:48] + bytes(32)
    for name, payload, work in [('point', invalid_point, 563),
                                 ('scalar', invalid_scalar, 807),
                                 ('response', wrong_response, 841)]:
        candidate = directory / f'{name}.bin'
        candidate.write_bytes(framed[:-80] + payload)
        rejected = journal.json([toolchain.runtime, '--json', 'verify', *args,
                                 f'--proof={candidate}'], refuses='artifact-stopped')
        assert rejected['execution']['external_work'] == work
        assert rejected['execution']['bytes'] == size
        assert not rejected['execution']['cleanup_errors']

    # The unused final absorb is an ordered transition and must still stop.
    stopped = journal.json([toolchain.runtime, '--json', 'prove', *args,
                            f'--witness={witness}', f'--output={directory / "limited.bin"}',
                            '--external-work=807'], refuses='exhausted:external-work-limit')
    assert stopped['execution']['external_work'] == 807
    assert not (directory / 'limited.bin').exists()
    assert not stopped['execution']['cleanup_errors']
    if raw:
        oracle = toolchain.driver('spongefish_schnorr')
        reference = directory / 'reference'
        vectors = journal.json([oracle, 'export', reference])
        assert vectors['vectors'][1]['bytes'] == 80
        assert (reference / 'fixed.bin').read_bytes() == framed
        assert journal.json([oracle, 'verify', proof])['accepted']
        upstream = journal.json([toolchain.runtime, '--json', 'verify', *args,
                                 f'--proof={reference / "reference.bin"}'])
        assert upstream['status'] == 'accepted'
        for name, payload in [('truncated', VECTOR[:-1]), ('trailing', VECTOR + b'\0')]:
            candidate = directory / f'{name}.bin'
            candidate.write_bytes(payload)
            assert not journal.json([oracle, 'verify', candidate])['accepted']
            code = 'refused:bytes-bounds' if name == 'truncated' else 'artifact-stopped'
            rejected = journal.json([toolchain.runtime, '--json', 'verify', *args,
                                     f'--proof={candidate}'], refuses=code)
            assert rejected['execution']['bytes'] == len(payload)
            assert not rejected['execution']['cleanup_errors']


@pytest.mark.parametrize('kind,body', [
    ('bool', 'let actual=send P->V(value);'),
    ('Data', ''),
    ('Data', 'let actual=send P->V(value);let more=send P->V(value);'),
    ('Data', 'for _ in 0..count roles(P,V) max 2 {let actual=send P->V(value);}'),
])
def test_raw_format_refuses_non_byte_or_repeated_messages(toolchain, journal, directory, kind, body):
    source = directory / 'main.zkc'
    source.write_text(f'''module sample;
    type Data=builtin("bytes");
    protocol Transfer roles(P,V)(value:{kind}@P,count:index@(P,V))->(ok:bool@V) {{
      {body}
      return(ok=true);
    }}
    construction ExternalWire for Transfer {{base authored;format RawBytes;}}
    proof Demo=Transfer {{prover P;verifier V;public{{count}};accept ok;construction ExternalWire;}}
    ''')
    journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                 f'--module=sample={source}', 'sample::Demo', f'--output={directory / "bad.zkpkg"}'],
                refuses='native-proof-format')


def test_random_source_prover_and_external_verifier(toolchain, journal, directory):
    project = ROOT / 'common/tests/fixtures/projects/spongefish-schnorr'
    proof = directory / 'proof.bin'
    common = [f'--project={project / "zkc.toml"}', f'--compiler={toolchain.compiler}', '--allow-authored']
    produced = journal.json([toolchain.runtime, '--json', 'prove', *common, f'--output={proof}'])
    assert produced['proof_bytes'] == 80
    assert journal.json([toolchain.driver('spongefish_schnorr'), 'verify', proof])['accepted']
    assert journal.json([toolchain.runtime, '--json', 'verify', *common, f'--proof={proof}'])['status'] == 'accepted'
    wrong = dict(PUBLIC, point=PUBLIC['base'])
    public = journal.write('wrong.json', wrong)
    rejected = journal.json([toolchain.runtime, '--json', 'verify', *common, f'--proof={proof}',
                             f'--public={public}'], refuses='artifact-stopped')
    assert rejected['execution']['external_work'] == 841
    assert not rejected['execution']['cleanup_errors']


def test_private_snapshot_containers_and_byte_relation_metadata(toolchain, journal, directory):
    source = directory / 'main.zkc'
    source.write_text('''module sample;
    type Bytes=builtin("bytes");
    type State=builtin("shake128_state");
    type States=builtin("sequence",State);
    struct Wrapped { state:State }
    relation Claim(statement payload:Bytes)=opaque("example.bytes/0","claim","0");
    fn snapshot()->States {
      let wrapped=Wrapped{state:kernel("shake128.init")};
      let empty=kernel<State>("sequence.empty");
      return kernel<State>("sequence.append",empty,wrapped.state);
    }
    fn verify(payload:Bytes)->bool {
      let states=snapshot();
      let state=kernel<State>("sequence.at",states,0);
      let next=kernel("shake128.absorb",state,payload);
      let (_,digest)=kernel("shake128.squeeze",next,32);
      return kernel("bytes.length",digest)==32;
    }
    protocol Transfer roles(P,V)(payload:Bytes@P)->(actual:Bytes@V,ok:bool@V)
      spec{target content=Claim(out.actual) accept out.ok;} {
      let actual=send P->V(payload);
      let ok@V=verify(actual);
      return(actual=actual,ok=ok);
    }
    proof Demo=Transfer {prover P;verifier V;public{};accept ok;construction authored;}
    ''')
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile',
                             f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                             'sample::Demo', f'--output={package}'])
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', '--allow-authored']
    witness = journal.write('witness.json', {'payload': [1, 2, 255]})
    proof = directory / 'proof.bin'
    journal.json([toolchain.runtime, '--json', 'prove', *args,
                  f'--witness={witness}', f'--output={proof}'])
    assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                          f'--proof={proof}'])['status'] == 'accepted'
