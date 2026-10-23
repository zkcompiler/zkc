"""One generic AIR/FRI argument across independently selected field profiles.

The integer recurrence is independent of native arithmetic. These are bounded
execution and rejection controls, not a soundness or external-system claim.
"""
import pytest

from test_stark_library import Package, frames, generated, quadratic_air, replace_frame

PROFILES = [
    ('baby_bear_quartic', 'baby-bear', 2013265921,
     'merlin3.baby-bear.ext4-binomial11.rejection31le/0', 94, 4),
    ('goldilocks_quadratic', 'goldilocks', 18446744069414584321,
     'merlin3.goldilocks.ext2-binomial7.rejection64le/0', 100, 8),
]


@pytest.mark.parametrize('profile,field,modulus,suite,vector_tag,word_bytes', PROFILES)
@pytest.mark.parametrize('flags,final', [([], 0), (['--release-storage'], 0),
                                         (['--no-simplify'], 1)])
def test_same_air_runs_with_explicit_field_and_hash_profile(
        toolchain, journal, directory, profile, field, modulus, suite, vector_tag,
        word_bytes, flags, final):
    bundle, public_data, trace = quadratic_air(16, 2, field=field, modulus=modulus)
    asset = journal.write('air.json', bundle)
    source = (generated(16, final, 1, 8)
              .replace('stark::configurations::koala_bear_octic::{Base, Extension}',
                       f'stark::configurations::{profile}::{{Base, Extension}}')
              .replace('stark::configurations::koala_bear_quartic::{Poseidon2}',
                       f'stark::configurations::{profile}::{{Poseidon2}}')
              .replace('merlin3.koala-bear.ext8-binomial3.rejection31le/0', suite))
    package = Package.source(toolchain, journal, directory, source, {'trace': asset},
                             flags=flags, modules=(f'arguments/stark/configurations/{profile}',))
    public, witness = {'public_data': public_data}, {'trace': trace}
    produced = []
    for workers in [1, 4]:
        report, proof = package.prove(public, witness, threads=workers)
        assert report['status'] == 'produced'
        assert package.verify(public, proof, threads=workers)['status'] == 'accepted'
        produced.append(proof.read_bytes())
    # Fiat-Shamir uses the same statement, messages and exact suite at both
    # worker counts. Scheduling must not alter challenges or proof bytes.
    assert produced[0] == produced[1]
    messages = frames(produced[0])
    position = next(i for i, message in enumerate(messages) if message[5] == vector_tag)
    message = bytearray(messages[position])
    word = int.from_bytes(message[10:10 + word_bytes], 'little')
    message[10:10 + word_bytes] = ((word + 1) % modulus).to_bytes(word_bytes, 'little')
    malformed = directory / 'changed-claim.proof'
    malformed.write_bytes(replace_frame(produced[0], position, message))
    assert package.verify(public, malformed, refuses=True)['status'] != 'accepted'
    changed = {'public_data': [str((int(public_data[0]) + 1) % modulus), *public_data[1:]]}
    for workers in [1, 4]:
        package.prove(changed, witness, threads=workers, refuses='artifact-stopped')
        package.verify(changed, proof, threads=workers, refuses='proof-header')
