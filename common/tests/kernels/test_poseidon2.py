"""Width-16 Poseidon2 through source, IR and Host.

The expected state is Plonky3 0.8.0's published answer for its default
KoalaBear constants (p3-koala-bear src/poseidon2.rs); batching is compared
with separate single-state calls. Native generic and integer differentials
live with the backend tests.
"""
import pytest

from entry import Entry
from source_modules import core_packages, library_modules

INPUT = [894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
         120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443,
         227047920, 1783754913]
EXPECTED = [1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747,
            351743874, 1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461,
            748270449, 651545025]

SOURCE = '''module sample;
use zkc::permutation as permutation;
use zkc::vector as vector;
use zkc::vector::{Vector};
domain F=field("koala-bear");
fn check(states:Vector<F>, count:index) -> (Vector<F>,bool) {
  let all=permutation::poseidon2_16(states);
  let mut same=true;
  for i in 0..count {
    let one=permutation::poseidon2_16(vector::slice(states,i*16,16));
    same=same && vector::equal(one,vector::slice(all,i*16,16));
  }
  return (all,same);
}
protocol Run roles(P)(states:Vector<F>@P, count:index@P) -> (result:(Vector<F>,bool)@P) {
  let result @P=check(states,count);
  return (result=result);
}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_poseidon2_width16(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, SOURCE, (*library_modules(*core_packages()), *flags))
    other = list(range(16))
    states, same = entry.run('batch', {'states': INPUT + other + INPUT, 'count': 3})['result']
    assert same is True
    assert states[:16] == [str(x) for x in EXPECTED]
    assert states[32:] == [str(x) for x in EXPECTED]
    assert states[16:32] != [str(x) for x in other]
    empty, same = entry.run('empty', {'states': [], 'count': 0})['result']
    assert (empty, same) == ([], True)
    entry.run('partial-state', {'states': INPUT[:15], 'count': 0}, refuses='poseidon2-width')
