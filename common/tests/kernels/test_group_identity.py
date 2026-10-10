"""Source mathematical identity through checked Algebra lowering and native Host."""
import json

import pytest

from entry import Entry
from toolchain import ROOT


@pytest.mark.parametrize('group', [
    'ristretto255.group', 'bls12-381.g1', 'bn254.g1', 'bn254.g2', 'bn254.gt',
])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_group_identity(toolchain, journal, directory, group, flags):
    empty = '' if group == 'bn254.gt' else '''
      let scalars=kernel<G::Scalar>("vector.empty");
      let points=kernel<G>("curve.empty");
      let sum=kernel<G>("curve.msm",scalars,points);
      require sum==z;
    '''
    source = f'''module sample;
    use zkc::curve as curve;
    domain G=group("{group}");
    math fn zero()->G{{return intrinsic<G>("curve.identity");}}
    fn check()->bool{{
      let z=zero();
      let library_zero=curve::identity<G>();
      let native_zero=kernel<G>("curve.identity");
      let g=kernel<G>("curve.generator");
      require z==library_zero;
      require z==native_zero;
      require z+g==g;
      require g+z==g;
      require g*0==z;
      require z*7==z;
      require !kernel<G>("curve.nonidentity",z);
      require kernel<G>("curve.nonidentity",g);
      {empty}
      return true;
    }}
    protocol Run roles(P)()->(ok:bool@P){{let ok @P=check();return(ok=ok);}}
    run Demo=Run;
    '''
    library = f'--module=zkc::curve={ROOT / "libraries/zkc/curve.zkc"}'
    entry = Entry(toolchain, journal, directory, source, (*flags, library))
    package = json.loads(entry.package.read_text())
    assert 'algebra.group_identity' in package['original']
    assert 'curve.identity' in package['artifact']
    result = entry.run('identity', {})
    assert result['ok'] is True, result
