"""Source mathematical identity through checked Algebra lowering and native Host."""

from source_modules import core_packages, library_modules
import json

import pytest

from entry import Entry, joint_package, joint_artifact


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
    run Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
    '''
    libraries = library_modules(*core_packages())
    entry = Entry(toolchain, journal, directory, source, (*flags, *libraries))
    package = json.loads(entry.package.read_text())
    assert 'algebra.group_identity' in joint_package(package)['original']
    assert 'curve.identity' in joint_artifact(package)['candidate']
    result = entry.run('identity', {})
    assert result['ok'] is True, result


@pytest.mark.parametrize('group', ['ristretto255.group', 'bn254.g1', 'bls12-381.g1'])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_curve_bulk_api(toolchain, journal, directory, group, flags):
    source = f'''module sample;
    use zkc::curve as curve;
    use zkc::vector as vec;
    use zkc::scalar as scalar;
    domain G=group("{group}");
    fn check(malformed:bool)->bool{{
      let g=curve::generator<G>();
      let points=curve::append(curve::append(curve::empty<G>(),g),g*2);
      let scalars=vec::append(vec::append(vec::empty<G::Scalar>(),3),5);
      let chosen=if malformed {{vec::empty<G::Scalar>()}} else {{scalars}};
      let result=curve::msm(chosen,points);
      require result==g*13;
      let scaled=curve::scale_each(scalars,points);
      require curve::get(scaled,0)==g*3;
      require curve::get(scaled,1)==g*10;
      let combined=points + scaled * 2;
      require curve::get(combined,0)==g*7;
      require curve::get(combined,1)==g*22;
      let halves=curve::split(combined);
      require curve::length(curve::concat(halves.0,halves.1))==2;
      require scalar::from_index<G::Scalar>(17)==17;
      return true;
    }}
    protocol Run roles(P)(malformed:bool@P)->(ok:bool@P){{return check(malformed);}}
    run Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
    '''
    libraries = library_modules(*core_packages())
    entry = Entry(toolchain, journal, directory, source, (*flags, *libraries))
    assert entry.run('bulk', {'malformed': False})['ok'] is True
    entry.run('mismatched-lengths', {'malformed': True}, refuses=True)
