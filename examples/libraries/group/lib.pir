// Selected group/scalar equations and affine random-state threading.
module {
  library(namespace="zkc.examples", name="group", version="1", resolution="source-v1");
  pub interface GroupAPI {
    domain G: group;
    domain F: field = G::Scalar;
    local draw(coins: rng<F>) -> (field<F>, rng<F>) effects (local);
    local public_value(secret: field<F>) -> group<G> effects (local);
    local check(point: group<G>, secret: field<F>) -> bool effects (local);
  }
  pub component BlsGroup: GroupAPI {
    domain G: group = "bls12-381.g1";
    domain F: field = "bls12-381.fr";
    local draw(coins: rng<F>) -> (field<F>, rng<F>) effects (local) {
      let (scalar, after) = random::draw::<"bls12-381.fr">(coins);
      return (scalar, after);
    }
    local public_value(secret: field<F>) -> group<G> effects (local) {
      let base = curve::generator::<"bls12-381.g1">();
      return curve::scale::<"bls12-381.g1">(base, secret);
    }
    local check(point: group<G>, secret: field<F>) -> bool effects (local) {
      let base = curve::generator::<"bls12-381.g1">();
      let expected = curve::scale::<"bls12-381.g1">(base, secret);
      let same = curve::equal::<"bls12-381.g1">(point, expected);
      control::require(same);
      return same;
    }
  }
  pub fn Draw<C: GroupAPI>(coins: rng<C::F>) -> (field<C::F>, rng<C::F>) effects (local) {
    return C::draw(coins);
  }
  pub fn Public<C: GroupAPI>(secret: field<C::F>) -> group<C::G> effects (local) {
    return C::public_value(secret);
  }
  pub fn Check<C: GroupAPI>(point: group<C::G>, secret: field<C::F>) -> bool effects (local) {
    return C::check(point, secret);
  }
}
