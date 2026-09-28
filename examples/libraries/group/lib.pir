// Selected group/scalar equations and affine random-state threading.
use zkc::random::{
  Rng
};
use zkc::core;
use zkc::curve;
use zkc::random;
library(namespace = "zkc.examples", name = "group", version = "1", resolution = "source-v1");
pub interface GroupAPI {
  domain G: group;
  domain F: field = G::Scalar;
  local draw(coins: Rng<F>) -> (F::Element, Rng<F>) effects(local);
  local public_value(secret: F::Element) -> G::Element effects(local);
  local check(point: G::Element, secret: F::Element) -> bool effects(local);
}
pub component BlsGroup: GroupAPI {
  domain G: group = "bls12-381.g1";
  domain F: field = "bls12-381.fr";
  local draw(coins: Rng<F>) -> (F::Element, Rng<F>) effects(local) {
    let (scalar, after) = zkc::random::draw::<"bls12-381.fr">(coins);
    return (scalar, after);
  }
  local public_value(secret: F::Element) -> G::Element effects(local) {
    let base = zkc::curve::generator::<"bls12-381.g1">();
    return zkc::curve::scale::<"bls12-381.g1">(base, secret);
  }
  local check(point: G::Element, secret: F::Element) -> bool effects(local) {
    let base = zkc::curve::generator::<"bls12-381.g1">();
    let expected = zkc::curve::scale::<"bls12-381.g1">(base, secret);
    let same = zkc::curve::equal::<"bls12-381.g1">(point, expected);
    zkc::core::require(same);
    return same;
  }
}
pub fn Draw<C: GroupAPI>(coins: Rng<C::F>) -> (C::F::Element, Rng<C::F>) effects(local) {
  return C::draw(coins);
}
pub fn Public<C: GroupAPI>(secret: C::F::Element) -> C::G::Element effects(local) {
  return C::public_value(secret);
}
pub fn Check<C: GroupAPI>(point: C::G::Element, secret: C::F::Element) -> bool effects(local) {
  return C::check(point, secret);
}
