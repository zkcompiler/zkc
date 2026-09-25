// Source families specialize into ordinary named protocols. No runtime
// protocol polymorphism or cryptographic security claim is implied.
module {
  const ROUNDS: index = BASE * 2;
  const BASE: index = 2;

  fn Double<F: Field>(x: F::Element) -> F::Element {
    let y = field::add::<F>(x, x);
    return y;
  }

  protocol Repeated<F: Field> requires (CommRing(F)) {
    roles (P);
    inputs (P x: F::Element);
    outputs (P F::Element);
    loop [rounds] ROUNDS carry (v = x) -> (answer) {
      local [double] P: let next = Double::<F>(v);
      yield next;
    }
    return answer;
  }

  configure Koala = Repeated(F = koala-bear);
  configure Scalar = Repeated(F = bls12-381.fr);

  instance Small: Koala { roles (P = Prover); }
  instance Curve: Scalar { roles (P = Prover); }
  entry small = Small;
  entry curve = Curve;
}
