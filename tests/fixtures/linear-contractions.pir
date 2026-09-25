module {
  bind mul = vector::mul(bls12-381.fr);
  bind dot = vector::dot(bls12-381.fr);
  bind scale = curve::scale_each(ristretto255.group);
  bind msm = curve::msm(ristretto255.group);
  fn Dot(
    w: Vector<"bls12-381.fr"::Element>,
    factors: Vector<"bls12-381.fr"::Element>,
    values: Vector<"bls12-381.fr"::Element>
  ) -> "bls12-381.fr"::Element {
    [multiply] let mapped = mul(factors, values);
    [contract] let result = dot(w, mapped);
    return result;
  }

  fn MSM(
    w: Vector<"ristretto255.scalar"::Element>,
    factors: Vector<"ristretto255.scalar"::Element>,
    values: Vector<"ristretto255.group"::Element>
  ) -> "ristretto255.group"::Element {
    [scale] let mapped = scale(factors, values);
    [contract] let result = msm(w, mapped);
    return result;
  }

  // Deliberately shares the producer binding with Dot. Escaping results must
  // remain dense when the pair in Dot receives an independent physical choice.
  fn Dense(factors: Vector<"bls12-381.fr"::Element>, values: Vector<"bls12-381.fr"::Element>) -> Vector<"bls12-381.fr"::Element> {
    [multiply] let mapped = mul(factors, values);
    return mapped;
  }

  protocol Main {
    roles (P, V);
    inputs (
      P w: Vector<"bls12-381.fr"::Element>,
      P a: Vector<"bls12-381.fr"::Element>,
      P v: Vector<"bls12-381.fr"::Element>,
      P r: Vector<"ristretto255.scalar"::Element>,
      P b: Vector<"ristretto255.scalar"::Element>,
      P g: Vector<"ristretto255.group"::Element>
    );
    outputs (
      P "bls12-381.fr"::Element,
      P "ristretto255.group"::Element,
      P Vector<"bls12-381.fr"::Element>
    );
    local [dot] P: let d = Dot(w, a, v);
    local [msm] P: let m = MSM(r, b, g);
    local [dense] P: let dense = Dense(a, v);
    return (d, m, dense);
  }

  instance concrete: Main {
    roles (P = P, V = V);
  }

  entry main = concrete;
}
