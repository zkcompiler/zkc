module {
  fn Work<F: domain Field>(
    cs: Vector<F::Element>,
    shift: F::Element,
    beta: F::Element,
    n: index,
    query: index
  ) -> (
    Vector<F::Element>,
    Vector<F::Element>,
    Vector<F::Element>,
    F::Element,
    Indices,
    index,
    index
  ) requires (TwoAdicField(F), CharacteristicNotTwo(F)) {
    [__site_0] let p = poly::from_coefficients::<F>(cs);
    [__site_1] let evaluated = poly::coset_evaluate::<F>(p, shift, n);
    [__site_2] let back = poly::coset_interpolate::<F>(evaluated, shift);
    [__site_3] let coefficients = poly::coefficients::<F>(back);
    [__site_4] let folded = poly::even_odd_fold::<F>(evaluated, shift, beta);
    [__site_5] let selected = vector::get::<F>(evaluated, query);
    [__site_6] let zero = indices::empty();
    [__site_7] let one = indices::append(zero, query);
    [__site_8] let twice = indices::append(one, query);
    [__site_9] let size = indices::length(twice);
    [__site_10] let count = poly::coefficient_count::<F>(back);
    return (evaluated, coefficients, folded, selected, twice, size, count);
  }

  configure Concrete = Work(F = koala-bear);
  protocol Main {
    roles (P);
    inputs (
      P cs: Vector<koala-bear::Element>,
      P shift: koala-bear::Element,
      P beta: koala-bear::Element,
      P n: index,
      P query: index
    );
    outputs (
      P Vector<koala-bear::Element>,
      P Vector<koala-bear::Element>,
      P Vector<koala-bear::Element>,
      P koala-bear::Element,
      P Indices,
      P index,
      P index
    );
    local [__site_0] P: let (evaluated, coefficients, folded, selected, twice, size, count) = Concrete(
      cs,
      shift,
      beta,
      n,
      query
    );
    return (evaluated, coefficients, folded, selected, twice, size, count);
  }

  instance concrete: Main {
    roles (P = P);
  }

  entry main = concrete;
}
