module {
  fn Twice<F: Field>(x: F::Element) -> F::Element {
    let result = field::add(x, x);
    return result;
  }
  fn Work<F: Field>(x: F::Element, enabled: bool, start: index, end: index)
      -> (Vector<F::Element>, index) {
    let mut acc = x;
    for i in start..end {
      if enabled {
        acc = Twice::<F>(acc);
      } else {
        acc = field::add(acc, x);
      }
    }
    let values = [x, acc];
    let selected = values[1];
    let length = values.len();
    let output = [selected, x];
    return (output, length);
  }
  configure Concrete = Work(F = koala-bear);
  protocol Main {
    roles (P);
    inputs (P x: koala-bear::Element, P enabled: bool, P start: index, P end: index);
    outputs (P Vector<koala-bear::Element>, P index);
    local P: let (values, length) = Concrete(x, enabled, start, end);
    return (values, length);
  }
  instance concrete: Main { roles (P = P); }
  entry main = concrete;
}
