module {
  fn Select(n: index) -> index { return n; }
  protocol Family {
    roles (P, V);
    parameters (rounds);
    inputs (P pn: index, V vn: index);
    outputs (P index, V index);
    loop [round] rounds carry (a = pn, b = vn) -> (x, y) {
      message [ping] index: P(a) -> V(got);
      yield (a, got);
    }
    return (x, y);
  }
  instance Main: Family {
    parameters (rounds = ingress(10, P = Select(pn), V = Select(vn)));
    roles (P = P, V = V);
  }
  entry main = Main;
}
