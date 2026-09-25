// Parameter order is deliberately nonlexical. Roles keep independent counts.
module {
  fn Select(n: index) -> index { return n; }
  protocol Family {
    roles (P, V);
    parameters (rounds, earlier);
    inputs (P first: index, P later: index, V receivedFirst: index, V receivedLater: index);
    outputs (P index, V index);
    loop [round] rounds carry (a = first, b = receivedFirst) -> (x, y) {
      message [ping] index: P(a) -> V(got);
      yield (a, got);
    }
    return (x, y);
  }
  instance Main: Family {
    parameters (
      rounds = ingress(10, P = Select(later), V = Select(receivedLater)),
      earlier = ingress(10, P = Select(first), V = Select(receivedFirst))
    );
    roles (P = P, V = V);
  }
  entry main = Main;
}
