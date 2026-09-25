module {
  bind both = bool.and();
  fn Local(unused: bool, x: bool, y: bool) -> (bool) {
    [dead] let dead = both(x, y);
    [last] let result = both(x, y);
    return (result);
  }
  protocol Main {
    roles (P);
    inputs (P unused: bool, P x: bool, P y: bool);
    outputs (P bool);
    local [work] P: let result = Local(unused, x, y);
    return (result);
  }
  instance root: Main { roles (P = P); }
  entry main = root;
}
