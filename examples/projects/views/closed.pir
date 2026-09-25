// Independent concrete specification of the externally visible return/stop.
// Resource observations belong to the selected implementations, not this model.
module {
  fn Expected(ready: bool, ok: bool) -> bool {
    control::require(ok);
    return ready;
  }
  protocol Direct {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = Expected(ready, ok);
    return answer;
  }
  instance run: Direct { roles (P = P); }
  entry main = run;
}
