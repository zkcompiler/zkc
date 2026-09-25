// One interface-checked client, two private representations. These components
// exercise ownership and fallible calls; they are not cryptographic validators.
module {
  library(namespace="zkc.examples", name="checked-components", version="1",
          resolution="source-example");

  interface Cell {
    type State drop;
    local start(ok: bool) -> State effects (local);
    local step(state: State) -> State;
    local finish(state: State, ok: bool) -> bool;
  }

  component EmptyCell: Cell {
    type State = ();
    local start(ok: bool) -> State effects (local) {
      control::require(ok);
      return ();
    }
    local step(state: State) -> State { return state; }
    local finish(state: State, ok: bool) -> bool { return ok; }
  }

  component StoredCell: Cell {
    type State = bool;
    local start(ok: bool) -> State effects (local) {
      control::require(ok);
      return ok;
    }
    local step(state: State) -> State { return state; }
    local finish(state: State, ok: bool) -> bool { return state; }
  }

  fn Client<C: Cell>(ok: bool) -> bool effects (local) {
    let state = C::start(ok);
    let next = C::step(state);
    return C::finish(next, ok);
  }

  link Empty = Client<EmptyCell>;
  link Stored = Client<StoredCell>;

  protocol EmptyExample {
    roles (P);
    inputs (P ok: bool);
    outputs (P bool);
    local P: let answer = Empty(ok);
    return answer;
  }
  protocol StoredExample {
    roles (P);
    inputs (P ok: bool);
    outputs (P bool);
    local P: let answer = Stored(ok);
    return answer;
  }
  instance EmptyRun: EmptyExample { roles (P = Prover); }
  instance StoredRun: StoredExample { roles (P = Prover); }
  entry empty = EmptyRun;
  entry stored = StoredRun;
}
