// Ordinary error values, isolated matches, and ownership-safe finite traversal.
module {
  library(namespace="zkc.examples", name="checked-variants", version="1",
          resolution="source-example");
  interface Cell {
    type State drop;
    local start(ok: bool) -> State;
    local step(state: State) -> State;
    local finish(state: State, ok: bool) -> bool;
  }
  enum Outcome<C: Cell> { Ready(C::State), Invalid(bool) }
  component EmptyCell: Cell {
    type State = ();
    local start(ok: bool) -> State { return (); }
    local step(state: State) -> State { return state; }
    local finish(state: State, ok: bool) -> bool { return ok; }
  }
  component StoredCell: Cell {
    type State = bool;
    local start(ok: bool) -> State { return ok; }
    local step(state: State) -> State { return state; }
    local finish(state: State, ok: bool) -> bool { return state; }
  }
  fn Ready<C: Cell>(ok: bool) -> bool {
    let state = C::start(ok);
    if ok capture(state, ok) -> (result) {
      let ready: Outcome<C> = Outcome::Ready(state);
      yield (ready);
    } else {
      let invalid: Outcome<C> = Outcome::Invalid(ok);
      yield (invalid);
    }
    match result capture(ok) -> (answer) {
      Ready(state) => {
        let next = C::step(state);
        let answer = C::finish(next, ok);
        yield (answer);
      },
      Invalid(error) => { yield (error); }
    }
    return answer;
  }
  fn Invalid<C: Cell>(error: bool) -> bool {
    let result: Outcome<C> = Outcome::Invalid(error);
    match result capture(error) -> (answer) {
      Ready(state) => {
        let answer = C::finish(state, error);
        yield (answer);
      },
      Invalid(error_value) => { yield (error_value); }
    }
    return answer;
  }
  fn Traverse<C: Cell>(ok: bool) -> bool {
    let elements = [C::start(ok), C::start(ok)];
    let initial = C::start(ok);
    for element in elements carry(state = initial) capture(ok) -> (output) {
      let accepted = C::finish(state, ok);
      let next = C::step(element);
      yield (next);
    }
    return C::finish(output, ok);
  }
  fn Zero<C: Cell>(ok: bool) -> bool {
    let empty: Array<C::State, 0> = [];
    let initial = C::start(ok);
    for element in empty carry(state = initial) capture(ok) -> (output) {
      let accepted = C::finish(state, ok);
      let next = C::step(element);
      yield (next);
    }
    return C::finish(output, ok);
  }
  link ReadyEmpty = Ready<EmptyCell>;
  link ReadyStored = Ready<StoredCell>;
  link ErrorValue = Invalid<StoredCell>;
  link Walk = Traverse<EmptyCell>;
  link NoTrips = Zero<EmptyCell>;
  protocol ReadyExample {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let answer = ReadyEmpty(ok);
    return answer;
  }
  protocol StoredExample {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let answer = ReadyStored(ok);
    return answer;
  }
  protocol ErrorExample {
    roles (P); inputs (P error: bool); outputs (P bool);
    local P: let answer = ErrorValue(error);
    return answer;
  }
  protocol WalkExample {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let answer = Walk(ok);
    return answer;
  }
  protocol ZeroExample {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let answer = NoTrips(ok);
    return answer;
  }
  instance ReadyRun: ReadyExample { roles (P = Prover); }
  instance StoredRun: StoredExample { roles (P = Prover); }
  instance ErrorRun: ErrorExample { roles (P = Prover); }
  instance WalkRun: WalkExample { roles (P = Prover); }
  instance ZeroRun: ZeroExample { roles (P = Prover); }
  entry ready = ReadyRun;
  entry stored = StoredRun;
  entry error = ErrorRun;
  entry walk = WalkRun;
  entry zero = ZeroRun;
}
