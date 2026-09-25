// Private views are local values, not commitments or a new proof protocol.
module {
  library(namespace="zkc.examples", name="views", version="1", resolution="source-v1");
  mod layouts;
  pub use layouts::{ViewAPI, EmptyViews, StoredViews, TerminalViews};
  pub enum Result<C: ViewAPI> { Ready(C::View), Invalid(bool) }

  // Checks once against abstract permissions, before either layout is selected.
  pub fn Traverse<C: ViewAPI, N: nat>(items: Array<C::View, N>, initial: C::View, ok: bool)
      -> C::View effects (local) {
    for item in items carry(state = initial) capture(ok) -> (output) {
      let previous = C::finish(state, ok);
      let next = C::step(item);
      yield (next);
    }
    return output;
  }
  pub fn Choose<C: ViewAPI>(state: C::View, ready: bool, ok: bool) -> bool effects (local) {
    if ready capture(state, ready) -> (result) {
      let value: Result<C> = Result::Ready(state);
      yield (value);
    } else {
      let error: Result<C> = Result::Invalid(ready);
      yield (error);
    }
    match result capture(ok) -> (answer) {
      Ready(view) => { let value = C::finish(view, ok); yield (value); },
      Invalid(error) => { yield (error); }
    }
    return answer;
  }
  pub fn Zero<C: ViewAPI>(ready: bool, ok: bool) -> bool effects (local) {
    let items: Array<C::View, 0> = [];
    let initial = C::start(ok);
    let view = Traverse::<C, 0>(items, initial, ok);
    return Choose::<C>(view, ready, ok);
  }
  pub fn One<C: ViewAPI>(ready: bool, ok: bool) -> bool effects (local) {
    let items = [C::start(ok)];
    let initial = C::start(ok);
    let view = Traverse::<C, 1>(items, initial, ok);
    return Choose::<C>(view, ready, ok);
  }
  pub fn Many<C: ViewAPI>(ready: bool, ok: bool) -> bool effects (local) {
    let items = [C::start(ok), C::start(ok), C::start(ok)];
    let initial = C::start(ok);
    let view = Traverse::<C, 3>(items, initial, ok);
    return Choose::<C>(view, ready, ok);
  }
}
