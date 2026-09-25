module {
  pub interface ViewAPI {
    type View drop;
    local start(ok: bool) -> View effects (local);
    local step(view: View) -> View;
    local finish(view: View, ok: bool) -> bool effects (local);
  }
  pub component EmptyViews: ViewAPI {
    type View = ();
    local start(ok: bool) -> View effects (local) { control::require(ok); return (); }
    local step(view: View) -> View { return view; }
    local finish(view: View, ok: bool) -> bool effects (local) { return ok; }
  }
  pub component StoredViews: ViewAPI {
    type View = (bool, bool);
    local start(ok: bool) -> View effects (local) { control::require(ok); return (ok, ok); }
    local step(view: View) -> View { return view; }
    local finish(view: View, ok: bool) -> bool effects (local) { return view[0]; }
  }
  pub component TerminalViews: ViewAPI {
    type View = ();
    local start(ok: bool) -> View effects (local) { control::require(ok); return (); }
    local step(view: View) -> View { return view; }
    local finish(view: View, ok: bool) -> bool effects (local) { stop refused; }
  }
}
