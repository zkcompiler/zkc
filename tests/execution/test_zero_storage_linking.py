"""Authored empty-representation adapters execute in Lean and native Rust.

Components construct resources through checked public methods. Each authored
client returns a Boolean while the tests check nominal resource accounting.
"""
from collections import Counter

import pytest


SOURCE = '''module {
  library(namespace="zkc.tests", name="zero-storage-execution", version="1",
          resolution="authored");
  interface Cell {
    type A drop;
    type B drop;
    local make(ok: bool) -> A;
    local through(x: A) -> A;
    local swap(x: A) -> B;
    local finishA(x: A, ok: bool) -> bool;
    local finishB(x: B, ok: bool) -> bool;
    local mixed(x: A, ok: bool) -> bool;
    local variant(x: A, ok: bool) -> bool;
    local variantHelper(x: A, ok: bool) -> bool;
    local nestedHelper(x: A, ok: bool) -> bool;
    local publicVariant(x: A, ok: bool) -> Holder;
    local createHas(x: A, ok: bool) -> bool;
    local createNothing(x: A, ok: bool) -> bool;
  }
  enum Holder { Has(((), bool)), Nothing(bool) }
  enum Outer { Wrap(Holder), Other(bool) }
  fn Id(x: ()) -> () { return x; }
  fn Snd(pair: ((), bool)) -> bool { return pair.1; }
  fn PlainHas(ok: bool) -> Holder {
    let pair = ((), ok);
    let holder: Holder = Holder::Has(pair);
    return holder;
  }
  fn PlainNothing(ok: bool) -> Holder {
    let holder: Holder = Holder::Nothing(ok);
    return holder;
  }
  fn Check(holder: Holder) -> bool {
    match holder capture() -> (answer) {
      Has(payload) => { yield (payload.1); },
      Nothing(value) => { yield (value); }
    }
    return answer;
  }
  fn CheckOuter(outer: Outer) -> bool {
    match outer capture() -> (answer) {
      Wrap(holder) => { let value = Check(holder); yield (value); },
      Other(value) => { yield (value); }
    }
    return answer;
  }
  component Empty: Cell {
    type A = ();
    type B = ();
    local make(ok: bool) -> A { return (); }
    local through(x: A) -> A { return Id(x); }
    local swap(x: A) -> B { return x; }
    local finishA(x: A, ok: bool) -> bool { return ok; }
    local finishB(x: B, ok: bool) -> bool { return ok; }
    local mixed(x: A, ok: bool) -> bool {
      let pair = (x, ok);
      if ok capture(pair) -> (answer) {
        let value = Snd(pair); yield (value);
      } else {
        let value = Snd(pair); yield (value);
      }
      return answer;
    }
    local variant(x: A, ok: bool) -> bool {
      let pair = (x, ok);
      let holder: Holder = Holder::Has(pair);
      match holder capture() -> (answer) {
        Has(payload) => { yield (payload.1); },
        Nothing(value) => { yield (value); }
      }
      return answer;
    }
    local variantHelper(x: A, ok: bool) -> bool {
      let pair = (x, ok);
      if ok capture(pair, ok) -> (holder) {
        let value: Holder = Holder::Has(pair); yield (value);
      } else {
        let value: Holder = Holder::Nothing(ok); yield (value);
      }
      return Check(holder);
    }
    local nestedHelper(x: A, ok: bool) -> bool {
      let pair = (x, ok);
      if ok capture(pair, ok) -> (holder) {
        let value: Holder = Holder::Has(pair); yield (value);
      } else {
        let value: Holder = Holder::Nothing(ok); yield (value);
      }
      let outer: Outer = Outer::Wrap(holder);
      return CheckOuter(outer);
    }
    local publicVariant(x: A, ok: bool) -> Holder {
      let pair = (x, ok);
      if ok capture(pair, ok) -> (holder) {
        let value: Holder = Holder::Has(pair); yield (value);
      } else {
        let value: Holder = Holder::Nothing(ok); yield (value);
      }
      return holder;
    }
    local createHas(x: A, ok: bool) -> bool {
      if ok capture(x, ok) -> (holder) {
        let pair = (x, ok);
        let value: Holder = Holder::Has(pair); yield (value);
      } else {
        let value = PlainHas(ok); yield (value);
      }
      return Check(holder);
    }
    local createNothing(x: A, ok: bool) -> bool {
      if ok capture(x, ok) -> (holder) {
        let pair = (x, ok);
        let value: Holder = Holder::Has(pair); yield (value);
      } else {
        let value = PlainNothing(ok); yield (value);
      }
      return Check(holder);
    }
  }
  fn PublicVariant<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    let holder = C::publicVariant(value, ok);
    return Check(holder);
  }
  fn VariantCreateHas<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    return C::createHas(value, ok);
  }
  fn VariantCreateNothing<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    return C::createNothing(value, ok);
  }
  fn Helper<C: Cell>(ok: bool) -> bool {
    let first = C::make(ok);
    let second = C::through(first);
    return C::finishA(second, ok);
  }
  fn Rebrand<C: Cell>(ok: bool) -> bool {
    let first = C::make(ok);
    let second = C::swap(first);
    return C::finishB(second, ok);
  }
  fn Mixed<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    return C::mixed(value, ok);
  }
  fn Variant<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    return C::variant(value, ok);
  }
  fn VariantHelper<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    return C::variantHelper(value, ok);
  }
  fn NestedHelper<C: Cell>(ok: bool) -> bool {
    let value = C::make(ok);
    return C::nestedHelper(value, ok);
  }
  link Closed = CLIENT<Empty>;
  protocol Run {
    roles (P); inputs (P ok: bool); outputs (P bool);
    local P: let answer = Closed(ok);
    return answer;
  }
  instance run: Run { roles (P = P); }
  entry main = run;
}'''


@pytest.mark.parametrize("client,units", [
    ("Helper", 2), ("Rebrand", 2), ("Mixed", 1), ("Variant", 1),
    ("VariantHelper", 1), ("NestedHelper", 1), ("PublicVariant", 1),
    ("VariantCreateHas", 1), ("VariantCreateNothing", 1),
])
@pytest.mark.parametrize("ok", [True, False], ids=["true", "false"])
def test_zero_storage_adapters_execute(toolchain, directory, journal, client, units, ok):
    authored = directory / "authored.pir"
    authored.write_text(SOURCE.replace("CLIENT", client))
    common = journal.json([toolchain.compiler, "protocol-source", authored])
    source = journal.write("source.json", common)
    journal.run([toolchain.compiler, "protocol-admit", source])
    checker = toolchain.checker("interactive-protocol")
    assert journal.json([checker, "--admit", source])[0] == "checked"
    physical = journal.write("physical.json", journal.json([
        toolchain.compiler, "protocol-compile", source]))
    assert journal.json([checker, "--check", source, physical])[0] == "checked"

    reference_inputs = journal.write("reference-inputs.json", [
        "zkc.reference-inputs/1", "main", "zero-storage",
        [["P", [["ok", ["bool", str(ok).lower()]]]]], [], [], [],
    ])
    wire = (b"ZKCV\x01\x05" + bytes([ok])).hex()
    native_inputs = journal.write("native-inputs.json", [
        "zkc.run/2", "main", "zero-storage", [],
        [["P", [], [["ok", ["wire", wire]]], []]], [],
    ])
    reference = journal.json([checker, "--reference", source, reference_inputs])
    native = journal.json([
        toolchain.runtime, "run-protocol", source, physical, native_inputs, checker])
    journal.write("reference-result.json", reference)
    journal.write("native-result.json", native)

    assert reference[3] == ["returned", [["bool", str(ok).lower()]]]
    assert native["outcome"] == ["returned", {"P": [["bool", ok]]}]
    assert reference[5] == []
    assert native["resources"] == []
    assert native["usage"]["P"]["live_resource_units"] == 0
    assert native["wire"]["messages"] == native["wire"]["payload_bytes"] == 0
    # The plain Has result needs a fresh token when it joins the enriched
    # sibling. The original captured token is separately retired. Nothing
    # carries no token, so adapting that alternative must not mint one.
    if client == "VariantCreateHas" and not ok:
        units += 1
    requests = [event[1] for event in reference[4] if event[0] == "request"]
    assert Counter(request[2] for request in requests) == {
        "resource_unit.create": units, "resource_unit.consume": units,
    }
    created = Counter(tuple(r[3]) for r in requests if r[2] == "resource_unit.create")
    consumed = Counter(tuple(r[3]) for r in requests if r[2] == "resource_unit.consume")
    assert created == consumed
    # Rebranding disposes A and creates B; it cannot transfer A under B's name.
    # The helper round trip instead retires and recreates the same nominal slot.
    assert len(created) == (2 if client == "Rebrand" else 1)

    if client == "PublicVariant" and ok:
        disposal = next(r for r in requests if r[2] == "resource_unit.consume")
        assert any(frame[0] == "match" and frame[-1] == "Has"
                   for frame in disposal[1][4])
    if client == "VariantCreateHas" and not ok:
        mint = [r for r in requests if r[2] == "resource_unit.create"
                and any(frame[0] == "match" and frame[-1] == "Has"
                        for frame in r[1][4])]
        assert len(mint) == 1
