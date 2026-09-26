"""Checked library entries preserve aggregate formation and forwarding identity."""
import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())

AGGREGATE = """module { library(namespace="test", name="entries", version="1", resolution="one");
  struct Held(empty: Array<bool, 0>, pair: (bool, bool));
  fn Echo(input: Held) -> Held { return input; }
  link Closed = Echo<>;
  configure Configured = Echo();
  interface Cell { type Value drop; local step(x: Value) -> Value; }
  component Unit: Cell { type Value = (); local step(x: Value) -> Value { return x; } }
  fn Client<C: Cell>(x: C::Value, data: Held) -> (C::Value, Held) { return (C::step(x), data); }
  link Mixed = Client<Unit>;
}"""
TICKET = """module { library(namespace="test", name="entries", version="1", resolution="one");
  checked struct Ticket(value: bool) constructors(Make);
  fn Make(value: bool) -> Ticket { return Ticket(value = value); }
  fn Echo(x: Ticket) -> Ticket { return x; }
  link Closed = Echo<>;
}"""

with case("link, configure and self-link preserve the same aggregate boundary"):
    module = json.loads(commands.source("protocol-source", AGGREGATE))
    functions = {f[1]: f for f in module[2]}
    target = functions["Closed"][4][0][2]
    for name in ("Closed", "Configured", "Echo"):
        f = functions[name]
        assert f[2:4] == [[["input.pair.0", "bool"], ["input.pair.1", "bool"]], ["bool", "bool"]]
        assert f[4] == [
            ["apply", "invoke", target, [], ["input.pair.0", "input.pair.1"], ["__link_result_0", "__link_result_1"]],
            ["return", ["__link_result_0", "__link_result_1"]],
        ]
        assert f[5] == [name, []]
    mixed = functions["Mixed"]
    assert mixed[2][0] == ["x", "resource_unit:library_slot_0"]
    assert mixed[3] == ["resource_unit:library_slot_0", "bool", "bool"]
    assert functions[target][5] == ["Echo", []]
    report = json.loads(commands.source("protocol-analyze", AGGREGATE))
    owners = {d["id"] for d in report["declarations"] if d["name"] in ("Closed", "Configured", "Echo", "Mixed")}
    uses = [u for u in report["uses"] if u["owner"] in owners]
    assert len(uses) == 4 and all(u["kind"] == "call" and u["site"] == "invoke" for u in uses), uses
    assert all(u["span"] is not None for u in uses), uses
    assert not [b for b in report["local_bindings"] if b["owner"] in owners], report["local_bindings"]

with case("linked result construction cannot bypass checked record authority"):
    for shape in ("Ticket", "(Ticket, bool)", "Array<Ticket, 1>"):
        source = TICKET.replace("fn Echo(x: Ticket) -> Ticket", f"fn Echo(x: {shape}) -> {shape}")
        commands.source("protocol-source", source, refuses="source-checked-construction")
        report = json.loads(commands.source("protocol-analyze", source))
        diagnostic = report["diagnostics"][0]
        assert diagnostic["code"] == "source-checked-construction"
        assert diagnostic["span"]["offset"] == source.index("link Closed")
    source = TICKET.replace("fn Echo(x: Ticket) -> Ticket", "fn Echo(x: Array<Ticket, 0>) -> Array<Ticket, 0>")
    commands.source("protocol-source", source)

with case("projected and canonical field spellings have one linked layout"):
    source = """module {
      library(namespace="test", name="entries", version="1", resolution="one");
      struct Held(x: bls12-381.g1::Scalar::Element, y: bls12-381.fr::Element);
      fn Echo(value: Held) -> Held { return value; }
      link Closed = Echo<>;
    }"""
    module = json.loads(commands.source("protocol-source", source))
    functions = {f[1]: f for f in module[2]}
    entry = functions["Closed"]
    assert entry[2] == [["value.x", "field:bls12-381.fr"], ["value.y", "field:bls12-381.fr"]]
    assert entry[3] == ["field:bls12-381.fr", "field:bls12-381.fr"]

with case("generated entries reserve aliases during static specialization"):
    source = """module {
      library(namespace="test", name="entries", version="1", resolution="one");
      fn Echo(x: (bool, bool)) -> (bool, bool) { return x; }
      link __stage_45_protocol_726f6f74 = Echo<>;
      protocol Family<F: Field> {
        roles (P); inputs (P x: F::Element); outputs (P F::Element); return x;
      }
      entry E = Family::<F = koala-bear>;
    }"""
    commands.source("protocol-source", source, refuses="source-static-duplicate")
