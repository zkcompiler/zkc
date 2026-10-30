"""Native participant data use and identities are independent of byte names."""
import json

from cases import case, counted
from commands import Commands
from tools import records, canonical_program

commands = Commands(records())
FIELD = '!algebra.field<"bls12-381.fr">'
RNG = '!runtime.capability<rng, "bls12-381.fr">'


def participant(body, inputs=(), outputs=(), *, name="p", role="P",
                instance="example", attributes=""):
    arguments = ", ".join(f"%{name}: {ty}" for name, ty in inputs)
    types = ", ".join(ty for _, ty in inputs)
    return f'''"protocol.participant"() ({{
      ^entry({arguments}):
        {body}
    }}) {{sym_name="{name}", function_type=({types}) -> ({', '.join(outputs)}),
          instance="{instance}", role="{role}"{attributes}}} : () -> ()'''


def module(*participants, targets='[["P", @p]]'):
    return '''module { "protocol.module"() ({
    ''' + "\n".join(participants) + f'''
      "protocol.entry"() {{sym_name="main", targets={targets}}} : () -> ()
    }}) {{profile=#protocol.profile<exec>}} : () -> () }}'''


def export(source):
    physical = commands.verified(source, None, "--zkc-select-physical")
    model = json.loads(commands.source("protocol-export", physical))
    # Independent byte admission is still an export boundary.
    canonical_program(commands, json.dumps(model))
    return model


with case("service identity cannot collide with invented value names"):
    source = module(participant(f'''
      %draw = "protocol.service_query"() {{port="v0", method="draw", site="draw"}}
        : () -> {FIELD}
      "protocol.finish"(%draw) : ({FIELD}) -> ()
    ''', [("x", FIELD)], [FIELD],
        attributes=', service_ports=[["v0", "random.bls12-381.fr/0", 1 : i64]]'))
    commands.verified(source)
    model = export(source)
    endpoint = model[3][0]
    assert endpoint[7] == [["v0", "random.bls12-381.fr/0", "1"]]
    assert endpoint[4][0][0] != "v0"
    assert endpoint[6][0][2] == "v0"

for title, before, after, reason in [
    ("service ingress out of range", "1 : i64", "2 : i64", "service-port-interface"),
    ("service ingress uses exact integer type", "1 : i64", "1 : i32", "service-port-interface"),
    ("unknown service identity", "random.bls12-381.fr/0", "random.unknown/0", "service-port-interface"),
    ("query uses declared authority", 'port="v0"', 'port="missing"', "service-query-signature"),
    ("query preserves nominal field", FIELD, '!algebra.field<"bn254.fr">', "service-query-signature"),
]:
    with case(title):
        commands.verified(source.replace(before, after), reason)

for name, position in [("v0", 0), ("second", 1)]:
    with case("service names and positions are independently unique"):
        duplicate = source.replace('1 : i64]]', f'1 : i64], ["{name}", "random.bls12-381.fr/0", {position} : i64]]')
        commands.verified(duplicate, "service-port-interface")

with case("copy aliases remain distinct native loop formals"):
    loop = module(participant(f'''
      "protocol.loop"(%n, %x, %x) ({{
      ^body(%i: ui64, %left: {FIELD}, %right: {FIELD}):
        "protocol.send"(%left) {{site="left", schema="message", peer="Q"}} : ({FIELD}) -> ()
        "protocol.send"(%right) {{site="right", schema="message", peer="Q"}} : ({FIELD}) -> ()
        "protocol.yield"() : () -> ()
      }}) {{site="loop", carried=0 : i64, count="", parameter=false, maximum=8 : i64}}
        : (ui64, {FIELD}, {FIELD}) -> ()
      "protocol.finish"(%x) : ({FIELD}) -> ()
    ''', [("n", "ui64"), ("x", FIELD)], [FIELD]))
    commands.verified(loop)
    commands.verified(loop, "interactive-loop-capture", "--zkc-select-physical")
    commands.verified(loop.replace('site="right"', 'site="left"'), "interactive-site")

with case("loop invariant cannot borrow an affine capability"):
    bad = module(participant(f'''
      "protocol.loop"(%n, %rng) ({{
      ^body(%i: ui64, %r: {RNG}):
        "protocol.yield"() : () -> ()
      }}) {{site="loop", carried=0 : i64, count="", parameter=false, maximum=8 : i64}}
        : (ui64, {RNG}) -> ()
      "protocol.finish"() : () -> ()
    ''', [("n", "ui64"), ("rng", RNG)]))
    commands.verified(bad, "interactive-loop-capture")

with case("conditional finish transfers affine continuation"):
    completion = module(participant(f'''
      %next = "protocol.finish_if"(%go, %rng) {{site="finish", owner="P"}}
        : (i1, {RNG}) -> {RNG}
      "protocol.finish"(%next) : ({RNG}) -> ()
    ''', [("go", "i1"), ("rng", RNG)], [RNG]))
    commands.verified(completion)
    export(completion)
    commands.verified(completion.replace('"protocol.finish"(%next)', '"protocol.finish"(%rng)'),
                      "interactive-resource-reuse")


def sender(name, role, ty, instance="example"):
    return participant(f'''
      "protocol.send"(%x) {{site="send", schema="message", peer="R"}} : ({ty}) -> ()
      "protocol.finish"() : () -> ()
    ''', [("x", ty)], name=name, role=role, instance=instance)


with case("schema identity is scoped to the protocol instance"):
    first = sender("p", "P", FIELD)
    second = sender("q", "Q", "i1")
    commands.verified(module(first, second), "interactive-schema-type")
    commands.verified(module(first, sender("q", "Q", "i1", "other")))

with case("entry cannot combine different instances"):
    commands.verified(module(sender("p", "P", FIELD), sender("q", "Q", FIELD, "other"),
                             targets='[["P", @p], ["Q", @q]]'), "interactive-entry-instance")

with case("participant cannot communicate with its own role"):
    commands.verified(module(sender("p", "P", FIELD)).replace('peer="R"', 'peer="P"'),
                      "interactive-peer")

print(f"participant admission: {counted()} cases; {commands.save()} commands")
