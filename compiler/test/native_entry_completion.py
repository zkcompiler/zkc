"""General entry completion: projection, schedule coverage and invalid sources."""

import json
import re
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import records, compiler, tool

OUT = records()
commands = Commands(OUT)
manifest = []
source = """!f = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%p:i1,%v:i1,%n:ui64,%data:!f):
   BODY
   %sent = protocol.exchange %data {sender="P",receiver="V",site="message"} : !f
   %ok = arith.constant true
   "protocol.return"(%ok,%ok) : (i1,i1)->()
 }) {sym_name="main",function_type=(i1,i1,ui64,!f)->(i1,i1),roles=["P","V"],input_roles=[["P"],["V"],["P","V"],["P","V"]],output_roles=[["P"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
"""
for depth, communicate in [(0, False), (1, False), (2, False), (1, True), (2, True)]:
    body = "\n".join(
        f'"protocol.finish_if"(%{role.lower()},%{role.lower()}) {{owner="{role}",site="exit_{role}"}} : (i1,i1)->()'
        for role in ["P", "V"]
    )
    if communicate:
        body += '\n%received = protocol.exchange %data {sender="P",receiver="V",site="inner_message"} : !f'
    for level in range(depth):
        for name in ["p", "v", "n", "data"]:
            body = re.sub(r"%" + name + r"\b", f"%{name}{level}", body)
        body = f""""protocol.repeat"(%n,%p,%v,%n,%data) ({{
          ^round{level}(%i{level}:ui64,%p{level}:i1,%v{level}:i1,%n{level}:ui64,%data{level}:!f):
          {body}
          "protocol.yield"() : ()->()
        }}) {{site="loop{level}",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]}} : (ui64,i1,i1,ui64,!f)->()"""
    text = source.replace("BODY", body)
    for suffix, options in [
        ("", []),
        ("_plain", ["--no-simplify"]),
        ("_release", ["--release-storage"]),
    ]:
        name = f"completion_{depth}" + ("_message" if communicate else "") + suffix
        with case(name):
            (OUT / f"{name}.mlir").write_text(text)
            (OUT / f"{name}.bundle").write_text(
                commands.source("protocol-bundle", text, *options)
            )
            manifest.append(
                dict(name=name, depth=depth, sends=1 + (2**depth if communicate else 0))
            )
with case("returned role does not participate in count agreement"):
    independent = """module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%exit:i1,%n:ui64):
        %no = arith.constant false
        "protocol.finish_if"(%exit,%no) {owner="P",site="exit_P"} : (i1,i1)->()
        "protocol.repeat"(%n) ({ ^round(%i:ui64):
          "protocol.yield"() : ()->()
        }) {site="rounds",carried=0:i64,maximum=3:i64,roles=["P","Q","V"],carried_roles=[]} : (ui64)->()
        %yes = arith.constant true
        "protocol.return"(%yes) : (i1)->()
      }) {sym_name="main",function_type=(i1,ui64)->i1,roles=["P","Q","V"],input_roles=[["P"],["P","Q","V"]],output_roles=[["P","Q","V"]]} : ()->()
    }) {profile=#protocol.profile<protocol>} : ()->() }"""
    (OUT / "independent_counts.bundle").write_text(
        commands.source("protocol-bundle", independent)
    )
# Formation must inspect the unreachable suffix and reject unavailable owners.
flat = source.replace(
    "BODY", '"protocol.finish_if"(%p,%p) {owner="P",site="exit"} : (i1,i1)->()'
)
for label, text in [
    ("wrong-owner", flat.replace('owner="P"', 'owner="absent"')),
    (
        "wrong-type",
        flat.replace("(%p,%p) {owner", "(%data,%p) {owner").replace(
            "(i1,i1)->()\n   %sent", "(!f,i1)->()\n   %sent"
        ),
    ),
    (
        "wrong-tuple",
        flat.replace("(%p,%p) {owner", "(%p) {owner").replace(
            "(i1,i1)->()\n   %sent", "(i1)->()\n   %sent"
        ),
    ),
]:
    with case(label):
        commands.source("protocol-bundle", text, refuses="interactive-return-type")
with case("component application cannot retarget entry completion"):
    wrapper = """ "protocol.func"() ({ ^entry(%p:i1,%v:i1,%n:ui64,%data:!f):
      %out:2 = protocol.apply @main(%p,%v,%n,%data) {roles=["P","V"],site="call"} : (i1,i1,ui64,!f)->(i1,i1)
      "protocol.return"(%out#0,%out#1) : (i1,i1)->()
    }) {sym_name="wrapper",function_type=(i1,i1,ui64,!f)->(i1,i1),roles=["P","V"],input_roles=[["P"],["V"],["P","V"],["P","V"]],output_roles=[["P"],["V"]]} : ()->()
"""
    commands.source(
        "protocol-bundle",
        flat.replace("}) {profile=", wrapper + "}) {profile="),
        refuses="conditional entry completion cannot be applied",
    )
with case("exit operands preserve source correspondence"):
    fixture = Path(__file__).parent / "fixtures/mathematical/attempt-abandonment.mlir"
    policy = OUT / "completion.policy"
    policy.write_text(
        json.dumps(
            [
                "zkc.native-proof-policy",
                "main",
                "P",
                "V",
                "0",
                "merlin3.bls12-381.fr64be/1",
                "3",
                ["0", "1"],
                [["draw", "challenge"]],
            ]
        )
    )
    candidate = commands.run([compiler, "protocol-construct-proof", fixture, policy])
    target = OUT / "completion.candidate.mlir"
    target.write_text(candidate)
    commands.run([compiler, "protocol-check-proof", fixture, policy, target])
    changed, n = re.subn(
        r'("protocol.finish_if"\()(%[\w]+), (%[\w]+)', r"\1\3, \2", candidate, count=1
    )
    assert n == 1
    target.write_text(changed)
    commands.run(
        [compiler, "protocol-check-proof", fixture, policy, target],
        refuses="native-proof-correspondence",
    )
with case("raw executable completion continuation arity"):
    deployment = json.loads(commands.run([compiler, "protocol-proof", fixture, policy]))
    program = json.loads(deployment[4])

    def remove_continuation(value):
        if not isinstance(value, list):
            return 0
        if value and value[0] == "return_if":
            value[4].pop()
            return 1
        return sum(remove_continuation(child) for child in value)

    assert remove_continuation(program) == 1
    commands.run(
        [tool("program_codec")],
        stdin=json.dumps(program),
        refuses="interactive-shape",
    )
with case("exit cannot interrupt selected challenge derivation"):
    text = fixture.read_text()
    line = next(line for line in text.splitlines() if '"protocol.finish_if"' in line)
    text = text.replace(line + "\n", "").replace(
        "     %challenge =", line + "\n     %challenge ="
    )
    src = OUT / "pending.mlir"
    src.write_text(text)
    commands.run(
        [compiler, "protocol-proof", src, policy], refuses="native-proof-prefix"
    )
(OUT / "manifest.json").write_text(json.dumps(manifest))
print(f"Entry completion: {counted()} cases; evidence: {OUT}")
