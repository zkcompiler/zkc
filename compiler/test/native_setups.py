"""Independent setups compose through ordinary protocol applications."""

import json
from pathlib import Path
from cases import case
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
source = Path(__file__).parent / "fixtures/mathematical/independent-setups.mlir"
manifest = []
for suffix, options in [
    ("", ()),
    ("_plain", ("--no-simplify",)),
    ("_release", ("--release-storage",)),
]:
    name = "setups" + suffix
    with case(name):
        policy = OUT / (name + ".policy")
        policy.write_text(
            json.dumps(
                [
                    "zkc.native-proof-policy/5",
                    "main",
                    "P",
                    "V",
                    "0",
                    "",
                    "",
                    ["2", "3", "4", "5", "8", "9", "10", "11"],
                    [],
                ]
            )
        )
        candidate = OUT / (name + ".candidate.mlir")
        candidate.write_text(
            commands.run([compiler, "protocol-construct-proof", source, policy])
        )
        commands.run([compiler, "protocol-check-proof", source, policy, candidate])
        (OUT / (name + ".deployment")).write_text(
            commands.run([compiler, "protocol-proof", source, policy, *options])
        )
        manifest.append(dict(name=name))
with case("actual terminal key operand remains source-bound"):
    original = (OUT / "setups.candidate.mlir").read_text()
    changed = original.replace(
        "local.call @check(%arg0,", "local.call @check(%arg4,", 1
    )
    assert changed != original
    candidate = OUT / "swapped-key.candidate.mlir"
    candidate.write_text(changed)
    commands.run(
        [compiler, "protocol-check-proof", source, policy, candidate],
        refuses="native-proof-correspondence",
    )
for same_arity in (False, True):
    name = "wrong-terminal-key" if same_arity else "wrong-terminal-arity"
    with case(name):
        text = source.read_text().replace(
            '"protocol.apply"(%ta,%pka,%vka,%ca,%ra,%va)',
            '"protocol.apply"(%ta,%pka,%vkb,%ca,%ra,%va)',
        )
        if same_arity:
            text = text.replace("callee=@double", "callee=@single")
        wrong = OUT / (name + ".mlir")
        wrong.write_text(text)
        (OUT / (name + ".deployment")).write_text(
            commands.run([compiler, "protocol-proof", wrong, policy])
        )
        manifest.append(dict(
            name=name, same_arity=same_arity,
            refusal="key-mismatch" if same_arity else "arity-mismatch",
        ))
with case("unused keys and terminal commitments"):
    text = source.read_text()
    start = text.index('   %a = "protocol.apply"(%ta')
    end = text.index(' }) {sym_name="main"', start)
    text = (
        text[:start]
        + """   %ok = arith.constant true
   "protocol.return"(%ok,%ca,%cb) : (i1,!c,!c)->()
"""
        + text[end:]
    )
    text = text.replace(
        'sym_name="main",function_type=(!t,!pk,!vk,!c,!f,!f,!t,!pk,!vk,!c,!f,!f)->i1',
        'sym_name="main",function_type=(!t,!pk,!vk,!c,!f,!f,!t,!pk,!vk,!c,!f,!f)->(i1,!c,!c)',
    )
    text = text.replace(
        '[["V"]]} : ()->()\n}) {profile', '[["V"],["V"],["V"]]} : ()->()\n}) {profile'
    )
    terminal = OUT / "terminal.mlir"
    terminal.write_text(text)
    (OUT / "terminal.deployment").write_text(
        commands.run([compiler, "protocol-proof", terminal, policy])
    )
    manifest.append(dict(name="terminal"))
with case("derived transcript observes two authorized setups"):
    text = source.read_text().replace(
        "module {", '!svc = !protocol.service_ref<"random.bls12-381.fr/1">\nmodule {', 1
    )
    text = text.replace("%rb:!f,%vb:!f):", "%rb:!f,%vb:!f,%random:!svc):")
    text = text.replace(
        '   %a = "protocol.apply"(%ta',
        '\n   %q = "protocol.query"(%random) {owner="V",method="draw",site="draw"} : (!svc)->!f\n'
        '   %received = protocol.exchange %q {sender="V",receiver="P",site="challenge"} : !f\n'
        '   %a = "protocol.apply"(%ta',
    )
    text = text.replace(
        'sym_name="main",function_type=(!t,!pk,!vk,!c,!f,!f,!t,!pk,!vk,!c,!f,!f)->i1',
        'sym_name="main",function_type=(!t,!pk,!vk,!c,!f,!f,!t,!pk,!vk,!c,!f,!f,!svc)->i1',
    )
    text = text.replace(
        '[["P"],["P"],["V"],["V"],["P","V"],["V"],["P"],["P"],["V"],["V"],["P","V"],["V"]]',
        '[["P"],["P"],["V"],["V"],["P","V"],["V"],["P"],["P"],["V"],["V"],["P","V"],["V"],["V"]]',
    )
    derived = OUT / "derived.mlir"
    derived.write_text(text)
    policy = OUT / "derived.policy"
    policy.write_text(
        json.dumps(
            [
                "zkc.native-proof-policy/5",
                "main",
                "P",
                "V",
                "0",
                "merlin3.bls12-381.fr64be/1",
                "12",
                ["2", "3", "4", "5", "8", "9", "10", "11"],
                [["draw", "challenge"]],
            ]
        )
    )
    (OUT / "derived.deployment").write_text(
        commands.run([compiler, "protocol-proof", derived, policy])
    )
    manifest.append(dict(name="derived"))
# Return after the first application while the second setup remains an entry
# obligation. Both participants must return their current constructed state.
for suffix, options in [
    ("", ()),
    ("_plain", ("--no-simplify",)),
    ("_release", ("--release-storage",)),
]:
    name = "early" + suffix
    with case(name):
        text = derived.read_text().replace(
            '   %b = "protocol.apply"(%tb',
            '''   %early = algebra.field_equal %ra,%rb : (!f,!f)->i1
   "protocol.finish_if"(%early) {owner="P",site="finish_P"} : (i1)->()
   "protocol.finish_if"(%early,%a) {owner="V",site="finish_V"} : (i1,i1)->()
   %b = "protocol.apply"(%tb''',
        )
        early = OUT / (name + ".mlir")
        early.write_text(text)
        candidate = OUT / (name + ".candidate.mlir")
        candidate.write_text(
            commands.run([compiler, "protocol-construct-proof", early, policy])
        )
        commands.run([compiler, "protocol-check-proof", early, policy, candidate])
        (OUT / (name + ".deployment")).write_text(
            commands.run([compiler, "protocol-proof", early, policy, *options])
        )
        manifest.append(dict(name=name, early=True))
with case("early validator rejection"):
    rejected = OUT / "early-reject.mlir"
    rejected.write_text((OUT / "early.mlir").read_text().replace(
        '   "protocol.finish_if"(%early,%a)',
        '   %reject = arith.constant false\n   "protocol.finish_if"(%early,%reject)',
    ))
    (OUT / "early-reject.deployment").write_text(
        commands.run([compiler, "protocol-proof", rejected, policy])
    )
    manifest.append(dict(name="early-reject", early=True, refusal="artifact-rejected"))
(OUT / "manifest.json").write_text(json.dumps(manifest))
