"""Original-commitment terminals through the ordinary native proof compiler."""

import json
import re
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / "fixtures/mathematical"
SUITES = ["merlin3.bls12-381.fr64be/1", "spongefish0.7.4.keccak.bls12-381.fr64be/1"]
manifest = []
for family in ["product", "cubic", "authored", "structured"]:
    fixture = "structured-opening" if family == "structured" else "authored-opening" if family in ("authored", "structured") else "committed-" + family
    for i, suite in enumerate([""] if family in ("authored", "structured") else SUITES):
        for suffix, options in [
            ("", ()),
            ("_plain", ("--no-simplify",)),
            ("_release", ("--release-storage",)),
            ("_plain_release", ("--no-simplify", "--release-storage")),
        ]:
            name = f"{family}_{i}{suffix}"
            with case(name):
                source, policy = OUT / (name + ".mlir"), OUT / (name + ".policy")
                source.write_text((FIXTURES / (fixture + ".mlir")).read_text())
                selected = [
                    "zkc.native-proof-policy/5",
                    "main",
                    "P",
                    "V",
                    "0",
                    suite,
                    "" if family in ("authored", "structured") else "4",
                    ["2", "3", "4", "5"]
                    if family in ("authored", "structured")
                    else ["0", "3", "6", "7", "8"],
                    [] if family in ("authored", "structured") else [["draw", "challenge"]],
                ]
                policy.write_text(json.dumps(selected))
                result = commands.run(
                    [compiler, "protocol-proof", source, policy, *options]
                )
                envelope = json.loads(result)
                assert envelope[0] == "zkc.native-proof/5"
                assert envelope[2][0] == "zkc.native-proof-descriptor/5"
                (OUT / (name + ".deployment")).write_text(result)
                manifest.append(dict(name=name, family=family))
(OUT / "manifest.json").write_text(json.dumps(manifest))

for complete in ("true", "false"):
    with case(f"key-bearing attempt completion {complete}"):
        source = (FIXTURES / "authored-opening.mlir").read_text()
        source = source.replace('"protocol.return"(%accepted) : (i1)->()',
                                f'%complete = arith.constant {complete}\n   "protocol.return"(%accepted,%complete) : (i1,i1)->()')
        source = source.replace('function_type=(!t,!pk,!vk,!c,!f,!f)->i1',
                                'function_type=(!t,!pk,!vk,!c,!f,!f)->(i1,i1)')
        source = source.replace('output_roles=[["V"]]} : ()->()\n})',
                                'output_roles=[["V"],["P"]]} : ()->()\n})')
        src = OUT / f'key_attempt_{complete}.mlir'
        src.write_text(source)
        (OUT / f'key_attempt_{complete}.deployment').write_text(commands.run(
            [compiler, 'protocol-proof', src, OUT / 'authored_0.policy']))


with case("retired policy refuses PCS deployments"):
    selected = json.loads((OUT / "product_0.policy").read_text())
    selected[0] = "zkc.native-proof-policy/3"
    policy = OUT / "old.policy"
    policy.write_text(json.dumps(selected))
    commands.run([compiler, "protocol-proof", OUT / "product_0.mlir", policy], refuses="native-proof-policy")

with case("every verifier input requires an explicit binding"):
    selected = json.loads((OUT / "product_0.policy").read_text())
    selected[7].remove("6")
    policy = OUT / "missing-binding.policy"
    policy.write_text(json.dumps(selected))
    commands.run([compiler, "protocol-proof", OUT / "product_0.mlir", policy], refuses="native-proof-public-bindings")

with case("multiple verifier setups are current public inputs"):
    source = (OUT / "authored_0.mlir").read_text()
    source = source.replace("%r:!f,%claim:!f):", "%r:!f,%claim:!f,%extra:!vk):")
    source = source.replace("function_type=(!t,!pk,!vk,!c,!f,!f)", "function_type=(!t,!pk,!vk,!c,!f,!f,!vk)")
    source = source.replace('[["P"],["P"],["V"],["V"],["P","V"],["V"]]', '[["P"],["P"],["V"],["V"],["P","V"],["V"],["V"]]')
    src, policy = OUT / "two-keys.mlir", OUT / "two-keys.policy"
    src.write_text(source)
    selected = json.loads((OUT / "authored_0.policy").read_text())
    selected[7].append("6")
    policy.write_text(json.dumps(selected))
    commands.run([compiler, "protocol-proof", src, policy])

with case("unused PCS entry operands still require setup authorization"):
    src, policy = OUT / "unused-key.mlir", OUT / "unused-key.policy"
    src.write_text('''!pk = !pcs.object<"multilinear.kzg.bls12-381/1", "prover_key">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%key:!pk,%accepted:i1):
   "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!pk,i1)->i1,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
''')
    policy.write_text(json.dumps(["zkc.native-proof-policy/5", "main", "P", "V", "0", "", "", ["1"], []]))
    commands.run([compiler, "protocol-proof", src, policy], refuses="native-proof-setup-coverage")

with case("source checking retains terminal and construction provenance"):
    src, policy = OUT / "product_0.mlir", OUT / "product_0.policy"
    original = commands.run([compiler, "protocol-construct-proof", src, policy])
    candidate = OUT / "constructed.mlir"
    candidate.write_text(original)
    commands.run([compiler, "protocol-check-proof", src, policy, candidate])
    candidate.write_text(original.replace("zkc.native-construction/5", "zkc.native-construction/3"))
    commands.run([compiler, "protocol-check-proof", src, policy, candidate], refuses="native-proof-candidate")
    candidate.write_text(original.replace("maximum = 8 : i64", "maximum = 9 : i64"))
    assert candidate.read_text() != original
    commands.run([compiler, "protocol-check-proof", src, policy, candidate], refuses="native-proof-correspondence")
with case("source checking preserves the terminal acceptance dependency"):
    src, policy = OUT / "product_0.mlir", OUT / "product_0.policy"
    original = commands.run([compiler, "protocol-construct-proof", src, policy])
    candidate = OUT / "bypassed-terminal.mlir"
    candidate.write_text(original)
    commands.run([compiler, "protocol-check-proof", src, policy, candidate])
    # Keep every operation and action record. An earlier root-equality result
    # dominates this opening guard, but cannot establish the opening check.
    condition = re.search(r'local\.guard (%[^ ]+) \{site = "root_T_check"\}', original)
    assert condition
    changed, count = re.subn(
        r'local\.guard %[^ ]+( \{site = "[^"\n]*opening_check"\})',
        lambda m: 'local.guard ' + condition[1] + m[1],
        original, count=1,
    )
    assert count == 1
    candidate.write_text(changed)
    commands.run([compiler, "protocol-check-proof", src, policy, candidate],
                 refuses="native-proof-correspondence")

with case("retired policy refuses private PCS operands"):
    selected = json.loads((OUT / "unused-key.policy").read_text())
    selected[0] = "zkc.native-proof-policy/3"
    policy = OUT / "private-old.policy"
    policy.write_text(json.dumps(selected))
    commands.run([compiler, "protocol-proof", OUT / "unused-key.mlir", policy], refuses="native-proof-policy")

with case("verifier keys require a bound validator port"):
    source = (OUT / "unused-key.mlir").read_text().replace('"prover_key"', '"verifier_key"')
    src = OUT / "private-verifier.mlir"
    src.write_text(source)
    commands.run([compiler, "protocol-proof", src, OUT / "unused-key.policy"], refuses="native-proof-verifier-key-port")
counted()
