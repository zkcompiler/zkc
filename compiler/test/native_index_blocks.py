"""Compile source product requests and validate both actual native endpoints."""
import copy
import json
import re
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
SOURCE = (Path(__file__).parent / "fixtures/language/index_block.zkc").read_text()


def source(text, name="block"):
    path = OUT / f"{name}.zkc"
    path.write_text(text)
    return path


def language(text, name="block", refuses=None):
    return commands.run([compiler, "language-bundle", "--source-format=zkc",
                         "--entry=sample::Proof", f"--module=sample={source(text, name)}"],
                        refuses=refuses)


with case("source generates a logical block in both selected endpoints"):
    deployment = json.loads(language(SOURCE))
    assert len(deployment[2]) == 8 and len(deployment[2][1]) == 12
    sequence = deployment[2][3]
    event = next(e for e in sequence if e[0] == "indices")
    assert event[2:] == ["8", "5"] and deployment[2][7] == []
    original = commands.run([compiler, "language-emit", "--source-format=zkc",
                             "--entry=sample::Proof", f"--module=sample={OUT / 'block.zkc'}"])
    (OUT / "original.mlir").write_text(original)
    POLICY = deployment[2][1]
    assert len(POLICY[8]) == 1


def construct(bits, base=None, original="original.mlir", name=None, sites=None):
    policy = copy.deepcopy(POLICY if base is None else base)
    policy[11] = [[site, str(bits)] for site, _ in policy[8]
                  if sites is None or site in sites]
    name = name or f"gated-{bits}"
    path = OUT / f"{name}.policy"
    path.write_text(json.dumps(policy))
    candidate = commands.run([compiler, "protocol-construct-proof", OUT / original, path])
    actual = OUT / f"{name}.mlir"
    actual.write_text(candidate)
    commands.run([compiler, "protocol-check-proof", OUT / original, path, actual])
    deployed = commands.run([compiler, "protocol-proof", OUT / original, path])
    (OUT / f"{name}.deployment").write_text(deployed)
    return policy, path, candidate, json.loads(deployed)


for bits in [0, 8, 64]:
    with case(f"difficulty {bits} emits checked search, witness transport and gate"):
        policy, path, candidate, deployment = construct(bits)
        assert 'transcript.native.indexed.indices.search' in candidate
        assert 'transcript.native.indexed.indices.gated' in candidate
        descriptor = deployment[2]
        event = next(e for e in descriptor[3] if e[0] == "gated-indices")
        assert event[2:] == ["8", "5", str(bits)]
        slot = "gate." + policy[8][0][0]
        assert descriptor[7] == [[event[1], slot, "index", "native.index/0"]]
        assert [event[1], slot] in deployment[8]
        assert len(re.findall(r'schema = "' + re.escape(slot) + r'"', candidate)) == 2

with case("source distribution admits positive bounds outside native selection"):
    path = source(SOURCE.replace("Blocks<8,5>", "Blocks<3,1048577>"), "general")
    commands.run([compiler, "language-check", "--source-format=zkc",
                  "--entry=sample::Proof", f"--module=sample={path}"])

with case("applied blocks select distinct occurrences with reordered roles"):
    applied = SOURCE.replace("protocol Blocks", "protocol Child").replace("proof Proof", '''
protocol Blocks<N: nat, Q: nat> roles(V,P)(rounds: index @(P,V), coins: Random<E> @V)
    -> (accepted: bool @V) {
  let first = Child<N,Q> roles(P,V)(rounds, coins);
  let second = Child<N,Q> roles(P,V)(rounds, coins);
  return (accepted = second);
}
proof Proof''')
    base = json.loads(language(applied, "applied"))[2][1]
    original = commands.run([compiler, "language-emit", "--source-format=zkc",
                             "--entry=sample::Proof", f"--module=sample={OUT / 'applied.zkc'}"])
    (OUT / "applied.mlir").write_text(original)
    assert len(base[8]) == 2 and base[8][0][0] != base[8][1][0]
    policy, _, _, deployment = construct(0, base, "applied.mlir", "applied-gated")
    witnesses = deployment[2][7]
    assert [row[1] for row in witnesses] == ["gate." + site for site, _ in policy[8]]
    assert len(set(row[0] for row in witnesses)) == 2
    _, _, _, partial = construct(0, base, "applied.mlir", "applied-partial", [base[8][0][0]])
    assert [e[0] for e in partial[2][3] if e[0] in ["indices", "gated-indices"]] == ["gated-indices", "indices"]
    assert len(partial[2][7]) == 1

with case("actual-body mutations refuse independently of event annotations"):
    policy, path, candidate, _ = construct(8)
    # Mutations retain well-typed inputs but break actual call/transport association.
    for name, changed, refusal in [
        ("difficulty", candidate.replace('5 : ui64, 8 : ui64]', '5 : ui64, 9 : ui64]', 1),
         "native-proof-correspondence: native-transcript-correspondence"),
        ("witness schema", candidate.replace('schema = "gate.', 'schema = "other.', 1),
         "native-proof-candidate"),
        ("search binding", candidate.replace('transcript.native.indexed.indices.search', 'transcript.native.indexed.indices', 1),
         "native-proof-candidate"),
    ]:
        assert changed != candidate, name
        target = OUT / (name.replace(" ", "_") + ".mlir")
        target.write_text(changed)
        commands.run([compiler, "protocol-check-proof", OUT / "original.mlir", path, target],
                     refuses=refusal)

with case("the emitted witness must be the actual search result"):
    _, path, candidate, _ = construct(8)
    changed, edits = re.subn(r'("protocol.send"\()(%\d+#1)(\) <\{peer = "[^"]+", schema = "gate\.)',
                            r'\1%arg2\3', candidate, count=1)
    assert edits == 1
    commands.verified(changed)
    target = OUT / "wrong-witness.mlir"
    target.write_text(changed)
    commands.run([compiler, "protocol-check-proof", OUT / "original.mlir", path, target],
                 refuses="native-proof-correspondence: native-transcript-correspondence")

for label, gates in [
    ("unknown", [["unknown", "8"]]),
    ("delivery", [["DELIVERY", "8"]]),
    ("duplicate", [["QUERY", "8"], ["QUERY", "8"]]),
    ("overflow", [["QUERY", "65"]]),
    ("noncanonical", [["QUERY", "08"]]),
]:
    with case(f"policy refuses {label} gates"):
        policy = copy.deepcopy(POLICY)
        policy[11] = [[POLICY[8][0][0] if site == "QUERY" else POLICY[8][0][1] if site == "DELIVERY" else site, b]
                      for site, b in gates]
        path = OUT / f"bad-{label}.policy"
        path.write_text(json.dumps(policy))
        commands.run([compiler, "protocol-proof", OUT / "original.mlir", path],
                     refuses="native-proof-gate-selection" if label in ["unknown", "delivery"] else "native-proof-policy")

with case("the retired policy length refuses"):
    path = OUT / "old.policy"
    path.write_text(json.dumps(POLICY[:-1]))
    commands.run([compiler, "protocol-proof", OUT / "original.mlir", path], refuses="native-proof-policy")

for name, old, new, refusal in [
    ("zero bound", "Blocks<8,5>", "Blocks<0,5>", "source.service"),
    ("zero count", "Blocks<8,5>", "Blocks<8,0>", "source.service"),
    ("native nonpower", "Blocks<8,5>", "Blocks<3,5>", "native-proof-index-block"),
    ("native count ceiling", "Blocks<8,5>", "Blocks<8,1048577>", "native-proof-index-block"),
]:
    with case(f"source refuses {name}"):
        language(SOURCE.replace(old,new), name.replace(" ","_"), refusal)

with case("scalar index installation does not imply block installation"):
    scalar_only = SOURCE.replace("ext4-binomial3", "ext8-binomial3").replace("hash-chain.keccak256.", "merlin3.")
    language(scalar_only, "scalar_only_suite", "native-proof-index-block")

with case("custom query handlers cannot reinterpret a block as one bound"):
    custom = SOURCE.replace("let positions", "#[site(pick)] let positions").replace(
        'construction fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", coins);',
        'construction Custom;')
    custom += '''
construction Custom for Blocks<8,5> {
  base fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", coins);
  on query pick(t,bound) { return (t,0); }
}
'''
    language(custom, "custom_handler", "source.construction")

with case("custom construction plans cannot claim uninstalled block adapters"):
    custom = SOURCE.replace(
        'construction fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", coins);',
        'construction Custom;')
    custom += '''
construction Custom for Blocks<8,5> {
  base fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", coins);
}
'''
    language(custom, "custom_plan", "native-proof-index-block")


with case("a gate cannot select a scalar source query"):
    scalar = SOURCE.replace("coins.indices(N,Q)", "coins.index<N>()")
    deployment = json.loads(language(scalar, "scalar"))
    original = commands.run([compiler, "language-emit", "--source-format=zkc",
                             "--entry=sample::Proof", f"--module=sample={OUT / 'scalar.zkc'}"])
    path = OUT / "scalar.mlir"
    path.write_text(original)
    policy = deployment[2][1]
    policy[11] = [[policy[8][0][0], "8"]]
    selected = OUT / "scalar.policy"
    selected.write_text(json.dumps(policy))
    commands.run([compiler, "protocol-proof", path, selected], refuses="native-proof-gate-selection")

counted()
