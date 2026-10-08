"""Nominal records and dynamic sum payloads through the generic native compiler."""
import json
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
source = Path(__file__).parent / "fixtures/mathematical/structured-message.mlir"
manifest = []
for i, suite in enumerate(["merlin3.bls12-381.fr64be/1", "spongefish0.7.4.keccak.bls12-381.fr64be/1"]):
    for suffix, options in [("", ()), ("_plain", ("--no-simplify",)), ("_release", ("--release-storage",))]:
        name = f"message_{i}{suffix}"
        with case(name):
            policy = OUT / f"{name}.policy"
            policy.write_text(json.dumps(["zkc.native-proof-policy/4", "main", "Alice", "Bob", "0", suite, "4", ["0", "2", "6", "7", "8"], [["draw_challenge", "challenge"]]]))
            result = commands.run([compiler, "protocol-proof", source, policy, *options])
            envelope = json.loads(result)
            assert envelope[0] == "zkc.native-proof/4"
            assert envelope[2][0] == "zkc.native-proof-descriptor/4"
            assert json.loads(envelope[4])[0] == "zkc.program/1"
            (OUT / f"{name}.deployment").write_text(result)
            manifest.append(dict(name=name))
for version in (1, 2, 3):
    with case(f"policy {version} refuses structured message"):
        selected = json.loads((OUT / "message_0.policy").read_text())
        selected[0] = f"zkc.native-proof-policy/{version}"
        policy = OUT / f"old_{version}.policy"
        policy.write_text(json.dumps(selected))
        commands.run([compiler, "protocol-proof", source, policy], refuses="native-proof-policy")
# Standalone numeric collections use the same new frame family and carrier.
# Wrapping them in a record is not required to select the correct boundary.
for name, ty in [("vector", "tensor<?x!algebra.field<\"bls12-381.fr\">>"),
                 ("groups", "tensor<?x!algebra.group<\"bls12-381.g1\">>"),
                 ("indices", "tensor<?xui64>")]:
    with case(f"standalone {name}"):
        text = f'''module {{ "protocol.module"() ({{
          "protocol.func"() ({{ ^entry(%data:{ty}, %ok:i1):
            %received = protocol.exchange %data {{site="data", sender="Alice", receiver="Bob"}} : {ty}
            "protocol.return"(%ok) : (i1)->()
          }}) {{sym_name="main", function_type=({ty},i1)->i1,
                roles=["Alice","Bob"], input_roles=[["Alice"],["Bob"]],
                output_roles=[["Bob"]]}} : ()->()
        }}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''
        fixture = OUT / f"{name}.mlir"
        fixture.write_text(text)
        policy = OUT / f"{name}.policy"
        policy.write_text(json.dumps(["zkc.native-proof-policy/4", "main", "Alice", "Bob", "0", "", "", ["1"], []]))
        deployment = commands.run([compiler, "protocol-proof", fixture, policy])
        envelope = json.loads(deployment)
        (OUT / f"{name}.deployment").write_text(deployment)
        manifest.append(dict(name=name, standalone=name))
        assert json.loads(envelope[4])[0] == "zkc.program/1"
        assert envelope[2][5][0][2] == "zkc.native-data/1"
(OUT / "manifest.json").write_text(json.dumps(manifest))
counted()
