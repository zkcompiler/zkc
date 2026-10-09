"""Runtime-count record and ragged-matrix clients use one generic data contract."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
fixtures = Path(__file__).parent / "fixtures/mathematical"
manifest = []
for family, public in [("batched-openings", ["2", "3", "4"]),
                       ("ragged-matrices", ["1", "2", "3"])]:
    source = fixtures / f"{family}.mlir"
    policy_data = ["zkc.native-proof-policy", "main", "P", "V", "0", "", "", public, []]
    policy = OUT / f"{family}.policy"
    policy.write_text(json.dumps(policy_data))
    for suffix, options in [("", ()), ("_plain", ("--no-simplify",)),
                            ("_release", ("--release-storage",))]:
        name = family + suffix
        with case(name):
            deployment = commands.run([compiler, "protocol-proof", source, policy, *options])
            envelope = json.loads(deployment)
            assert envelope[0] == "zkc.native-proof"
            assert json.loads(envelope[4])[0] == "zkc.program"
            assert envelope[2][5][0][2] == "zkc.native-data"
            assert "sequence<" in envelope[4]
            assert len(envelope[4]) < 40000, "runtime counts must not expand the program"
            (OUT / f"{name}.deployment").write_text(deployment)
            bundle = commands.run([compiler, "protocol-bundle", source, *options])
            (OUT / f"{name}.bundle").write_text(bundle)
            manifest.append(dict(name=name, family=family))
    with case(f"{family} refuses unknown policy tag"):
        malformed = list(policy_data)
        malformed[0] = "invalid.native-proof-policy"
        path = OUT / f"{family}_unknown-tag.policy"
        path.write_text(json.dumps(malformed))
        commands.run([compiler, "protocol-proof", source, path],
                     refuses="native-proof-policy")

standalone = OUT / "matrix.mlir"
standalone.write_text('''!m = tensor<?x?x!algebra.field<"bls12-381.fr">>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%matrix:!m,%rows:ui64,%columns:ui64):
   %received = protocol.exchange %matrix {sender="P",receiver="V",site="matrix"} : !m
   %r = "data.dim"(%received) {axis=0:i64} : (!m)->ui64
   %c = "data.dim"(%received) {axis=1:i64} : (!m)->ui64
   %r_ok = "data.index_equal"(%r,%rows) : (ui64,ui64)->i1
   %c_ok = "data.index_equal"(%c,%columns) : (ui64,ui64)->i1
   %ok = arith.andi %r_ok,%c_ok : i1
   "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!m,ui64,ui64)->i1,roles=["P","V"],input_roles=[["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }''')
policy_data = ["zkc.native-proof-policy", "main", "P", "V", "0", "", "", ["1", "2"], []]
policy = OUT / "matrix.policy"
policy.write_text(json.dumps(policy_data))
for suffix, options in [("", ()), ("_plain", ("--no-simplify",)), ("_release", ("--release-storage",))]:
    name = "matrix" + suffix
    with case(f"standalone {name}"):
        deployment = commands.run([compiler, "protocol-proof", standalone, policy, *options])
        assert json.loads(deployment)[2][5][0][2] == "zkc.native-data"
        (OUT / f"{name}.deployment").write_text(deployment)
        manifest.append(dict(name=name, family="matrix"))
with case("standalone matrix refuses unknown policy tag"):
    malformed = list(policy_data)
    malformed[0] = "invalid.native-proof-policy"
    policy = OUT / "matrix_unknown-tag.policy"
    policy.write_text(json.dumps(malformed))
    commands.run([compiler, "protocol-proof", standalone, policy],
                 refuses="native-proof-policy")

# A challenge echo makes absorption of the exact nested frame observable to an
# independent upstream transcript oracle in the runtime client.
observed = OUT / "observed.mlir"
observed.write_text('''!f = !algebra.field<"bls12-381.fr">
!s = !data.sequence<tensor<?x?x!f>>
!coins = !protocol.service_ref<"random.bls12-381.fr/1">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%data:!s,%coins:!coins):
   %received = protocol.exchange %data {sender="P",receiver="V",site="data"} : !s
   %r = "protocol.query"(%coins) {method="draw",owner="V",site="draw"} : (!coins)->!f
   %sent = protocol.exchange %r {sender="V",receiver="P",site="challenge"} : !f
   %echo = protocol.exchange %sent {sender="P",receiver="V",site="echo"} : !f
   %ok = algebra.field_equal %echo,%r : (!f,!f)->i1
   "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!s,!coins)->i1,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }''')
for i, suite in enumerate(["merlin3.bls12-381.fr64be/1", "spongefish0.7.4.keccak.bls12-381.fr64be/1"]):
    for suffix, options in [("", ()), ("_plain", ("--no-simplify",)), ("_release", ("--release-storage",))]:
        name = f"observed_{i}{suffix}"
        with case(name):
            policy = OUT / f"{name}.policy"
            policy.write_text(json.dumps(["zkc.native-proof-policy", "main", "P", "V", "0", suite, "1", [], [["draw", "challenge"]]]))
            deployment = commands.run([compiler, "protocol-proof", observed, policy, *options])
            (OUT / f"{name}.deployment").write_text(deployment)
            manifest.append(dict(name=name, family="observed"))

with case("an empty PCS sequence still requires deployment setup authority"):
    source = OUT / "missing-setup.mlir"
    source.write_text('''!s = !data.sequence<!pcs.object<"multilinear.kzg.bls12-381/1", "proof">>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%data:!s,%ok:i1):
   %received = protocol.exchange %data {sender="P",receiver="V",site="data"} : !s
   "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!s,i1)->i1,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }''')
    policy = OUT / "missing-setup.policy"
    policy.write_text(json.dumps(["zkc.native-proof-policy", "main", "P", "V", "0", "", "", ["1"], []]))
    commands.run([compiler, "protocol-proof", source, policy], refuses="native-proof-setup-coverage")

# Total data operations lower through checked native kernels. Invalid indexing
# remains an explicit local operation even when its result is unused.
probe = '''!s = !data.sequence<ui64>
module { "protocol.module"() ({
 "local.binding"() {sym_name="at",contract="sequence.at",arguments=["index"],implementation=""} : ()->()
 local.func @checked(%s:!s,%i:ui64)->ui64 attributes {logical_origin=["checked",[]]} {
   %unused = "data.exec.sequence_at"(%s,%i) {binding=@at,parameters=[],site="at"} : (!s,ui64)->ui64
   local.return %i : ui64
 }
 "protocol.func"() ({ ^entry(%i:ui64):
   %empty = "data.sequence_empty"() : ()->!s
   %one = "data.sequence_append"(%empty,%i) : (!s,ui64)->!s
   %n = "data.sequence_length"(%one) : (!s)->ui64
   %out = "protocol.local_call"(%one,%i) {callee=@checked,role="P",site="checked"} : (!s,ui64)->ui64
   "protocol.return"(%n,%out) : (ui64,ui64)->()
 }) {sym_name="main",function_type=(ui64)->(ui64,ui64),roles=["P"],input_roles=[["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }'''
with case("total operations and checked indexing"):
    path = OUT / "checked.mlir"
    path.write_text(probe)
    for suffix, options in [("", ()), ("_plain", ("--no-simplify",)), ("_release", ("--release-storage",))]:
        bundle = commands.run([compiler, "protocol-bundle", path, *options])
        assert "native/sequence.at" in json.loads(bundle)["candidate"]
        (OUT / f"checked{suffix}.bundle").write_text(bundle)
with case("affine element rejected at type formation"):
    commands.verified(probe.replace("!data.sequence<ui64>", '!data.sequence<!local.capability<"rng:bls12-381.fr">>'),
                      refuses="copyable and discardable")
with case("complete MLIR sequence type obeys structural depth"):
    element = "ui64"
    for _ in range(8):
        element = f"!data.sequence<{element}>"
    commands.verified(f"module attributes {{data.type = {element}}} {{}}")
    commands.verified(f"module attributes {{data.type = !data.sequence<{element}>}} {{}}",
                      refuses="binding-type-limit")
with case("copyable PCS elements do not grant total mathematical operations"):
    source = OUT / "non-total.mlir"
    source.write_text('''!s = !data.sequence<!pcs.object<"multilinear.kzg.bls12-381/1", "prover_key">>
module { "protocol.module"() ({
 "protocol.func"() ({
   %empty = "data.sequence_empty"() : ()->!s
   "protocol.return"(%empty) : (!s)->()
 }) {sym_name="main",function_type=()->!s,roles=["P"],input_roles=[],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }''')
    commands.run([compiler, "protocol-bundle", source], refuses="mathematical-formation")
(OUT / "manifest.json").write_text(json.dumps(manifest))
counted()
