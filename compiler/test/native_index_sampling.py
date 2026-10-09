"""UniformIndex queries: source, formation, carrier and Fiat-Shamir boundaries.

The generated deployments feed the independent native driver
`native_index_sampling`, which proves, verifies and replays their transcripts.
"""
import json
import re
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import canonical_program, compiler, records

OUT = records()
commands = Commands(OUT)
CLIENT = Path(__file__).parent / "fixtures/language/index_sampling.zkc"
SUITE = "merlin3.koala-bear.ext8-binomial3.rejection31le/0"
SERVICE = '!protocol.service_ref<"random.koala-bear.ext8-binomial3/0">'
manifest = []


def language(subcommand, source, entry, *options, refuses=None, name="source"):
    path = OUT / f"{name}.zkc"
    path.write_text(source)
    return commands.run([compiler, subcommand, "--source-format=zkc",
                         f"--entry=sample::{entry}", f"--module=sample={path}",
                         *options], refuses=refuses)


PICK = '''module sample;
domain E = field("koala-bear.ext8-binomial3");
domain Fr = field("bls12-381.fr");
protocol Pick roles(P, V)(coins: Random<E> @V)
    -> (p: index @P, v: index @V) {
  let v = coins.index<8>();
  let p = send V -> P(v);
  return (p = p, v = v);
}
entry Demo = Pick;
'''

with case("a static power-of-two domain emits a constant bound and an index query"):
    emitted = language("language-emit", PICK, "Demo", name="pick")
    assert re.search(r'"data.index"\(\) <\{value = "8"\}> : \(\) -> ui64', emitted)
    assert 'method = "index"' in emitted and 'method = "draw"' not in emitted
    largest = language("language-emit", PICK.replace("index<8>", "index<pow2(63)>"),
                       "Demo", name="pick_largest")
    assert 'value = "9223372036854775808"' in largest
    language("language-check", PICK.replace("index<8>", "index<1>"), "Demo",
             name="pick_single")

GENERIC = '''module sample;
domain E = field("koala-bear.ext8-binomial3");
protocol Pick<F: Field + Share + Wire, N: nat> roles(P, V)(coins: Random<F> @V) -> (v: index @V) REQUIRE {
  let v = coins.index<N>();
  return (v = v);
}
protocol Run roles(P, V)(coins: Random<E> @V) -> (v: index @V) {
  let v = Pick<E, SIZE>(coins);
  return (v = v);
}
entry Demo = Run;
'''

with case("explicit generic contracts retain the IndexRandomness requirement"):
    assumed = GENERIC.replace("REQUIRE", "where zkc::random::IndexRandomness(F)")
    language("language-check", assumed.replace("SIZE", "pow2(4)"), "Demo",
             name="generic_assumed")
    language("language-check", GENERIC.replace("REQUIRE", "where ()").replace("SIZE", "16"),
             "Demo", name="generic_missing", refuses="source.service")

with case("an omitted generic contract infers IndexRandomness"):
    language("language-check", GENERIC.replace("REQUIRE", "").replace("SIZE", "16"),
             "Demo", name="generic_inferred")

with case("index results constrain unannotated arithmetic and service aliases"):
    aliased = PICK.replace("let v = coins.index<8>();",
                           "let alias = coins; let v = increment(alias.index<8>());")
    aliased += "fn increment(value: index) { return 1 + value; }\n"
    language("language-check", aliased, "Demo", name="index_alias_inference")

with case("a selected generic domain must close to a power of two"):
    language("language-check",
             GENERIC.replace("REQUIRE", "where zkc::random::IndexRandomness(F)")
             .replace("SIZE", "12"),
             "Demo", name="generic_twelve", refuses="source.service")

for name, old, new in [
    ("non-power-of-two domain", "index<8>", "index<3>"),
    ("empty domain", "index<8>", "index<0>"),
    ("missing domain", "index<8>()", "index()"),
    ("two domains", "index<8>", "index<8, 8>"),
    ("data argument", "index<8>()", "index<8>(1)"),
    ("type domain", "index<8>", "index<E>"),
    ("field without index randomness", "Random<E>", "Random<Fr>"),
]:
    with case(f"source refuses {name}"):
        language("language-check", PICK.replace(old, new), "Demo",
                 name=name.replace(" ", "_"), refuses="source.service")

with case("the index method is a method call only"):
    language("language-check", PICK.replace("coins.index<8>()", "coins.index<8>"),
             "Demo", name="index_projection", refuses="source.syntax")

FORMED = f'''module {{ "protocol.module"() ({{
  "protocol.func"() ({{
  ^entry(%n: ui64, %r: {SERVICE}):
    %b = "data.index"() {{value = "8"}} : () -> ui64
    %x = "protocol.query"(%r, %b) {{method = "index", owner = "V", site = "sample"}} : ({SERVICE}, ui64) -> ui64
    "protocol.return"(%x) : (ui64) -> ()
  }}) {{sym_name = "main", function_type = (ui64, {SERVICE}) -> (ui64), roles = ["V"], input_roles = [["V"], ["V"]], output_roles = [["V"]]}} : () -> ()
}}) {{profile = #protocol.profile<protocol>}} : () -> () }}'''

with case("formation admits the smallest and largest domains"):
    for value in ("1", "9223372036854775808"):
        commands.verified(FORMED.replace('value = "8"', f'value = "{value}"'), None)

for name, old, new in [
    ("non-power-of-two bound", 'value = "8"', 'value = "3"'),
    ("zero bound", 'value = "8"', 'value = "0"'),
    ("noncanonical bound", 'value = "8"', 'value = "08"'),
    ("bound above 2^63", 'value = "8"', 'value = "18446744073709551616"'),
    ("runtime bound", '"protocol.query"(%r, %b)', '"protocol.query"(%r, %n)'),
    ("service without index randomness", '"random.koala-bear.ext8-binomial3/0"', '"random.bls12-381.fr/0"'),
    ("field result", '(ui64) -> ()', '(!algebra.field<"koala-bear.ext8-binomial3">) -> ()'),
    ("missing bound", '"protocol.query"(%r, %b)', '"protocol.query"(%r)'),
]:
    with case(f"formation refuses {name}"):
        mutated = FORMED.replace(old, new)
        if name == "field result":
            mutated = mutated.replace(f"({SERVICE}, ui64) -> ui64", f'({SERVICE}, ui64) -> !algebra.field<"koala-bear.ext8-binomial3">')
            mutated = mutated.replace("-> (ui64), roles", '-> (!algebra.field<"koala-bear.ext8-binomial3">), roles')
        if name == "missing bound":
            mutated = mutated.replace(f"({SERVICE}, ui64) -> ui64", f"({SERVICE}) -> ui64")
        commands.verified(mutated, "mathematical-formation")

with case("the program carrier keeps the bound as the query's data input"):
    logical = commands.verified(FORMED, None, "--zkc-project-protocol",
                                "--zkc-simplify-participant", "--zkc-lower-math")
    physical = commands.verified(logical, None, "--zkc-select-physical=release-storage=true")
    carrier = json.loads(commands.source("protocol-export", physical))
    (OUT / "carrier.json").write_text(json.dumps(carrier))
    role = carrier[3][0]
    queries = [op for op in role[6] if op[0] == "query"]
    assert len(queries) == 1 and queries[0][3] == "index" and len(queries[0][4]) == 1
    canonical_program(commands, json.dumps(carrier))
    for label, mutate, reason in [
        ("missing bound input", lambda q: q.__setitem__(4, []), "service-query-signature"),
        ("draw with a bound", lambda q: q.__setitem__(3, "draw"), "service-query-signature"),
        ("unknown method", lambda q: q.__setitem__(3, "sample"), "service-query-signature"),
    ]:
        changed = json.loads(json.dumps(carrier))
        mutate(next(op for op in changed[3][0][6] if op[0] == "query"))
        canonical_program(commands, json.dumps(changed), refuses=reason)

ECHO = '''module sample;
domain E = field("koala-bear.ext8-binomial3");
fn same(a: index, b: index) -> bool { return a == b; }
fn agree(a: E, b: E) -> bool { return a == b; }
fn yes() -> bool { return true; }
// P returns each derived field challenge and position. V compares them with
// its own samples, so a prover/verifier transcript disagreement is rejected.
protocol Echo<N: nat, Max: nat> roles(P, V)(rounds: index @(P,V),
     coins: Random<E> @V) -> (accepted: bool @V) {
  for i in 0..rounds roles(P,V) max Max {
    let c = coins.draw();
    let cp = send V -> P(c);
    let q = coins.index<N>();
    let qp = send V -> P(q);
    let ce = send P -> V(cp);
    let qe = send P -> V(qp);
    let c_ok @V = agree(c, ce);
    let q_ok @V = same(q, qe);
    require @V c_ok;
    require @V q_ok;
  }
  let accepted @V = yes();
  return (accepted = accepted);
}
entry Proof = Echo<pow2(5), 4> {
  prover P;
  verifier V;
  public { rounds };
  accept accepted;
  construction fiat_shamir("SUITE") {
    derive coins;
  }
}
'''.replace("SUITE", SUITE)

with case("derived transcripts carry typed index events with their bound"):
    for suffix, flags in [("", []), ("_plain", ["--no-simplify"]),
                          ("_release", ["--release-storage"])]:
        name = "echo" + suffix
        deployment = language("language-bundle", ECHO, "Proof", *flags, name=name)
        envelope = json.loads(deployment)
        assert envelope[0] == "zkc.native-proof/0"
        policy, events = envelope[2][1], envelope[2][3]
        assert policy[5] == SUITE and len(policy[8]) == 2
        assert [e[0] for e in events] == ["query", "message", "index", "message", "message", "message"]
        assert events[2][2] == "32" and all(len(e) == 2 for i, e in enumerate(events) if i != 2)
        (OUT / f"{name}.deployment").write_text(deployment)
        manifest.append({"name": name, "bound": 32, "rounds": 3})
    (OUT / "echo.policy").write_text(json.dumps(policy))
    original = language("language-emit", ECHO, "Proof", name="echo_original")
    (OUT / "echo.mlir").write_text(original)

with case("the explicit policy reconstructs and checks the same candidate"):
    source, policy = OUT / "echo.mlir", OUT / "echo.policy"
    candidate = commands.run([compiler, "protocol-construct-proof", source, policy])
    (OUT / "echo.candidate.mlir").write_text(candidate)
    commands.run([compiler, "protocol-check-proof", source, policy, OUT / "echo.candidate.mlir"])
    constant = re.search(r'"algebra.exec.index_constant"\(\) <\{[^}]*parameters = \["32"\]', candidate)
    assert constant, "the helper materializes its static bound"
    for value, reason in [("64", "native-proof-correspondence"), ("3", "mathematical-projection")]:
        changed = OUT / f"echo.candidate.{value}.mlir"
        changed.write_text(candidate.replace('parameters = ["32"]', f'parameters = ["{value}"]'))
        commands.run([compiler, "protocol-check-proof", source, policy, changed], refuses=reason)


def mutate_original(name, edit, reason):
    text = (OUT / "echo.mlir").read_text()
    index = re.search(r'(%\d+) = "protocol.query"\((%arg\d+), (%\d+)\) <\{method = "index"', text)
    draw = re.search(r'(%\d+) = "protocol.query"\((%arg\d+)\) <\{method = "draw"', text)
    assert index and draw
    changed = OUT / f"echo.{name}.mlir"
    changed.write_text(edit(text, index, draw))
    commands.run([compiler, "protocol-proof", changed, OUT / "echo.policy"], refuses=reason)


def insert(text, before, lines):
    """Insert generic operations immediately before the first matching line."""
    rows = text.splitlines()
    at = next(i for i, row in enumerate(rows) if before in row)
    rows[at:at] = lines
    return "\n".join(rows) + "\n"


def extra_query(service, site):
    return [f'%{site}_bound = "data.index"() <{{value = "32"}}> : () -> ui64',
            f'%{site} = "protocol.query"({service}, %{site}_bound) <{{method = "index", owner = "V", site = "{site}"}}> : ({SERVICE}, ui64) -> ui64']


for name, edit, reason in [
    # A different value cannot stand in for the sampled index at the producer.
    ("transformed delivery",
     lambda t, i, d: t.replace(f'"protocol.exchange"({i[1]})', f'"protocol.exchange"({i[3]})'),
     "native-proof-reverse-message"),
    # A selected query must be delivered before the next selected query.
    ("outstanding draw",
     lambda t, i, d: insert(t, f'"protocol.exchange"({d[1]})', extra_query(d[2], "early")),
     "native-proof-prefix"),
    # A query outside the selected ordered pairs cannot be derived.
    ("unselected index",
     lambda t, i, d: insert(t, '"protocol.yield"', extra_query(i[2], "late")),
     "native-proof-draw-selection"),
]:
    with case(f"construction refuses {name}"):
        mutate_original(name.replace(" ", "_"), edit, reason)

with case("the maintained spot-check client constructs index transitions in a loop"):
    path = OUT / "client.zkc"
    path.write_text(CLIENT.read_text())
    deployment = commands.run([compiler, "language-bundle", "--source-format=zkc",
                               "--entry=sample::Proof", f"--module=sample={path}"])
    events = json.loads(deployment)[2][3]
    assert [e[0] for e in events].count("index") == 1
    assert next(e for e in events if e[0] == "index")[2] == "8"

(OUT / "manifest.json").write_text(json.dumps(manifest))
counted()
