"""Native common IR -> actual participant carrier, checked independently.

The small carrier evaluator uses field integers and generator coefficients for
group values. Native curve/codec execution is a separate example. It does not
share the projector's dependency or slicing implementation.
"""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records


ROOT = Path(__file__).parent / "fixtures/mathematical"
OUT = records()
commands = Commands(OUT)
FIELD = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def project(source, optimize=True, name=None):
    passes = ["--verify-each"]
    passes += ["--zkc-project-protocol"]
    if optimize:
        passes += ["--zkc-simplify-participant"]
    ir = commands.verified(source, None, *passes, "--zkc-lower-math")
    physical = commands.verified(ir, None, "--zkc-select-physical")
    carrier = commands.source("protocol-export", physical)
    if name:
        (OUT / (name + ".source.mlir")).write_text(source)
        (OUT / (name + ".logical.mlir")).write_text(ir)
        (OUT / (name + ".physical.mlir")).write_text(physical)
        (OUT / (name + ".json")).write_text(carrier)
    return json.loads(carrier), ir


class Stop(Exception):
    pass


def execute(carrier, role, inputs, replies=()):
    bindings = {b[0]: b[1] for b in carrier[1]}
    functions = {f[1]: f for f in carrier[3]}
    participant = next(p for p in carrier[4] if p[3] == role)
    assert len(inputs) == len(participant[5])
    env = dict(zip((p[0] for p in participant[5]), inputs))
    events = []
    incoming = iter(replies)

    def body(instructions, local):
        for op in instructions:
            kind = op[0]
            if kind in ("return", "yield"):
                return tuple(local[v] for v in op[1])
            if kind == "stop":
                raise Stop(op[2])
            if kind == "if":
                result = body(op[4] if local[op[2]] else op[5], local.copy())
                local.update(zip(op[6], result))
            elif kind == "local":
                function = functions[op[2]]
                values = [local[v] for v in op[3]]
                assert len(values) == len(function[2])
                arguments = dict(zip((p[0] for p in function[2]), values))
                local.update(zip(op[4], body(function[4], arguments)))
            elif kind == "op":
                contract = bindings[op[2]]
                if contract == "control.require":
                    # The installed backend exposes this as a backend failure,
                    # distinct from a source guard's explicit reject outcome.
                    if not local[op[4][0]]:
                        raise Stop("backend:rejected:require")
                    continue
                a, b = (local[v] for v in op[4])
                if contract in ("field.add", "curve.add"):
                    result = (a + b) % FIELD
                elif contract in ("field.mul", "curve.scale"):
                    result = (a * b) % FIELD
                elif contract in ("field.equal", "curve.equal"):
                    result = a == b
                elif contract == "bool.and":
                    result = a and b
                else:
                    raise AssertionError(contract)
                assert len(op[5]) == 1
                local[op[5][0]] = result
            elif kind == "send":
                events.append(("send", op[1], local[op[4]]))
            elif kind == "receive":
                try:
                    value = next(incoming)
                except StopIteration:
                    raise Stop("pending") from None
                events.append(("receive", op[1], value))
                local[op[4]] = value
            else:
                raise AssertionError(kind)
        raise AssertionError("carrier body has no terminator")

    try:
        return "returned", body(participant[7], env), events
    except Stop as stop:
        return str(stop), (), events


mixed = (ROOT / "mixed.mlir").read_text()
schnorr = (ROOT / "schnorr.mlir").read_text()
control = (ROOT / "control.mlir").read_text()
receives = (ROOT / "receives.mlir").read_text()

with case("acceptance maps identify independent role components"):
    family = '''module { "protocol.module"() ({
      relation.declare @check {kind="external", key="example/component", revision="1", signature=(i1) -> i1, purposes=["statement"]}
      "protocol.func"() ({
      ^entry(%x: i1):
        protocol.statement @check(%x) {selectors=["P"], acceptance=0 : i64} : i1
        %received = protocol.exchange %x {sender="P", receiver="V", site="acceptance"} : i1
        "protocol.return"(%received) : (i1) -> ()
      }) {sym_name="main", function_type=(i1) -> i1, roles=["P","V"], input_roles=[["P"]], output_roles=[["P","V"]]} : () -> ()
    }) {profile=#protocol.profile<protocol>} : () -> () }'''
    candidate, _ = project(family)
    assert execute(candidate, 'P', [True])[:2] == ('returned', (True,))
    assert execute(candidate, 'V', [], [False])[:2] == ('returned', (False,))

with case("mixed helper: per-result slices and all advertised ports"):
    candidate, _ = project(mixed, name="mixed")
    assert {p[3]: len(p[5]) for p in candidate[4]} == {"Alice": 2, "Bob": 1, "Observer": 1}
    for a in [0, 1, 19, FIELD-1]:
        for w in [0, 7, FIELD-1]:
            assert execute(candidate, "Alice", [a,w])[:2] == ("returned", (2*a % FIELD, 2*a*w % FIELD))
            # Shared does not imply equal: Bob has a different component.
            assert execute(candidate, "Bob", [(a+1) % FIELD])[:2] == ("returned", (2*(a+1) % FIELD,))
    assert execute(candidate, "Observer", [False])[:2] == ("returned", ())

with case("multiple common programs share one checked helper closure"):
    # Reuse the same private helper under independently named protocol entries.
    function_start = mixed.index('  "protocol.func"')
    function_end = mixed.index('}) {profile=')
    other = mixed[function_start:function_end].replace('sym_name="main"', 'sym_name="other"')
    combined = mixed[:function_end]+other+mixed[function_end:]
    carrier, _ = project(combined)
    assert len(carrier[4]) == 6
    assert len(carrier[5]) == 2
    assert {entry[1] for entry in carrier[5]} == {'main', 'other'}

with case("helper expansion precedes scoped CSE"):
    helper_call = next(line for line in mixed.splitlines() if '%h:2 = func.call' in line)
    repeated = mixed.replace(helper_call, helper_call+'\n'+helper_call.replace('%h:2', '%j:2'))
    repeated = repeated.replace('"protocol.return"(%h#0, %h#1)', '"protocol.return"(%j#0, %h#1)')
    prepared = commands.verified(repeated, None, '--zkc-prepare-protocol')
    assert 'func.call' not in prepared
    assert '#protocol.profile<protocol>' in prepared
    assert commands.verified(prepared, None, '--zkc-prepare-protocol') == prepared
    candidate, _ = project(repeated, optimize=False)
    # Alice computes add/mul once; Bob computes add once. The two helper calls
    # demand different results but share their common addition after expansion.
    assert sum(op[0] == 'op' for f in candidate[3] for op in f[4]) == 3
    assert execute(candidate, 'Alice', [3, 7])[:2] == ('returned', (6, 42))

with case("Schnorr generated carriers use actual commitment/challenge/response"):
    candidate, ir = project(schnorr, name="schnorr")
    assert "protocol.projection" in ir and "schnorr_relation" in ir
    for x in [1, 13, FIELD-1]:
        for nonce in [0, 17]:
            for challenge in [0, 19]:
                response = (nonce + challenge*x) % FIELD
                p = execute(candidate, "Alice", [1,x,x,nonce], [challenge])
                assert p == ("returned", (), [("send","commitment",nonce), ("receive","challenge",challenge), ("send","response",response)])
                assert execute(candidate, "Bob", [1,x,challenge], [nonce,response])[:2] == ("returned", (True,))
                assert execute(candidate, "Bob", [1,x,challenge], [nonce,(response+1)%FIELD])[:2] == ("returned", (False,))
                assert execute(candidate, "Bob", [1,x,challenge], [(nonce+1)%FIELD,response])[:2] == ("returned", (False,))

with case("guard stops locally; deferred false still sends; peer stays open"):
    guarded, _ = project(control, name="control")
    deferred, _ = project((ROOT / "deferred.mlir").read_text(), name="deferred")
    assert all(binding[1] != "control.require" for binding in guarded[1])
    assert execute(guarded, "Bob", [False,3,7]) == ("reject", (), [("send","selected",7)])
    assert execute(deferred, "Bob", [False,3,7]) == ("returned", (False,7,3), [("send","selected",7),("send","after_guard",3)])
    assert execute(guarded, "Bob", [True,3,7]) == ("returned", (True,3,3), [("send","selected",3),("send","after_guard",3)])
    assert execute(guarded, "Alice", [29,31], [7]) == ("pending", (), [("receive","selected",7)])

with case("equal-looking receives remain fresh after canonicalization and CSE"):
    candidate, ir = project(receives, name="receives")
    assert ir.count('"protocol.receive"()') == 2
    assert execute(candidate, "Alice", [3]) == ("returned", (6,), [("send","first",3),("send","second",3)])
    assert execute(candidate, "Bob", [], [5,11]) == ("returned", (16,), [("receive","first",5),("receive","second",11)])

with case("renaming roles and preserving statement/acceptance interface"):
    renamed = schnorr.replace('"Alice"','"Sender"').replace('"Bob"','"Checker"')
    candidate, ir = project(renamed)
    assert execute(candidate,"Checker",[1,13,19],[17,264])[:2] == ("returned",(True,))
    assert 'selectors = ["Checker", "Checker", "Sender"]' in ir
    assert 'acceptance = 0' in ir
    assert [len(p[5]) for p in candidate[4]] == [4,3]

with case("ordinary CSE merges total values and retains explicit restriction"):
    source = receives.replace('%one = protocol.exchange', '%double = algebra.field_add %a, %a : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">\n%duplicate = algebra.field_add %a, %a : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">\n%narrow = protocol.restrict_roles %duplicate {roles=["Alice"]} : !algebra.field<"bls12-381.fr">\n%one = protocol.exchange').replace('protocol.exchange %a','protocol.exchange %double',1).replace('protocol.exchange %a','protocol.exchange %narrow',1)
    optimized = commands.verified(source, None, "--canonicalize", "--cse")
    assert optimized.count("algebra.field_add") == 2  # merged duplicate + final sum
    assert optimized.count("protocol.restrict_roles") == 1
    candidate, _ = project(source)
    assert execute(candidate,"Alice",[3])[1] == (12,)

with case("projection exposes sender component equality before lowering"):
    field = '!algebra.field<"bls12-381.fr">'
    alias = f'''module {{ "protocol.module"() ({{
      "protocol.func"() ({{
      ^entry(%x: {field}):
        %received = protocol.exchange %x {{sender="P", receiver="V", site="message"}} : {field}
        %a = algebra.field_add %x, %x : ({field}, {field}) -> {field}
        %b = algebra.field_add %received, %received : ({field}, {field}) -> {field}
        "protocol.return"(%a, %b) : ({field}, {field}) -> ()
      }}) {{sym_name="main", function_type=({field}) -> ({field}, {field}), roles=["P", "V"], input_roles=[["P"]], output_roles=[["P"], ["P", "V"]]}} : () -> ()
    }}) {{profile=#protocol.profile<protocol>}} : () -> () }}'''
    projected = commands.verified(alias, None, '--zkc-project-protocol')
    assert '#protocol.profile<participant>' in projected
    assert 'local.func' not in projected and 'local.binding' not in projected
    assert projected.count('algebra.field_add') == 3
    optimized = commands.verified(projected, None, '--zkc-simplify-participant')
    assert optimized.count('algebra.field_add') == 2
    assert optimized.count('"protocol.receive"()') == 1
    assert commands.verified(optimized, None, '--zkc-simplify-participant') == optimized
    candidate, _ = project(alias)
    assert execute(candidate, 'P', [3])[:2] == ('returned', (6, 6))
    assert execute(candidate, 'V', [], [11])[:2] == ('returned', (22,))
    commands.source('protocol-export', projected, refuses='interactive-module')
    commands.verified(alias, 'mathematical-lowering-profile', '--zkc-lower-math')
    commands.verified(projected, 'mathematical-module', '--zkc-project-protocol')

# Move the statement after the computed value so this checks statement
# formation rather than merely failing MLIR dominance.
lines = schnorr.splitlines()
statement_line = next(line for line in lines if line.startswith('protocol.statement'))
lines.remove(statement_line)
lines.insert(next(i for i,line in enumerate(lines) if '"protocol.return"' in line),
             statement_line.replace('%x)', '%cx)'))
computed_statement = '\n'.join(lines)

# These are source admission tests: malformed unused code must fail before a
# generic transform has the opportunity to erase it.
negative = [
    ("private helper result exposed to Bob", mixed.replace('output_roles=[["Alice","Bob"],["Alice"]]', 'output_roles=[["Alice","Bob"],["Alice","Bob"]]'), "mathematical-formation"),
    ("unknown role", mixed.replace('input_roles=[["Alice","Bob"]', 'input_roles=[["Unknown","Bob"]'), "mathematical-formation"),
    ("duplicate roster", mixed.replace('roles=["Alice", "Bob", "Observer"]','roles=["Alice", "Alice", "Observer"]'), "mathematical-formation"),
    ("empty role set", mixed.replace('[["Alice","Bob"],["Alice"],["Observer"]]', '[["Alice","Bob"],[],["Observer"]]'), "mathematical-formation"),
    ("disjoint helper dependency", mixed.replace('[["Alice","Bob"],["Alice"],["Observer"]]', '[["Bob"],["Alice"],["Observer"]]'), "mathematical-formation"),
    ("private select condition", control.replace('input_roles=[["Bob"]', 'input_roles=[["Alice"]'), "mathematical-formation"),
    ("foreign unavailable send", receives.replace('sender="Alice",receiver="Bob"','sender="Bob",receiver="Alice"',1), "mathematical-formation"),
    ("duplicate action occurrence", receives.replace('site="second"','site="first"'), "mathematical-formation"),
    ("statement binds computed value", computed_statement, "mathematical-formation"),
    ("statement loses acceptance", schnorr.replace('acceptance=0 : i64','acceptance=1 : i64'), "mathematical-formation"),
    ("missing relation", schnorr.replace('protocol.statement @schnorr_relation','protocol.statement @absent'), "mathematical-statement"),
]
F = '!algebra.field<"bls12-381.fr">'
common = mixed[mixed.index('  "protocol.func"'):]
recursive = f"""module {{
"protocol.module"() ({{
func.func private @helper(%a: {F}, %w: {F}) -> ({F}, {F}) {{
  %h:2 = func.call @helper(%a, %w) : ({F}, {F}) -> ({F}, {F})
  return %h#0, %h#1 : {F}, {F}
}}
""" + common
opaque = f'module {{ \"protocol.module\"() ({{ func.func private @helper({F}, {F}) -> ({F}, {F})\n' + common
empty = 'module { "protocol.module"() ({ "protocol.func"() ({}) {sym_name="empty", function_type=() -> (), roles=["A"], input_roles=[], output_roles=[]} : () -> () }) {profile=#protocol.profile<protocol>} : () -> () }'
negative += [
    ("empty common region", empty, "mathematical-formation"),
    ("recursive helper", recursive, "mathematical-formation"),
    ("opaque helper", opaque, "mathematical-formation"),
    ("finite legacy field is outside this profile", mixed.replace('bls12-381.fr','f7'), "mathematical-formation"),
    ("called helper must be private", mixed.replace('private @helper','@helper'), "mathematical-formation"),
    ("unavailable explicit restriction", receives.replace('%one = protocol.exchange', f'%n = protocol.restrict_roles %a {{roles=["Bob"]}} : {F}\n%one = protocol.exchange'), "mathematical-formation"),
]
with case("nested pass verification and module metadata preservation"):
    decorated = mixed.replace('module {', 'module attributes {test.tag="retained"} {',1)
    optimized = commands.verified(decorated, None, '--pass-pipeline=builtin.module(protocol.module(func.func(canonicalize),protocol.func(cse)))')
    _, ir = project(optimized)
    assert 'test.tag = "retained"' in ir

with case("statement relation stays live before projection"):
    optimized = commands.verified(schnorr, None, '--symbol-dce')
    assert '@schnorr_relation' in optimized
    _, ir = project(optimized)
    assert 'relation_type =' in ir

with case("deep SSA demand uses an iterative traversal"):
    terms = []
    previous = '%a'
    for i in range(3000):
        terms.append(f'%chain{i} = algebra.field_add {previous}, %a : ({F}, {F}) -> {F}')
        previous = f'%chain{i}'
    source = receives.replace('%one = protocol.exchange', '\n'.join(terms)+'\n%one = protocol.exchange')
    source = source.replace('protocol.exchange %a', f'protocol.exchange {previous}',1)
    candidate, _ = project(source, optimize=False)
    assert execute(candidate,'Alice',[3])[1] == (9006,)

# Public definitions are part of a module's callable interface even when the
# mathematical entry does not call them.
public_unused = mixed.replace('}) {profile=', 'func.func @unrelated() { return }\n}) {profile=')
negative.append(("uncalled public definition", public_unused, "mathematical-formation"))

def helper_graph(depth, branching):
    definitions = []
    for level in range(depth):
        calls = ''
        result = '%arg'
        if level+1 < depth:
            for branch in range(branching):
                calls += f'%v{branch} = func.call @h{level+1}(%arg) : ({F}) -> {F}\n'
            result = '%v0'
        definitions.append(f'func.func private @h{level}(%arg: {F}) -> {F} {{\n{calls}return {result} : {F}\n}}')
    source = receives.replace('"protocol.module"() ({','"protocol.module"() ({\n'+'\n'.join(definitions),1)
    source = source.replace('%one = protocol.exchange',f'%h = func.call @h0(%a) : ({F}) -> {F}\n%one = protocol.exchange')
    return source.replace('protocol.exchange %a','protocol.exchange %h',1)

unused_bad = mixed.replace('}) {profile=', 'func.func private @unused(%x: i32) -> i32 { return %x : i32 }\n}) {profile=')
unused_recursive = mixed.replace('}) {profile=', 'func.func private @unused() { func.call @unused() : () -> () return }\n}) {profile=')
negative += [
    ("unused unsupported helper", unused_bad, "mathematical-formation"),
    ("unused recursive helper", unused_recursive, "mathematical-formation"),
    ("helper depth admission bound", helper_graph(66,1), "mathematical-analysis-limit"),
    ("expanded helper work bound", helper_graph(17,2), "mathematical-analysis-limit"),
]

wide_arguments = ', '.join(f'%argument{i}: i1' for i in range(10000))
wide_helper = mixed.replace('}) {profile=', f'func.func private @wide({wide_arguments}) {{ return }}\n}}) {{profile=')
unused_intermediate = (mixed.replace('return %s, %t', 'return %a, %w')
    .replace('input_roles=[["Alice","Bob"]', 'input_roles=[["Bob"]')
    .replace('output_roles=[["Alice","Bob"]', 'output_roles=[["Bob"]'))
conflict = 'relation.declare @conflicting {kind="external", key="example/schnorr", revision="1", signature=(!algebra.group<"bls12-381.g1">, !algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> i1, purposes=["statement", "statement", "witness"]}'
conflicting_relation = schnorr.replace('}) {profile=', conflict+'\n}) {profile=')
negative += [
    ("wide helper dependency work bound", wide_helper, "mathematical-analysis-limit"),
    ("unused unavailable helper intermediate", unused_intermediate, "mathematical-formation"),
    ("unused conflicting relation schema", conflicting_relation, "relation-declaration-conflict"),
    ("unknown total operation attribute", receives.replace('algebra.field_add %one, %two :', 'algebra.field_add %one, %two {trusted=true} :'), "mathematical-formation"),
    ("unknown protocol attribute", receives.replace('sym_name="main"', 'sym_name="main", trusted=true'), "mathematical-formation"),
]
for attribute in ['arg_attrs=[{test.assumption=true}, {}]', 'res_attrs=[{}, {}]', 'no_inline']:
    negative.append((f"call refuses {attribute.split('=')[0]}",
        mixed.replace('func.call @helper(%a, %w) :', f'func.call @helper(%a, %w) {{{attribute}}} :'),
        "mathematical-formation"))
negative += [
    ("common function in wrong profile", mixed.replace('#protocol.profile<protocol>', '#protocol.profile<exec>'), "mathematical-formation"),
    ("common function argument annotations", mixed.replace('sym_name="main"', 'sym_name="main", arg_attrs=[]'), "mathematical-formation"),
]

# A shared helper's small static body can still require expensive availability
# intersections at many calls. The replay budget is independent of expansion.
arity = 128
arguments = ', '.join(f'%x{i}: {F}' for i in range(arity))
chain = '\n'.join(f'%s{i} = algebra.field_add '+('%x0' if i == 1 else f'%s{i-1}')+f', %x{i} : ({F}, {F}) -> {F}' for i in range(1, arity))
helper = f'func.func private @prefix({arguments}) -> {F} {{\n{chain}\nreturn %s{arity-1} : {F}\n}}'
roster = '['+', '.join(f'"role{i}"' for i in range(1024))+']'
actuals = ', '.join('%a' for _ in range(arity))
types = ', '.join(F for _ in range(arity))
calls = '\n'.join(f'%c{i} = func.call @prefix({actuals}) : ({types}) -> {F}' for i in range(16))
replay_stress = f'''module {{ "protocol.module"() ({{
{helper}
"protocol.func"() ({{
^entry(%a: {F}):
{calls}
"protocol.return"(%a) : ({F}) -> ()
}}) {{sym_name="main", function_type=({F}) -> {F}, roles={roster}, input_roles=[{roster}], output_roles=[["role0"]]}} : () -> ()
}}) {{profile=#protocol.profile<protocol>}} : () -> () }}'''
negative.append(("summary availability replay budget", replay_stress, "mathematical-analysis-limit"))

# Role expansion is bounded before participant allocation, separately from
# the common helper/availability budgets.
expansion_roles = '['+', '.join(f'"R{i}"' for i in range(120))+']'
expansion_chain = '\n'.join(f'%s{i} = algebra.field_add '+('%x' if i == 0 else f'%s{i-1}')+f', %x : ({F}, {F}) -> {F}' for i in range(1000))
expansion = f'''module {{ "protocol.module"() ({{
"protocol.func"() ({{
^entry(%x: {F}):
{expansion_chain}
"protocol.return"(%s999) : ({F}) -> ()
}}) {{sym_name="main", function_type=({F}) -> {F}, roles={expansion_roles}, input_roles=[{expansion_roles}], output_roles=[{expansion_roles}]}} : () -> ()
}}) {{profile=#protocol.profile<protocol>}} : () -> () }}'''
negative.append(("bounded role expansion before allocation", expansion, "mathematical-projection-limit"))

unwrapped = (mixed.replace('"protocol.module"() ({', '', 1)
    .replace('}) {profile=#protocol.profile<protocol>} : () -> ()', ''))
negative.append(("common function outside protocol unit", unwrapped, "parent"))

for label, source, code in negative:
    with case(label):
        commands.verified(source, code, "--canonicalize", "--cse", "--zkc-project-protocol", "--zkc-lower-math")

print(f"Mathematical projection: {counted()} cases; evidence: {OUT}")

with case("scoped preparation removes only an admitted unused role view"):
    field = '!algebra.field<"bls12-381.fr">'
    unused_view = receives.replace('%one = protocol.exchange',
        f'%unused = protocol.restrict_roles %a {{roles=["Alice"]}} : {field}\n%one = protocol.exchange')
    prepared = commands.verified(unused_view, None, '--zkc-prepare-protocol')
    assert 'protocol.restrict_roles' not in prepared
    assert prepared.count('protocol.exchange') == 2
