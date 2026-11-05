"""Execute selected total Boolean work and ordinary enum formation natively."""

import hashlib
import json

import pytest

from entry import Entry, joint_artifact, joint_execution, joint_package


PRELUDE = '''module computation;
domain F=field("koala-bear");
domain fn range(lo:index,hi:index)->domain<index>=domain("range");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn expensive(n:index,x:F)->bool{return fold(range(0,n),x,fn(s,i)=>s+x)==x;}
enum Choice{Empty(),Value(bool)}
math fn unwrap(x:Choice)->bool{return match x{Empty()=>{false},Value(v)=>{v}};}
math fn enum_math(a:bool)->bool{
 let empty=Choice::Empty();
 return match Choice::Value(a){Empty()=>{true},Value(v)=>{
   match empty{Empty()=>{v},Value(w)=>{w}}
 }};
}
'''


def compile_source(toolchain, journal, directory, source, flags=(), layout=False):
    path = directory / "computation.zkc"
    path.write_text(source)
    package = directory / "computation.zkpkg"
    package.write_text(journal.run([
        toolchain.compiler, "language-package",
        f'--source-format={"zkc-layout" if layout else "zkc"}',
        f"--module=computation={path}", "--entry=computation::Demo", *flags,
    ]))
    return package, hashlib.sha256(package.read_bytes()).hexdigest()


def execute(toolchain, journal, directory, package, pin, inputs):
    request = directory / "inputs.json"
    request.write_text(json.dumps({"inputs": inputs}))
    output = directory / "results.json"
    report = journal.json([
        toolchain.runtime, "--json", "run", f"--package={package}",
        f"--sha256={pin}", f"--input={request}", f"--results={output}",
    ])
    assert report["status"] == "executed"
    return json.loads(output.read_text())["value"], report


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_literal_payloads_and_natural_statics_execute(
        toolchain, journal, directory, flags):
    source = PRELUDE + '''
fn local_number()->index{return 3;}
math fn math_number()->index{return 3;}
fn natural<N:nat>()->index{return index<N>();}
math fn math_natural<N:nat>()->index{return index<N>();}
math fn generic<E:Field>()->E{return 1;}
protocol Run roles(P,Q)()->(local_value:index@P,math_value:index@(P,Q),
 natural_value:index@P,static_value:index@(P,Q),field_value:F@(P,Q),flag_value:bool@(P,Q)){
 return(local_value=local_number(),math_value=math_number(),natural_value=natural<9>(),
        static_value=math_natural<9>(),field_value=generic<F>(),flag_value=true);
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    values, _ = execute(toolchain, journal, directory, package, pin,
                        {"P": {}, "Q": {}})
    shared = {"math_value": "3", "static_value": "9", "field_value": "1",
              "flag_value": True}
    assert values == {"P": {**shared, "local_value": "3", "natural_value": "9"},
                      "Q": shared}


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_eager_shared_recipe_restricts_to_nested_loop_participants(
        toolchain, journal, directory, flags):
    source = PRELUDE + '''
fn size(rows:domain<index>)->F{return fold(rows,0,fn(total,item)=>total+1);}
protocol Run roles(P,Q)(x:F@P,n:index@(P,Q))->(r:F@P){
 let mut count@(P,Q)=n;let rows=range(0,count);count=3;
 let mut result@P=x;
 for _ in 0..count roles(P) max 4{
  for _ in 0..index<1>() roles(P) max 1{result=result+size(rows);}
 }
 return result;
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    for n, other, expected in [(0, 4, "5"), (2, 1, "11"), (4, 0, "17")]:
        invocation = directory / f"eager-{n}"
        invocation.mkdir()
        values, _ = execute(toolchain, journal, invocation, package, pin,
                            {"P": {"x": "5", "n": str(n)},
                             "Q": {"n": str(other)}})
        assert values == {"P": {"r": expected}, "Q": {}}


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_enum_math_and_pointwise_constructors_execute(toolchain, journal, directory, flags):
    source = PRELUDE + '''
protocol Run roles(P,V)(a:bool@(P,V))->(r:bool@(P,V),empty:bool@(P,V)){
 return(r=enum_math(unwrap(Choice::Value(a))),empty=unwrap(Choice::Empty()));
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    values, _ = execute(toolchain, journal, directory, package, pin,
                        {"P": {"a": True}, "V": {"a": False}})
    assert values == {"P": {"r": True, "empty": False},
                      "V": {"r": False, "empty": False}}


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_authored_producers_preserve_fields_constants_and_local_state(
        toolchain, journal, directory, flags):
    source = PRELUDE + '''
struct Pair{pub left:bool,pub right:bool}
math fn captureless()->bool{return false||true;}
math fn ordinary(x:F,a:bool)->F{
 let pair=Pair{left:a,right:true};
 return if pair.left&&captureless(){x+2}else{x+3};
}
fn local(a:bool)->bool{
 let mut state=false;
 let value=a&&{state=true;false};
 return value||state;
}
protocol Run roles(P,V)(a:bool@(P,V),x:F@(P,V),only:bool@P)->
 (number:F@(P,V),local:bool@P,pointwise:bool@(P,V),empty:bool@(P,V)){
 return(number=ordinary(x,a),local=local(only),pointwise=true&&false,
        empty=unwrap(Choice::Empty()));
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    for only in (False, True):
        values, _ = execute(toolchain, journal, directory, package, pin, {
            "P": {"a": True, "x": "5", "only": only},
            "V": {"a": False, "x": "7"},
        })
        assert values == {
            "P": {"number": "7", "local": only, "pointwise": False, "empty": False},
            "V": {"number": "10", "pointwise": False, "empty": False},
        }


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_local_selected_yields_and_joined_state_execute(
        toolchain, journal, directory, flags):
    source = '''module computation;
fn conjunction(go:bool)->(bool,bool,bool){
 let mut left=false;let mut right=true;
 let value=go&&{left=true;right=false;let unused=true;false};
 return(value,left,right);
}
fn disjunction(go:bool)->(bool,bool,bool){
 let mut state=(false,true);
 let value=go||{state=(true,false);let unused=false;true};
 return(value,state.0,state.1);
}
fn nested(go:bool)->(bool,bool,bool){
 let mut left=false;let mut right=true;
 let value=go&&{left=true;false||{right=false;true}};
 return(value,left,right);
}
protocol Run roles(P)(go:bool@P)->
 (conjunction:(bool,bool,bool)@P,disjunction:(bool,bool,bool)@P,
  nested:(bool,bool,bool)@P){
 return(conjunction=conjunction(go),disjunction=disjunction(go),nested=nested(go));
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    for go in (False, True):
        values, _ = execute(toolchain, journal, directory, package, pin,
                            {"P": {"go": go}})
        assert values == {"P": {
            "conjunction": [False, go, not go],
            "disjunction": [True, not go, go],
            "nested": [go, go, not go],
        }}


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
@pytest.mark.parametrize("operator", ["&&", "||"])
@pytest.mark.parametrize("math", [False, True])
def test_selected_finite_work_executes_only_when_reached(
        toolchain, journal, directory, flags, operator, math):
    formula = f"go{operator}expensive(n,x)"
    source = PRELUDE
    if math:
        source += f"math fn selected(go:bool,n:index,x:F)->bool{{return {formula};}}"
        formula = "selected(go,n,x)"
    source += f'''
protocol Run roles(P,V)(go:bool@P,n:index@P,x:F@P)->(r:bool@P){{return {formula};}}
entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    encoded = json.loads(package.read_text())
    child = joint_package(encoded)
    assert '"data.branch"' in child["original"]
    assert '"protocol.branch"' not in child["original"]
    # This is structural execution evidence beyond the Boolean truth table:
    # the actual participant Program retains a selected instruction.
    candidate = json.loads(joint_artifact(encoded)["candidate"])
    assert '"if"' in json.dumps(candidate)
    usage = {}
    for go in (False, True):
        values, report = execute(toolchain, journal, directory, package, pin,
                                 {"P": {"go": go, "n": "8", "x": "1"}, "V": {}})
        assert values == {"P": {"r": False if operator == "&&" else go}, "V": {}}
        usage[go] = joint_execution(report)["roles"][0]["usage"]
    reached = operator == "&&"
    assert (usage[reached]["iterations"] > usage[not reached]["iterations"]
            or usage[reached]["instructions"] > usage[not reached]["instructions"])
    (directory / "selection-work.json").write_text(json.dumps({
        "reached": usage[reached], "skipped": usage[not reached],
    }, indent=2))


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_nested_callbacks_domains_and_mutable_projection_snapshots(
        toolchain, journal, directory, flags):
    source = PRELUDE + '''
struct Pair{pub left:bool,pub right:bool}
math fn apply(x:bool,f:math fn(bool)->bool)->bool{return f(x);}
protocol Run roles(P,V)(a:bool@P,b:bool@P,n:index@P,x:F@P)->(r:bool@P){
 let mut pair=Pair{left:a,right:b};
 let first=pair.left&&pair.right;
 pair=Pair{left:b,right:a};
 let rows=range(0,n);
 let work=pair.left&&{let value=fold(rows,x,fn(s,i)=>s+x);value==x};
 return first||apply(work,fn(v)=>v||pair.right);
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    for a, b in ((False, True), (True, False), (True, True)):
        values, _ = execute(toolchain, journal, directory, package, pin, {
            "P": {"a": a, "b": b, "n": "8", "x": "1"}, "V": {},
        })
        assert values == {"P": {"r": a}, "V": {}}


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_explicit_boolean_intrinsic_remains_eager(toolchain, journal, directory, flags):
    source = PRELUDE + '''
math fn eager(go:bool,n:index,x:F)->bool{
 return intrinsic("bool.and",go,expensive(n,x));
}
protocol Run roles(P,V)(go:bool@P,n:index@P,x:F@P)->(r:bool@P){return eager(go,n,x);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags)
    for go in (False, True):
        values, report = execute(toolchain, journal, directory, package, pin,
                                 {"P": {"go": go, "n": "8", "x": "1"}, "V": {}})
        assert values == {"P": {"r": False}, "V": {}}
        assert joint_execution(report)["roles"][0]["usage"]["iterations"] == 8


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_layout_pointwise_and_or_accept_divergent_components(
        toolchain, journal, directory, flags):
    source = '''pub protocol Run roles(P,V)(a: bool @(P,V), b: bool @(P,V)) -> bool @(P,V):
    return a and (b or a)
entry def Demo(inputs: Run::Inputs):
    results <- Run::run(inputs)
    return results
'''
    package, pin = compile_source(toolchain, journal, directory, source, flags, layout=True)
    child = joint_package(json.loads(package.read_text()))
    assert '"protocol.branch"' not in child["original"]
    values, _ = execute(toolchain, journal, directory, package, pin, {
        "P": {"a": False, "b": True}, "V": {"a": True, "b": False},
    })
    assert values == {"P": {"result": False}, "V": {"result": True}}


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
@pytest.mark.parametrize("operator", ["&&", "||"])
def test_selected_local_stop_preserves_reached_reason(
        toolchain, journal, directory, flags, operator):
    source = f'''module sample;
fn selected(go:bool, reason:bool)->bool{{
 return go{operator}{{if reason{{stop "reject";}}else{{stop "abort";}}}};
}}
protocol Run roles(P)(go:bool@P,reason:bool@P)->(result:bool@P){{
 return selected(go,reason);
}}
entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    reached = operator == "&&"
    for reason in (False, True):
        assert entry.run(f"skip-{reason}", {"go": not reached, "reason": reason}) == {
            "result": not reached,
        }
        report = entry.run(f"stop-{reason}", {"go": reached, "reason": reason},
                           refuses="entry-host-run-failed")
        assert joint_execution(report)["roles"][0]["after"][1]["cause"] == [
            "explicit", {"omitted_bytes": 0, "text": "reject" if reason else "abort"},
        ]


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
@pytest.mark.parametrize("context", ["if", "match", "loop", "callback", "deferred"])
def test_authored_index_exits_preserve_reached_and_skipped_stops(
        toolchain, journal, directory, flags, context):
    stop = 'if reason{stop "reject";}else{stop "abort";}'
    expressions = {
        "if": f'return if go{{{stop}}}else{{7}};',
        "match": f'''let choice=if go{{Choice::First()}}else{{Choice::Second()}};
return match choice{{Second()=>{{7}},First()=>{{{stop}}}}};''',
        "loop": f'for _ in 0..(if go{{2}}else{{0}}){{{stop}}}return 7;',
        "callback": f'return if go{{apply(fn()=>{{{stop}}})}}else{{7}};',
        "deferred": f'return ignore(fn()=>{{{stop}}});',
    }
    source = f'''module sample;
enum Choice{{First(),Second()}}
fn apply(f:fn()->index)->index{{return f();}}
fn ignore(f:fn()->index)->index{{return 7;}}
fn selected(go:bool,reason:bool)->index{{{expressions[context]}}}
protocol Run roles(P)(go:bool@P,reason:bool@P)->(result:index@P){{
 return selected(go,reason);
}}
entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for reason in (False, True):
        assert entry.run(f"skip-{reason}", {"go": False, "reason": reason}) == {
            "result": "7",
        }
        inputs = {"go": True, "reason": reason}
        if context == "deferred":
            assert entry.run(f"unused-{reason}", inputs) == {"result": "7"}
        else:
            report = entry.run(f"stop-{reason}", inputs, refuses="entry-host-run-failed")
            assert joint_execution(report)["roles"][0]["after"][1]["cause"] == [
                "explicit", {"omitted_bytes": 0, "text": "reject" if reason else "abort"},
            ]


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_reordered_all_stopped_match_preserves_each_leaf_reason(
        toolchain, journal, directory, flags):
    source = '''module sample;
enum Choice{First(),Second()}
fn selected(go:bool)->index{
 let choice=if go{Choice::First()}else{Choice::Second()};
 return match choice{Second()=>{stop "abort";},First()=>{stop "reject";}};
}
protocol Run roles(P)(go:bool@P)->(result:index@P){return selected(go);}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for go in (False, True):
        report = entry.run(str(go), {"go": go}, refuses="entry-host-run-failed")
        assert joint_execution(report)["roles"][0]["after"][1]["cause"] == [
            "explicit", {"omitted_bytes": 0, "text": "reject" if go else "abort"},
        ]


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_distinct_control_headers_tails_and_mutable_carry_execute(
        toolchain, journal, directory, flags):
    source = '''module sample;
math fn pick(go:bool,a:bool,b:bool)->(bool,bool){
 return if go{{(a,b)}}else{(b,a)};
}
fn bounded(lo:index,hi:index,a:bool)->bool{
 let mut state=a;
 for _ in lo..hi{state=!state;}
 return state;
}
protocol Run roles(P)(go:bool@P,a:bool@P,b:bool@P,lo:index@P,hi:index@P)->
 (left:bool@P,right:bool@P,branch:bool@P,local:bool@P,carry:bool@P){
 let (left,right)=pick(go,a,b);
 let mut state=a;
 for _ in 0..hi roles(P) max 8{state=!state;}
 let _:()=if go{()}else{()};
 return(carry=state,local=bounded(lo,hi,a),right=right,left=left,
        branch=if go{a}else{b});
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for go in (False, True):
        for lo, hi in ((0, 0), (1, 1), (0, 1), (1, 3), (3, 1)):
            assert entry.run(f"bounds-{go}-{lo}-{hi}", {
                "go": go, "a": True, "b": False, "lo": str(lo), "hi": str(hi),
            }) == {
                "left": go, "right": not go, "branch": go,
                "local": max(hi - lo, 0) % 2 == 0, "carry": hi % 2 == 0,
            }
