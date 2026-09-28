"""Focused structured notation and typed projection regressions."""

import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())
cases = []


def yes(name, src):
    cases.append((name, src, None))


def no(name, src, code):
    cases.append((name, src, code))


yes(
    "subtraction without spaces",
    'use zkc::algebra; fn X(x: "koala-bear"::Element,y: "koala-bear"::Element)->"koala-bear"::Element{return x-y;}',
)
yes("raw import", "use zkc::poly::r#fold;")
yes(
    "qualified record root", "struct R{x:bool} fn X()->bool{return crate::R{x:true}.x;}"
)
yes("qualified constant", "const N:index=3;fn X()->index{return crate::N;}")
yes(
    "qualified configure",
    'fn Echo<F:Field>(x:F::Element)->F::Element{return x;}configure X=crate::Echo(F="koala-bear");',
)
yes("record len field", "struct R{len:bool} fn X(r:R)->bool{return r.len;}")
yes(
    "vector temporary length",
    'use zkc::algebra::Vector; fn V(v:Vector<"koala-bear"::Element>)->Vector<"koala-bear"::Element>{return v;}fn X(v:Vector<"koala-bear"::Element>)->index{return V(v).len();}',
)
yes("array selection", "struct R{x:bool}fn X(a:Array<R,1>)->bool{return a[0].x;}")
yes(
    "flat field call",
    "struct R{x:bool}fn Id(x:bool)->bool{return x;}fn X(r:R)->bool{let x=Id(r.x);return x;}",
)
yes(
    "exact binding", 'bind same="index.equal"(); fn X(x:index)->bool{return same(x,x);}'
)
no("receiver call", "fn X(x:bool)->bool{return x.nope();}", "source-receiver-call")
no("raw malformed", "fn r#1()->(){return;}", "source-identifier")
no("quoted declaration", 'fn "X"()->(){return;}', "source-identifier")
no("reserved declaration", "fn return()->(){return;}", "source-identifier")
no("old keyed record", "struct R{x:bool}fn X()->R{return R(x=true);}", "source-syntax")
no("old record declaration", "struct R(x:bool);", "source-syntax")
no("bare binding target", "bind x=index.equal();", "source-string")
no(
    "record ordinal flat",
    "struct R{x:bool}fn Id(x:bool)->bool{return x;}fn X(r:R)->bool{let x=Id(r.0);return x;}",
    "source-projection",
)
no(
    "array ordinal flat",
    "fn Id(x:bool)->bool{return x;}fn X(a:Array<bool,1>)->bool{let x=Id(a.0);return x;}",
    "source-projection",
)
no("array bounds", "fn X(a:Array<bool,1>)->bool{return a[1];}", "source-projection")
no(
    "array dynamic",
    "fn X(a:Array<bool,1>,i:index)->bool{return a[i];}",
    "source-projection",
)
no("protocol hidden return", "protocol P{roles(A);return F();}", "source-reference")
base = 'library(namespace="test",name="probe",version="1",resolution="fixture");interface Marker{}component Selected:Marker{} '
yes(
    "checked temporary product",
    base
    + "fn X<C:Marker>(x:bool,y:bool)->bool effects(local){return (x,y).0;}link Closed=X<Selected>;",
)
yes(
    "checked temporary record",
    base
    + "struct R{x:bool,y:bool}fn X<C:Marker>(x:bool,y:bool)->bool effects(local){return R{x,y}.x;}link Closed=X<Selected>;",
)
yes(
    "checked field capture",
    base
    + "struct R{x:bool,y:bool}fn X<C:Marker>(items:Array<bool,1>,r:R)->Array<bool,1> effects(local){return map items |item| {r.x};}link Closed=X<Selected>;",
)
yes(
    "checked vector length",
    base
    + 'use zkc::algebra::Vector;fn X<C:Marker>(v:Vector<"koala-bear"::Element>)->index effects(local){return v.len();}link Closed=X<Selected>;',
)
resource = 'library(namespace="test",name="probe",version="1",resolution="fixture");interface Resource{type Item;} '
no(
    "abstract temporary discard",
    resource
    + "fn X<C:Resource>(x:C::Item,y:C::Item)->C::Item effects(local){return (x,y).0;}",
    "library-resource-leak",
)
no(
    "abstract binding discard",
    resource
    + "fn X<C:Resource>(x:C::Item,y:C::Item)->C::Item effects(local){let pair=(x,y);return pair.0;}",
    "library-resource-leak",
)

yes("raw field", "struct R{r#return:bool}fn X(r:R)->bool{return r.r#return;}")
yes(
    "raw associated member",
    base
    + "interface I{local r#fold(x:bool)->bool;}component C:I{local r#fold(x:bool)->bool{return x;}}fn X<T:I>(x:bool)->bool{return T::r#fold(x);}link Closed=X<C>;",
)
no(
    "nested temporary discard",
    resource
    + "fn X<C:Resource>(x:C::Item,y:C::Item,z:C::Item)->C::Item{return ((x,y),z).0.0;}",
    "library-resource-leak",
)
no(
    "zero extent traversal capture",
    resource
    + "fn X<C:Resource>(items:Array<bool,0>,x:C::Item)->Array<C::Item,0>{return map items |item| {x};}",
    "library-traversal-capture",
)
no("unfinished function at EOF", "fn X()->(){return;", "source-syntax")
no("raw declaration keyword", "r#fn X()->(){return;}", "source-syntax")

checked_record = "checked struct R{x:bool} constructors(Build);fn Build(x:bool)->R{return crate::R{x};}"
yes("authorized qualified constructor", checked_record)
no(
    "unauthorized qualified constructor",
    checked_record + "fn Forge(x:bool)->R{return crate::R{x};}",
    "source-checked-construction",
)
no(
    "first operand refusal precedes second evaluation",
    "fn Second(x:bool)->bool{return x;}fn Join(first:bool,second:bool)->(bool,bool){return (first,second);}fn X(x:bool,y:bool)->bool{return Join(first:x.0,second:Second()).0;}",
    "source-projection",
)
no(
    "checked first operand refusal precedes second evaluation",
    base
    + "fn Wide(x:index)->bool{return true;}fn Join(a:bool,b:bool)->(bool,bool){return (a,b);}fn X<C:Marker>(x:bool)->bool effects(local){return Join(b:x.0,a:Wide(x)).0;}link Closed=X<Selected>;",
    "library-source-projection",
)
no(
    "checked restricted constructor through a qualified path",
    base
    + "checked struct R{x:bool} constructors(Build);fn Build(x:bool)->R{return crate::R{x};}fn X<C:Marker>(x:bool)->R effects(local){return crate::R{x};}link Closed=X<Selected>;",
    "library-source-record-authority",
)

# Zero-storage values keep their nominal obligations through selections,
# inferred captures and traversals, in abstract clients and after selecting a
# concrete empty representation.
cell = 'library(namespace="test",name="probe",version="1",resolution="fixture");interface Cell{type Value;} '
yes(
    "inferred region captures a copyable sibling of a zero-storage place",
    cell
    + "fn Client<C:Cell>(x:(C::Value,bool),b:bool)->(C::Value,bool){if b -> (r) {yield (x.1);} else {yield (x.1);} return (x.0,r);}",
)
no(
    "a zero-storage sibling left beside an inferred capture",
    cell
    + "fn Client<C:Cell>(x:(C::Value,bool),b:bool)->bool{if b -> (r) {yield (x.1);} else {yield (x.1);} return r;}",
    "library-resource-leak",
)
no(
    "a selected concrete empty representation keeps the abstract obligation",
    cell
    + "component Impl:Cell{type Value=();}fn Client<C:Cell>(x:(C::Value,bool),b:bool)->bool{if b -> (r) {yield (x.1);} else {yield (x.1);} return r;}link Closed=Client<Impl>;",
    "library-resource-leak",
)
no(
    "a nested zero-storage selection captured by a traversal",
    cell
    + "fn Client<C:Cell>(items:Array<bool,0>,x:(C::Value,bool))->Array<C::Value,0>{return map items |i| {x.0};}",
    "library-traversal-capture",
)
no(
    "a nested zero-storage selection captured by a nonempty traversal",
    cell
    + "fn Client<C:Cell>(items:Array<bool,1>,x:(C::Value,bool))->Array<C::Value,1>{return map items |i| {x.0};}",
    "library-traversal-capture",
)

# Reference-only slots select existing places. They never evaluate a call,
# a collection query or a literal, and never materialize a constant.
for slot, text in (
    (
        "message",
        'protocol P{roles(A,B);inputs(A x:bool);outputs(B bool);message "S":A(F(x))->B(y);return(y);}',
    ),
    (
        "finish",
        "protocol P{roles(A);inputs(A x:bool);outputs(A r:bool);finish{r:F(x)};}",
    ),
    (
        "invoke",
        "protocol C{roles(A);inputs(A x:bool);return;}protocol P{roles(A);inputs(A x:bool);dependencies(c:C());invoke c(F(x))->();return;}",
    ),
    (
        "carry",
        "protocol P{roles(A);inputs(A x:bool);outputs(A bool);loop 1 carry (a=F(x)) -> (r) {yield (a);} return(r);}",
    ),
    (
        "capture",
        "fn X(x:bool,b:bool)->bool{if b capture(x.len()) -> (r) {yield (x);} else {yield (x);} return r;}",
    ),
    (
        "match",
        "enum E{A(),B()} fn X(x:bool)->bool{match F(x) -> (r) {A() => {yield (x);}, B() => {yield (x);}} return r;}",
    ),
    (
        "yield literal",
        "fn X(x:bool,b:bool)->bool{if b -> (r) {yield (true);} else {yield (x);} return r;}",
    ),
):
    no(
        f"reference-only {slot} refuses computation",
        text,
        "source-reference" if slot != "yield literal" else "source-identifier",
    )
no(
    "traversal input is an array place",
    base
    + "fn X<C:Marker>(v:Array<bool,1>)->bool{for x in Id(v) carry (a=x) -> (r) {yield (a);} return r;}",
    "library-source-traversal",
)
no(
    "protocol message does not materialize constants",
    'const N:index=3;protocol P{roles(A,B);outputs(B index);message "S":A(crate::N)->B(y);return(y);}',
    "source-value-reference",
)
no(
    "reference-only bulk collection index is a computation",
    'use zkc::algebra::Indices;protocol P{roles(A,B);inputs(A v:Indices);outputs(B index);message "S":A(v[0])->B(y);return(y);}',
    "source-projection",
)
yes(
    "structural array element in a protocol reference slot",
    'protocol P{roles(A,B);inputs(A v:Array<bool,2>);outputs(B bool);message "S":A(v[1])->B(y);return(y);}',
)
no(
    "protocol product ordinal on an array",
    'protocol P{roles(A,B);inputs(A v:Array<bool,2>);outputs(B bool);message "S":A(v.1)->B(y);return(y);}',
    "source-projection",
)

# Raw identifiers work in every identifier position with their decoded name.
yes(
    "raw local and label",
    "fn Id(r#in:bool)->bool{return r#in;}fn X(x:bool)->bool{let r#let=Id(r#in:x);return r#let;}",
)
yes(
    "raw role and port",
    "protocol P{roles(r#local);inputs(r#local r#in:bool);outputs(r#local r#return:bool);finish{r#return:r#in};}",
)
yes(
    "raw record field initializer",
    "struct R{r#return:bool} fn X(x:bool)->R{return R{r#return:x};}",
)
no("raw keyword is not a keyword", "fn X(x:bool)->bool{r#return x;}", "source-syntax")

# Requirement lists state equality directly, and installed predicates without
# a source export are named by their dotted key's segments.
yes(
    "requirement list equality",
    "use zkc::curve;fn Id<F:PairingField>(x:F::Element)->F::Element requires (ScalarAction(F::PairingG1), F::PairingG1::Scalar == F){return x;}",
)
yes(
    "installed predicate path",
    "fn Good<E: domain Codec,D: domain Codec,F: domain Field>()->() where E == D requires (Encodes::field(E,F)){return();}",
)
no(
    "unknown predicate path",
    "fn Bad<E: domain Codec,F: domain Field>()->() requires (Encodes::nothing(E,F)){return();}",
    "source-name-unresolved",
)
no(
    "requirement item is a predicate or an equality",
    "fn X<F:Field>()->() requires (F){return();}",
    "source-syntax",
)

yes(
    "projected protocol message",
    'protocol P{roles(A,B);inputs(A p:(bool,bool));outputs(B bool);message [send] "S":A(p.0)->B(y);return(y);}',
)
no(
    "protocol return does not materialize constants",
    "const N:index=3;protocol P{roles(A);outputs(A index);return(crate::N);}",
    "source-value-reference",
)

empty_component = (
    base + "interface Empty{type Value;}component Unit:Empty{type Value=();}"
)
no(
    "closed empty nominal sibling retains abstract obligation",
    empty_component
    + "fn X<C:Empty>(x:C::Value,b:bool)->bool{return (x,b).1;}link Closed=X<Unit>;",
    "library-resource-leak",
)
no(
    "closed zero storage traversal retains abstract obligation",
    empty_component
    + "fn X<C:Empty>(x:C::Value,a:Array<bool,0>)->Array<C::Value,0>{return map a |b| {x};}link Closed=X<Unit>;",
    "library-traversal-capture",
)
yes(
    "private component can consume its empty representation",
    base
    + "interface I{type Value;local take(x:Value,b:bool)->bool;}component C:I{type Value=();local take(x:Value,b:bool)->bool{return (x,b).1;}}",
)
yes(
    "protocol static array element",
    'protocol P{roles(A,B);inputs(A xs:Array<bool,1>);outputs(B bool);message [send] "S":A(xs[0])->B(y);return(y);}',
)
no(
    "protocol message cannot hide runtime indexing",
    'use zkc::algebra::Vector;protocol P{roles(A,B);inputs(A xs:Vector<"koala-bear"::Element>);outputs(B "koala-bear"::Element);message [send] "S":A(xs[0])->B(y);return(y);}',
    "source-projection",
)
no(
    "protocol dynamic array index is not a place",
    'protocol P{roles(A,B);inputs(A xs:Array<bool,2>,A i:index);outputs(B bool);message [send] "S":A(xs[i])->B(y);return(y);}',
    "source-reference",
)
no(
    "aggregate mutation remains unsupported",
    "fn X(r:(bool,bool),b:bool)->bool{let mut x=r;x.0=b;return x.0;}",
    "source-struct-mutable",
)

yes(
    "exact site and implementation labels in configuration",
    'use zkc::poly::Table;fn Fold<F:Field>(f:Table<F>,r:F::Element)->Table<F>{["fold-site"]let out=zkc::poly::r#fold::<F>(f,r);return out;}configure Chosen=Fold(F="bls12-381.fr") using("fold-site"="arkworks-msb/poly.fold");',
)
yes(
    "associated type reflexive equality",
    base
    + "interface I{type Value copy drop;}component C:I{type Value=bool;}fn X<T:I>(x:T::Value)->T::Value where T::Value==T::Value{return x;}link Closed=X<C>;",
)

yes(
    "multiple bulk element reads infer one checked capture",
    base
    + 'use zkc::algebra;use zkc::algebra::Vector;fn Both<T:Marker>(a:Array<bool,1>,v:Vector<"koala-bear"::Element>)->Array<"koala-bear"::Element,1> effects(local){return map a |i| {let x=v[0];let y=v[1];x+y};}link Closed=Both<Selected>;',
)

yes(
    "instance participants are exact labels",
    'protocol P{roles(A);inputs(A x:bool);outputs(A bool);return(x);}instance i:P{roles(A="prover-1");}entry main=i;',
)

for name, text, refusal in cases:
    with case(name):
        emitted = commands.source("protocol-source", text, refuses=refusal)
        if refusal is None:
            assert json.loads(emitted)[0] in ("zkc.protocol/1", "zkc.library/1")

with case("subtraction spacing preserves common instructions"):
    text = 'use zkc::algebra; fn X(x: "koala-bear"::Element,y: "koala-bear"::Element)->"koala-bear"::Element{return x-y;}'
    compact = json.loads(commands.source("protocol-source", text))
    spaced = json.loads(
        commands.source("protocol-source", text.replace("x-y", "x - y"))
    )
    assert compact == spaced

with case("raw spelling preserves declaration identity"):
    text = "fn Echo(x:bool)->bool{return x;}"
    plain = json.loads(commands.source("protocol-source", text))
    raw = json.loads(
        commands.source(
            "protocol-source", text.replace("Echo", "r#Echo").replace("x", "r#x")
        )
    )
    assert plain == raw

with case("empty authored file"):
    assert (
        json.loads(commands.source("protocol-source", "// empty\n"))[0]
        == "zkc.protocol/1"
    )

with case("ordinary wrapper is obsolete"):
    commands.source("protocol-source", "module {}", refuses="source-module-wrapper")

with case("temporary receiver and named operands run once in written order"):
    text = "use zkc::core;fn First(x:bool)->bool{core::require(x);return x;}fn Second(x:bool)->bool{core::require(x);return x;}fn Join(first:bool,second:bool)->(bool,bool){return (first,second);}fn X(x:bool,y:bool)->bool{return Join(second:Second(y),first:First(x)).0;}"
    module = json.loads(commands.source("protocol-source", text))
    function = next(row for row in module[2] if row[1] == "X")
    assert [row[2] for row in function[4] if row[0] == "apply"] == [
        "Second",
        "First",
        "Join",
    ]

with case("raw and quoted exact labels have identical decoded bytes"):
    text = "protocol P{roles(A,B);inputs(A x:bool);outputs(B bool);message [r#return] r#message:A(x)->B(y);return(y);}"
    raw = json.loads(commands.source("protocol-source", text))
    quoted = json.loads(
        commands.source(
            "protocol-source",
            text.replace("r#return", '"return"').replace("r#message", '"message"'),
        )
    )
    assert raw == quoted


def body(module, name):
    return next(row for row in module[2] if row[1] == name)[4]


def traversals(report):
    def walk(value):
        if isinstance(value, dict):
            if value.get("kind") == "array_traversal":
                yield value
            for child in value.values():
                yield from walk(child)
        elif isinstance(value, list):
            for child in value:
                yield from walk(child)

    return [t["captures"] for t in walk(report)]


with case("flat-call sites count authored instructions, not bracket operands"):
    text = "struct R{x:bool,y:bool}fn Id(x:bool)->bool{return x;}fn X(r:R,a:Array<bool,2>)->bool{let x=Id(r.x);let y=Id(a[1]);let z=Id(x);return z;}"
    rows = body(json.loads(commands.source("protocol-source", text)), "X")
    assert [(row[1], row[4]) for row in rows if row[0] == "apply"] == [
        ("__site_0", ["r.x"]),
        ("__site_1", ["a.1"]),
        ("__site_2", ["x"]),
    ]

with case("a flat call reads a qualified constant through its expression"):
    text = "const N:index=3;fn Id(x:index)->index{return x;}fn X()->index{let y=Id(crate::N);return y;}"
    rows = body(json.loads(commands.source("protocol-source", text)), "X")
    assert rows[0][0] == "op" and rows[0][3] == ["3"]
    assert rows[1][:2] == ["apply", "__site_0"]

with case("a temporary receiver runs once and selects one component"):
    text = "struct R{x:bool,y:bool}fn Make(x:bool)->R{return R{x,y:x};}fn X(x:bool)->bool{return Make(x).y;}"
    rows = body(json.loads(commands.source("protocol-source", text)), "X")
    applied = [row for row in rows if row[0] == "apply"]
    assert [row[2] for row in applied] == ["Make"]
    assert rows[-1] == ["return", [applied[0][5][1]]]

with case("ordinary inferred captures select fields and whole collections"):
    text = (
        'use zkc::algebra::Vector;struct R{x:"koala-bear"::Element,y:"koala-bear"::Element}'
        'fn X(r:R,v:Vector<"koala-bear"::Element>,k:index,n:index)->"koala-bear"::Element{'
        "let acc=r.x;for i in 0..n carry (a=acc) -> (out) {let e=v[k];let s=a+r.x;yield (s);}return out;}"
    )
    rows = body(json.loads(commands.source("protocol-source", text)), "X")
    loop = next(row for row in rows if row[0] == "for")
    assert loop[6] == ["v", "k", "r.x"], loop[6]

checked_captures = (
    (
        "a record field",
        "struct R{x:bool,y:bool}fn Client<C:Marker>(items:Array<bool,2>,r:R)->Array<bool,2> effects(local){return map items |i| {r.x};}",
        [[{"path": [0], "value": 1}]],
    ),
    (
        "a structural array element",
        "struct R{x:bool,y:bool}fn Client<C:Marker>(items:Array<bool,2>,rows:Array<R,2>)->Array<bool,2> effects(local){return map items |i| {rows[1].x};}",
        [[{"path": [1, 0], "value": 1}]],
    ),
    (
        "a collection and its index",
        "use zkc::algebra::Indices;fn Client<C:Marker>(items:Array<bool,2>,v:Indices,k:index)->Array<index,2> effects(local){return map items |i| {v[k]};}",
        [[{"path": [], "value": 1}, {"path": [], "value": 2}]],
    ),
    (
        "a collection for a literal index",
        "use zkc::algebra::Indices;fn Client<C:Marker>(items:Array<bool,2>,v:Indices)->Array<index,2> effects(local){return map items |i| {v[0]};}",
        [[{"path": [], "value": 1}]],
    ),
    (
        "a whole value at its first selection",
        "use zkc::core;struct R{x:bool,y:bool}fn Pick(r:R)->bool{return r.y;}fn Client<C:Marker>(items:Array<bool,2>,z:bool,r:R)->Array<bool,2> effects(local){return map items |i| {zkc::core::and(r.x,zkc::core::and(z,Pick(r)))};}",
        [[{"path": [], "value": 2}, {"path": [], "value": 1}]],
    ),
)
for name, text, expected in checked_captures:
    with case(f"checked traversal captures {name}"):
        report = json.loads(
            commands.source(
                "protocol-analyze", base + text + "link Closed=Client<Selected>;"
            )
        )
        assert report["state"] == "source_checked", report["diagnostics"]
        assert traversals(report) == expected, traversals(report)

for name, text, column in (
    ("projection", "struct R{x:bool}fn X(r:R)->bool{return r.nope;}", 40),
    (
        "reference slot projection",
        'protocol P{roles(A,B);inputs(A p:(bool,bool));outputs(B bool);message "S":A(p.2)->B(y);return(y);}',
        77,
    ),
    (
        "reference slot root",
        'protocol P{roles(A,B);inputs(A p:(bool,bool));outputs(B bool);message "S":A(q.0)->B(y);return(y);}',
        77,
    ),
):
    with case(f"{name} diagnostics locate the place"):
        commands.source("protocol-source", text, refuses=True)
        assert f"-:1:{column}:" in commands.last.stderr, commands.last.stderr


with case("syntax inspection preserves paths and exact static roots"):
    parsed = json.loads(
        commands.source(
            "protocol-parse",
            'fn X<F:Field>(x:"koala-bear"::Element)->F::Element{let y=crate::Id::<"koala-bear",F::Scalar>(x);return y;}',
        )
    )["content"]["functions"][0]
    call = parsed["body"][0]
    assert call["callee"] == "crate::Id"
    assert call["staticArguments"] == ['"koala-bear"', "F::Scalar"]
    assert parsed["arguments"][0]["type"]["rootKind"] == "identity"
