"""Exact static named selections through layout source and the native Host."""

import hashlib
import json

import pytest


PROVIDER = '''pub def same<T: Type + Copy + Drop>(x: T) -> T:
    return x
pub local def checked(x: bool) -> bool effects(stop):
    guard x
    return x
'''
CLIENT = '''use exports as selected
use provider::{checked}
def apply<A: Type + Copy + Drop, B: Type + Copy + Drop>(x: A, f: fn(A) -> B) -> B:
    return f(x)
def forward<A: Type + Copy + Drop, B: Type + Copy + Drop>(x: A, f: fn(A) -> B) -> B:
    return apply(x, f)
interface Identity:
    def same<T: Type + Copy + Drop>(x: T) -> T
module Implementation: Identity:
    def same<T: Type + Copy + Drop>(x: T) -> T:
        return x
def member<C: Identity>(x: bool) -> bool:
    return forward(x, C::same<bool>)
local def ordered(x: bool, f: local fn(bool) -> bool effects(stop)) -> bool effects(f):
    result <- f(x)
    return result
pub protocol Run roles(P)(x: bool @P) -> (bool, bool, bool) @P:
    first = forward(x, selected::same)
    second = apply(x, selected::same<bool>)
    third <- ordered(x, checked)
    return (first, second, member<Implementation>(third))
'''
FINITE = '''domain F = field("koala-bear")
type Vector<E: Field> = builtin("vector", E)
type Finite<I: Type + Copy + Drop> = builtin("finite", I)
view def elements<E: Field>(xs: Vector<E>) -> Finite<E> = domain("elements")
def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: fn(S, item: I) -> S where item_from(item, rows)) -> S = finite("math.fold")
local def ordered<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: local fn(S, item: I) -> S effects(stop) where item_from(item, rows)) -> S effects(stop) = finite("local.fold")
def add<E: Field>(state: E, item: E) -> E:
    return state + item
local def add_local<E: Field>(state: E, item: E) -> E effects():
    return state + item
pub protocol Run roles(P)(xs: Vector<F> @P, initial: F @P) -> F @P:
    first = fold(elements(xs), initial, add)
    second <- ordered(elements(xs), initial, add_local<F>)
    return first + second
'''


def compile_source(toolchain, journal, directory, source, flags):
    modules = {"provider": PROVIDER, "exports": "pub use provider::{same}\n", "m": source}
    arguments = []
    for name, text in modules.items():
        path = directory / f"{name}.zkc"
        path.write_text(text)
        arguments.append(f"--module={name}={path}")
    package = directory / "named.zkpkg"
    package.write_text(journal.run([
        toolchain.compiler, "language-package", "--source-format=zkc-layout",
        "--entry=m::Run", *arguments, *flags,
    ]))
    return package, hashlib.sha256(package.read_bytes()).hexdigest()


def execute(toolchain, journal, directory, package, pin, name, arguments, refuses=None):
    inputs = directory / f"{name}.inputs.json"
    inputs.write_text(json.dumps({"inputs": {"P": arguments}}))
    outputs = directory / f"{name}.outputs.json"
    report = journal.json([
        toolchain.runtime, "--json", "run", f"--package={package}", f"--sha256={pin}",
        f"--input={inputs}", f"--results={outputs}",
    ], refuses=refuses)
    if refuses:
        assert not outputs.exists()
        return report
    return json.loads(outputs.read_text())["value"]["P"]["result"]


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_imported_math_local_and_generic_members(toolchain, journal, directory, flags):
    package, pin = compile_source(toolchain, journal, directory, CLIENT, flags)
    assert execute(toolchain, journal, directory, package, pin, "pass", {"x": True}) == [True] * 3
    execute(toolchain, journal, directory, package, pin, "stop", {"x": False},
            refuses="entry-host-run-failed")


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
@pytest.mark.parametrize("values,expected", [([], "14"), (["2", "3", "5"], "34")])
def test_named_finite_callbacks_zero_and_many(toolchain, journal, directory, flags, values, expected):
    package, pin = compile_source(toolchain, journal, directory, FINITE, flags)
    assert execute(toolchain, journal, directory, package, pin, "fold",
                   {"xs": values, "initial": "7"}) == expected


EXTENTS = '''module m;
domain F=field("bls12-381.fr");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
type Vector<E:Field>=builtin("vector",E);
math fn apply(xs:Array<F,4>,ys:Array<F,4>,f:math fn(Array<F,4>,Array<F,4>)->bool)->bool{return f(xs,ys);}
math fn unused(xs:Array<F,4>,ys:Array<F,4>,f:math fn(Array<F,4>,Array<F,4>)->bool)->bool{return true;}
math fn same<N:nat,M:nat>(xs:Array<F,N>,ys:Array<F,M>)->bool where equal_extent(xs,ys){return true;}
interface Same{math fn same<N:nat,M:nat>(xs:Array<F,N>,ys:Array<F,M>)->bool where equal_extent(xs,ys);}
module Implementation:Same{math fn same<N:nat,M:nat>(xs:Array<F,N>,ys:Array<F,M>)->bool where equal_extent(xs,ys){return true;}}
math fn member<C:Same>(xs:Array<F,4>,ys:Array<F,4>)->bool{return apply(xs,ys,C::same<4,4>);}
fn checked(xs:Vector<F>,ys:Vector<F>)->(bool,bool,bool,bool,bool,bool) effects(stop){
 let a=kernel<F,4>("field_array.from_vector",xs);
 let b=kernel<F,4>("field_array.from_vector",ys);
 return (same<4,4>(a,b),apply(a,b,fn(x,y)=>same<4,4>(x,y)),apply(a,b,same<4,4>),apply(a,b,same),unused(a,b,same),member<Implementation>(a,b));
}
pub protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P)->(result:(bool,bool,bool,bool,bool,bool)@P){return checked(xs,ys);}
'''


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_generic_named_extent_controls(toolchain, journal, directory, flags):
    source = directory / "m.zkc"
    source.write_text(EXTENTS)
    package = directory / "extents.zkpkg"
    package.write_text(journal.run([
        toolchain.compiler, "language-package", "--source-format=zkc",
        "--entry=m::Run", f"--module=m={source}", *flags,
    ]))
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    assert execute(toolchain, journal, directory, package, pin, "extents",
                   {"xs": ["1", "2", "3", "4"], "ys": ["5", "6", "7", "8"]}) == [True] * 6
    execute(toolchain, journal, directory, package, pin, "short",
            {"xs": ["1", "2", "3"], "ys": ["5", "6", "7", "8"]},
            refuses="entry-host-run-failed")


PROJECTIONS = '''module m;
domain F=field("bls12-381.fr");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
type Vector<E:Field>=builtin("vector",E);
math fn apply<N:nat>(xs:[Array<F,4>;N],f:math fn([Array<F,4>;N])->bool)->bool{return f(xs);}
math fn same(xs:Array<F,4>,ys:Array<F,4>)->bool where equal_extent(xs,ys){return true;}
math fn selected<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0){return true;}
interface Selection{math fn selected<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0);}
module Implementation:Selection{math fn selected<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N,equal_extent(xs.0,xs.0){return true;}}
math fn member<M:nat,C:Selection>(xs:[Array<F,4>;M])->bool where 1<=M{return apply(xs,C::selected<M>);}
math fn nested<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N{let first=apply(xs,selected<N>);return same(xs[0],xs[0]);}
math fn literal<N:nat>(xs:[Array<F,4>;N])->bool where 1<=N{return apply(xs,fn(a)=>same(a[0],a[0]));}
math fn controls<M:nat>(xs:[Array<F,4>;M])->(bool,bool,bool,bool,bool,bool,bool) where 1<=M{
 return (selected<M>(xs),apply(xs,fn(a)=>selected<M>(a)),apply(xs,selected<M>),apply(xs,selected),member<M,Implementation>(xs),apply(xs,nested<M>),apply(xs,literal<M>));
}
math fn wrap(a:Array<F,4>)->[Array<F,4>;1]{return [a];}
fn checked(xs:Vector<F>)->(bool,bool,bool,bool,bool,bool,bool) effects(stop){
 let a=kernel<F,4>("field_array.from_vector",xs);
 return controls<1>(wrap(a));
}
pub protocol Run roles(P)(xs:Vector<F>@P)->(result:(bool,bool,bool,bool,bool,bool,bool)@P){return checked(xs);}
'''


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_symbolic_selected_projection_controls(toolchain, journal, directory, flags):
    source = directory / "m.zkc"
    source.write_text(PROJECTIONS)
    package = directory / "projections.zkpkg"
    package.write_text(journal.run([
        toolchain.compiler, "language-package", "--source-format=zkc",
        "--entry=m::Run", f"--module=m={source}", *flags,
    ]))
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    assert execute(toolchain, journal, directory, package, pin, "projections",
                   {"xs": ["1", "2", "3", "4"]}) == [True] * 7
    execute(toolchain, journal, directory, package, pin, "short",
            {"xs": ["1", "2", "3"]}, refuses="entry-host-run-failed")
