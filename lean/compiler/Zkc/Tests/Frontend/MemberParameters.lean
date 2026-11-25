import Zkc.Tests.Frontend.Typing

/-!
# Static parameters of interface members

These source programs reach a member either by calling it or by selecting another definition
of its module. Both paths check the implementing body at the member's parameters.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend

private def carrier := "module example
interface Carrier:
    type T
module Bits: Carrier:
    type T = bool
"

private def compareMember (condition body selected : String) : String :=
  let helper := if selected == "keep" then "    pub def keep(x: bool) -> bool: x\n" else ""
  carrier ++ s!"interface Methods:
    def compare<X: Carrier>(x: X::T) -> bool{condition}
module M<n: nat>: Methods:
    def compare(x): {body}
{helper}def evaluate(x: bool) -> bool: M<1>::{selected}(x)
"

private def mixedMember (outerWhere innerWhere body : String) : String := carrier ++
  s!"interface Methods<P: Carrier>:
    def choose<X: Carrier>(p: P::T, x: X::T) -> bool{innerWhere}
module M<C: Carrier>: Methods<C>{outerWhere}:
    def choose(p, x): {body}
def evaluate(x: bool) -> bool: M<Bits>::choose<Bits>(x, x)
"

private def defaultMember (width body : String) : String := s!"module example
interface Mark<n: nat>
module One: Mark<1>:
    nat K = 1
interface Methods:
    nat Count
    def f<H: Mark<Self::Count>>(x: bool) -> bool
module M<n: nat>: Methods:
    nat Count = n
    def f(x): {body}
    pub def keep(x: bool) -> bool: x
def evaluate(x: bool) -> bool: M<{width}>::keep(x)
"

private def equalitySlots (receiver : String) : String := s!"module example
interface Any:
    type T
interface Equality where (Self: Any):
    def equal(a: Self::T, b: Self::T) -> bool
module Numbers: Any + Equality:
    type T = nat
    def equal(a, b): a * b == 1
interface Methods:
    def compare<A: Any, E: Equality>(a: A::T, b: E::T) -> bool
module M: Methods:
    def compare(a, b):
        x: E::T = b
        return {receiver} == {receiver}
def evaluate(n: nat) -> bool: M::compare<Numbers, Numbers>(n, n)
"

/-- A helper is instantiated at the fresh type and again at the emitted type. For a
generic receiver its historical traversal also allocates the helper at the outer type. -/
private def checkCopyKeys (source : String) (keys : List Nat) (outer : Bool) : TestM Unit := do
  let .ok (check, _) := typeBlock ⟨"member-keys", "", "", #[source]⟩
    | failure "copy: names failed"
  let packages := check.packages.filterMap fun report => match report.outcome with
    | .admitted p => some (p.toSourcePackage.named.definitions.map (·.key.number))
    | _ => none
  expectTrue (check.refusals.isEmpty && packages == #[keys])
    s!"copy: expected keys {keys}, got {packages}; {check.refusals.map (·.render)}"
  let s := check.state
  let views := s.table.requestedIds.filterMap fun id => do
    let (ref, _) ← (s.table.allocatedKey? id).bind (·.opaqueFor)
    return (← (← s.program.scopes[ref.scope]?).parameters[ref.index]?).name.text
  expectTrue (views == (if outer then #["C"] else #[])) s!"copy: published opaque modules {views}"
  let some definition := s.results.trees.entries.findSome? (fun entry => do
    let .done d := entry.state | none
    guard (d.generic.isSome && d.waiting.isNone)
    return d) | failure "copy: missing generic body"
  let printed := definition.print s.env.renderer
  let detailed := definition.print s.env.renderer true
  expectTrue (printed.contains "return call identity<X::T>(x#" && detailed.contains " : X::T)")
    s!"copy: the generic body lost the private helper or its type: {printed} / {detailed}"

def memberParameterSuite : TestM Unit := do
  let check (id expected source : String) :=
    checkTypingBlock ⟨id, expected, "", #[source]⟩
  let admitted := "// sole package example::evaluate\n"
  for selected in ["compare<Bits>", "keep"] do
    check s!"opaque-{selected}" "refuse SP12 9" (compareMember "" "x == x" selected)
    check s!"equated-{selected}" "accept"
      (compareMember " where (X::T == bool)" "x == x" selected ++ admitted)

  -- The two parameter references have the same concrete module. Only the equation on
  -- the indicated reference permits built-in equality in its opaque typing.
  let outer := " where (C::T == bool)"
  let inner := " where (X::T == bool)"
  check "outer-equation" "accept" (mixedMember outer "" "p == p" ++ admitted)
  check "inner-still-opaque" "refuse SP12 9" (mixedMember outer "" "x == x")
  check "inner-equation" "accept" (mixedMember "" inner "x == x" ++ admitted)
  check "outer-still-opaque" "refuse SP12 9" (mixedMember "" inner "p == p")
  check "fixed-interface-argument" "accept" (carrier ++ "interface Methods<P: Carrier>:
    def compare<X: Carrier>(p: P::T) -> bool
module M: Methods<Bits>:
    def compare(p): p == p
def evaluate(x: bool) -> bool: M::compare<Bits>(x)
" ++ admitted)

  let result := fun (returned : String) => carrier ++ s!"interface Methods<P: Carrier>:
    def copy<X: Carrier>(p: P::T, x: X::T) -> X::T
module M<C: Carrier>: Methods<C>:
    def copy(p, x): {returned}
def evaluate(x: bool) -> bool: M<Bits>::copy<Bits>(x, x)
"
  check "own-result" "accept" (result "x" ++ admitted)
  check "distinct-result" "refuse SP12 9" (result "p")

  -- Multiplication occurs only in Numbers::equal. Seeing it in evaluate's package
  -- requires replaying the resolution for E, even though A stands for Numbers too.
  check "declared-equality" "accept" (equalitySlots "x" ++ "// uses nat.mul\n" ++ admitted)
  check "undeclared-equality" "refuse SP12 14" (equalitySlots "a")

  let numbers := "module demo
interface Any:
    type T
module N: Any:
    type T = nat
"
  checkCopyKeys (numbers ++ "interface Methods:
    def copy<X: Any>(x: X::T) -> X::T
def identity<T>(x: T) -> T: x
module M: Methods:
    def copy(x): identity<X::T>(x)
def evaluate(x: nat) -> nat: M::copy<N>(x)
") [5, 4, 3] false
  checkCopyKeys (numbers ++ "interface Methods<P: Any>:
    def copy<X: Any>(p: P::T, x: X::T) -> X::T
def identity<T>(x: T) -> T: x
module M<C: Any>: Methods<C>:
    def copy(p, x):
        y: C::T = identity<C::T>(p)
        return identity<X::T>(x)
def evaluate(x: nat) -> nat: M<N>::copy<N>(x, x)
") [8, 4, 2] true

  -- The independent default is All. The explicitly selected Equality is abstract in
  -- the generic check and receives nat in the instance. It never has to compare C::T.
  check "mixed-selected" "accept" (numbers ++ "interface Test:
    def applies<T>(x: T) -> bool
module All: Test:
    def applies(x): true
module Equality: Test:
    def applies(x): x == x
interface Methods<P: Any>:
    def compare<X: Test>(p: P::T) -> bool
module M<C: Any>: Methods<C>:
    def compare(p): X::applies<C::T>(p)
def evaluate(x: nat) -> bool: M<N>::compare<Equality>(x)
// sole package demo::evaluate
")

  check "self-bound" "refuse TY5 10" (defaultMember "1" "(x, x)")
  check "self-bound-valid-body" "accept" (defaultMember "1" "x" ++ admitted)
  check "self-bound-no-candidate" "accept" (defaultMember "2" "(x, x)" ++ admitted)
  check "self-natural-bound" "refuse TY5 7" "module example
interface Methods:
    nat Count
    def f<n: nat>(x: bool) -> bool where (n <= Self::Count)
module M: Methods:
    nat Count = 5
    def f(x): if n == 5 then (x, x) else x
"
  check "self-law-bound" "accept" "module example
interface Mark<n: nat>
module One: Mark<1>:
    nat K = 1
interface Methods:
    nat Count
    law applicable<H: Mark<Self::Count>>(x: bool): x == x
module First: Methods:
    nat Count = 1
module Second: Methods:
    nat Count = 2
// obligations 1
"

end Zkc.Tests.Frontend
