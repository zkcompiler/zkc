import Zkc.Frontend.Driver.SourcePhases
import Zkc.Tests.Frontend.Reference
import ZkcFormal.Written.FiniteModel

/-!
The member that a use of a module parameter's interface calls, where one place of the text is
typed more than once (SP12).

A definition generic over a module parameter is typed twice: the opaque typing chooses, at each
operator and dot call on a type member of the parameter, the member of the interface that it
is, and the typing at the instance reads that choice back by the place in the text. A place in
a loop typed step by step, in a sum typed term by term, or in a comprehension typed by element
is typed once for each, and the choices can differ: members of two modules, or a member in one
typing and a function of the type's own module in another. The instance typing would read one
of them for all, and the program would call the wrong function. Such a definition waits.

Each case is a source with a root: a function `run`, or the protocol of a scheme. The check runs
the frontend and, where the root is admitted, reads the functions that its package reaches and,
for a function, evaluates it in the finite model. A written-out form returns what the source
means and reaches both functions; the loop, the sum and the comprehension of the same calls
wait, with a reason that names the place and both choices; a loop whose receiver does not
change, and a loop over two parameters that stand for one module, are admitted with their
values. The cases vary what the resolution is read through: a dot call and an operator, a
function and a protocol, and module parameters among natural parameters and under a section.
-/

open Zkc Zkc.Core Zkc.Frontend Zkc.Tests.Frontend ZkcFormal.Written

namespace ZkcFormalTests.MemberResolution

/-- What the frontend makes of the root `run` of a source. -/
inductive Outcome where
  /-- The root waits, with this reason. -/
  | waits (reason : String)
  /-- The root is admitted: its value in the finite model, and the functions that its package
  reaches. -/
  | returns (value : Nat) (reached : List String)
  | failed (what : String)

private def closedNat (program : Zkc.Core.Typed Standard) (key : Key) : Option Nat := do
  let some (.fn (hdr := hdr) ref) := program.find key | none
  if hi : hdr.ins = [] then
    if ho : hdr.outs = [.nat] then
      let inputs : HList FiniteModel.model.Val hdr.ins := hi.symm ▸ HList.nil
      let process := fnMeaning FiniteModel.model program ref inputs
      let typed : Local (HList FiniteModel.model.Val [.nat]) := ho ▸ process
      functionResult typed
    else none
  else none

private def value : (b : Zkc.Vocabulary.Project.Bindings) → Zkc.Core.Typed b.vocabulary → Key → Option Nat
  | ⟨[], _⟩, program, key => closedNat program key
  | _, _, _ => none

/-- The frontend on a source, through the typing of its bodies. -/
private def typed (text : String) : Except String Compile.State := do
  let assembly := Id.run <| assemble #[⟨"client.zkc", Syntax.parseString "client.zkc" text⟩]
    fun _ => pure none
  let context := Typing.withProtocolBodies {vocabulary}
  let mut state : Compile.State := {}
  for phase in Driver.sourcePhases assembly do
    state := (phase.runIn context state).2
    if state.log.hasErrors then break
  unless state.log.hasErrors do state := (Typing.typeProgram.run context state).2
  if let some refusal := state.log.entries.find? (·.isError) then
    throw (refusal.render state.env.renderer)
  return state

/-- What the frontend makes of a root: `evaluate` says whether it is a function without
parameters, whose value is read. -/
private def rootOutcome (state : Compile.State) (id : InstanceId) (evaluate : Bool) : Outcome :=
  match Typing.emitRoot state id with
  | .error (.waiting reason) => .waits reason
  | .error (.defect reason) => .failed s!"defect: {reason}"
  | .error (.noCoreForm reason) => .failed s!"no core form: {reason}"
  | .ok emission =>
    let reached := emission.origins.toList.map fun origin =>
      match state.table.entries[origin.definition.number]? with
      | some entry => Static.qualifiedName state.program entry.key.declaration
      | none => "?"
    match (emission.package ⟨[], [], [], [], []⟩).checkEvidence with
    | .error _ => .failed "the package is not admitted"
    | .ok admitted =>
      if evaluate then
        match value emission.bindings admitted.admitted.program ⟨id⟩ with
        | some result => .returns result reached
        | none => .failed "the root has no value in the finite model"
      else .returns 0 reached

/-- What the frontend makes of the root `run` of a source. -/
def outcome (text : String) : Outcome :=
  match typed text with
  | .error refusal => .failed refusal
  | .ok state =>
    match state.results.roots.find? fun (id, _) => (Static.renderInstance state id).endsWith "run" with
    | some (id, _) => rootOutcome state id true
    | none => .failed "no root `run`"

/-- What the frontend makes of the protocol of the scheme of a source. Its value is not read. -/
def protocolOutcome (text : String) : Outcome :=
  match typed text with
  | .error refusal => .failed refusal
  | .ok state =>
    match state.results.schemes[0]? with
    | some scheme => rootOutcome state scheme.protocol false
    | none => .failed "no scheme"

/-- Two modules implement one interface over one record, and `digit` is 3 in the first and 9 in
the second. -/
def twoModules (body call : String) : String :=
  "module client\n" ++
  "pub struct Box:\n    pub n: nat\n" ++
  "interface Carrier:\n    type T\n    def digit(a: T) -> nat\n" ++
  "module First: Carrier:\n    type T = Box\n    def digit(a): 3\n" ++
  "module Other: Carrier:\n    type T = Box\n    def digit(a): 9\n" ++
  "pub def f<X: Carrier, Y: Carrier>(x: X::T, y: Y::T) -> nat:\n" ++ body ++
  s!"pub def run() -> nat: {call}(Box\{n = 0}, Box\{n = 0})\n"

/-- One module, and a function `digit` of the record's own module, which is 5. -/
def moduleAndHome (body : String) : String :=
  "module client\n" ++
  "pub struct Box:\n    pub n: nat\n" ++
  "pub def digit(a: Box) -> nat: 5\n" ++
  "interface Carrier:\n    type T\n    def digit(a: T) -> nat\n" ++
  "module First: Carrier:\n    type T = Box\n    def digit(a): 3\n" ++
  "pub def f<X: Carrier>(x: X::T) -> nat:\n" ++ body ++
  "pub def run() -> nat: f<First>(Box{n = 0})\n"

/-- Two modules whose `equal`, the member that `==` is, differs: true in the first and false in
the second. -/
def twoEqualities (body : String) : String :=
  "module client\n" ++
  "pub struct Box:\n    pub n: nat\n" ++
  "interface Carrier:\n    type T\n    def equal(a: T, b: T) -> bool\n" ++
  "module First: Carrier:\n    type T = Box\n    def equal(a, b): true\n" ++
  "module Other: Carrier:\n    type T = Box\n    def equal(a, b): false\n" ++
  "pub def f<X: Carrier, Y: Carrier>(x: X::T, y: Y::T) -> nat:\n" ++ body ++
  "pub def run() -> nat: f<First, Other>(Box{n = 0}, Box{n = 0})\n"

/-- The two modules of `twoModules`, and a function with the given static parameters. -/
def withParameters (parameters body call : String) : String :=
  ((twoModules body call).replace "f<X: Carrier, Y: Carrier>" s!"f<{parameters}>")

/-- The two modules of `twoModules`, with the function under a section: one module parameter and
one natural of the section, one natural and one module parameter of its own. -/
def underSection (body call : String) : String :=
  "module client\n" ++
  "pub struct Box:\n    pub n: nat\n" ++
  "interface Carrier:\n    type T\n    def digit(a: T) -> nat\n" ++
  "module First: Carrier:\n    type T = Box\n    def digit(a): 3\n" ++
  "module Other: Carrier:\n    type T = Box\n    def digit(a): 9\n" ++
  "section <k: nat, X: Carrier>:\n" ++
  "    pub def f<j: nat, Y: Carrier>(x: X::T, y: Y::T) -> nat:\n" ++
  "\n".intercalate ((body.splitOn "\n").map fun line => if line.isEmpty then line else "    " ++ line) ++
  s!"pub def run() -> nat: {call}(Box\{n = 0}, Box\{n = 0})\n"

/-- The two modules of `twoModules`, and a protocol generic over both, deployed by a scheme. -/
def protocolOf (body scheme : String) : String :=
  "module client\n" ++
  "pub struct Box:\n    pub n: nat\n" ++
  "interface Carrier:\n    type T\n    def digit(a: T) -> nat\n" ++
  "module First: Carrier:\n    type T = Box\n    def digit(a): 3\n" ++
  "module Other: Carrier:\n    type T = Box\n    def digit(a): 9\n" ++
  "pub protocol Walk<X: Carrier, Y: Carrier> roles(P, V)(x: X::T @(P, V), y: Y::T @(P, V))" ++
  " -> out: nat @(P, V):\n" ++ body ++
  s!"scheme Checked = {scheme}:\n    prover P\n    construction interactive\n"

def loop (count : Nat) (first next : String) : String :=
  s!"    mut z = {first}\n    mut acc: nat = 0\n    for i in 0..{count}:\n" ++
  s!"        acc := 10 * acc + z.digit()\n        z := {next}\n    return acc\n"

def first := "client::First::digit"
def other := "client::Other::digit"
def home := "client::digit"

/-- The root is admitted, returns `expected`, and of the functions named `digit` reaches exactly
`members`. -/
def expectValue (name : String) (found : Outcome) (expected : Nat) (members : List String) :
    IO Unit := do
  match found with
  | .returns result reached =>
    unless result == expected do
      throw (IO.userError s!"{name}: returns {result}, and the source means {expected}")
    for member in members do
      unless reached.contains member do
        throw (IO.userError s!"{name}: does not reach {member}; it reaches {reached}")
    for member in [first, other, home] do
      if reached.contains member && !members.contains member then
        throw (IO.userError s!"{name}: reaches {member}, which the source does not call")
  | .waits reason => throw (IO.userError s!"{name}: waits: {reason}")
  | .failed what => throw (IO.userError s!"{name}: {what}")

/-- The root waits, for a reason that has each of `parts`. -/
def expectWait (name : String) (found : Outcome) (parts : List String) : IO Unit := do
  match found with
  | .waits reason =>
    for part in parts do
      unless (reason.splitOn part).length > 1 do
        throw (IO.userError s!"{name}: waits for another reason: {reason}")
  | .returns result reached =>
    throw (IO.userError s!"{name}: is admitted and returns {result}, reaching {reached}")
  | .failed what => throw (IO.userError s!"{name}: {what}")

/-- What the reason of a wait says of two members. -/
def twoMembers := ["typed more than once", "the member `digit` of `X`", "the member `digit` of `Y`"]

/-- What the reason of a wait says of a member and a function of the home module. -/
def memberAndHome := ["typed more than once", "the member `digit` of `X`", "as no member"]

/-- The written-out form of the loop of two. -/
def writtenOut := "    return 10 * x.digit() + y.digit()\n"

/-- A loop in which `==` is applied to the receiver. -/
def equalityLoop :=
  "    mut z = x\n    mut acc: nat = 0\n    for i in 0..2:\n" ++
  "        acc := 10 * acc + (if z == z then 1 else 2)\n        z := y\n    return acc\n"

#eval show IO Unit from do
  -- the calls written out: the source's meaning, and both members
  expectValue "written out" (outcome (twoModules writtenOut "f<First, Other>")) 39 [first, other]
  expectValue "written out, modules exchanged" (outcome (twoModules writtenOut "f<Other, First>")) 93
    [first, other]
  -- the same calls in a loop: one place, typed once for each iteration, with two members
  expectWait "loop of two" (outcome (twoModules (loop 2 "x" "y") "f<First, Other>")) twoMembers
  expectWait "loop of three" (outcome (twoModules (loop 3 "x" "y") "f<First, Other>")) twoMembers
  expectWait "loop of two, modules exchanged" (outcome (twoModules (loop 2 "x" "y") "f<Other, First>"))
    twoMembers
  -- a place typed once, or never, has one member
  expectValue "loop of one" (outcome (twoModules (loop 1 "x" "y") "f<First, Other>")) 3 [first]
  expectValue "loop of none" (outcome (twoModules (loop 0 "x" "y") "f<First, Other>")) 0 []
  -- two parameters that stand for one module choose one member
  expectValue "loop of two, one module twice" (outcome (twoModules (loop 2 "x" "y") "f<First, First>"))
    33 [first]
  -- a receiver that does not change is typed once
  expectValue "loop of two, one receiver" (outcome (twoModules (loop 2 "x" "x") "f<First, Other>")) 33
    [first]
  -- a sum typed term by term and a comprehension typed by element, over a tuple
  expectValue "tuple, written out"
    (outcome (twoModules "    t = (x, y)\n    return t[0].digit() + t[1].digit()\n" "f<First, Other>"))
    12 [first, other]
  expectWait "sum over a tuple"
    (outcome (twoModules "    t = (x, y)\n    return ∑ i ∈ 0..2, t[i].digit()\n" "f<First, Other>"))
    twoMembers
  expectWait "comprehension over a tuple"
    (outcome (twoModules ("    t = (x, y)\n    ds = [t[i].digit() for i in 0..2]\n" ++
      "    return 10 * ds[0] + ds[1]\n") "f<First, Other>")) twoMembers
  -- a member in one typing and a function of the record's own module in another
  expectValue "member then home, written out"
    (outcome (moduleAndHome "    z = x\n    w = Box{n = 0}\n    return 10 * z.digit() + w.digit()\n"))
    35 [first, home]
  expectWait "member then home" (outcome (moduleAndHome (loop 2 "x" "Box{n = 0}"))) memberAndHome
  expectValue "home then member, written out"
    (outcome (moduleAndHome "    z = Box{n = 0}\n    w = x\n    return 10 * z.digit() + w.digit()\n"))
    53 [first, home]
  expectWait "home then member" (outcome (moduleAndHome (loop 2 "Box{n = 0}" "x"))) memberAndHome
  -- an operator: `==` is the member `equal`
  expectValue "operator, written out" (outcome (twoEqualities
    "    return 10 * (if x == x then 1 else 2) + (if y == y then 1 else 2)\n")) 12 []
  expectWait "operator in a loop" (outcome (twoEqualities equalityLoop))
    ["typed more than once", "the member `equal` of `X`", "the member `equal` of `Y`"]
  -- the module parameters among natural parameters: the instance's values are read by position
  for (parameters, call) in [("k: nat, X: Carrier, Y: Carrier", "f<5, First, Other>"),
      ("X: Carrier, k: nat, Y: Carrier", "f<First, 5, Other>"),
      ("X: Carrier, Y: Carrier, k: nat", "f<First, Other, 5>")] do
    expectValue s!"written out, {call}" (outcome (withParameters parameters writtenOut call)) 39
      [first, other]
    expectWait s!"loop of two, {call}" (outcome (withParameters parameters (loop 2 "x" "y") call))
      twoMembers
  expectValue "loop of two, one module twice after a natural"
    (outcome (withParameters "k: nat, X: Carrier, Y: Carrier" (loop 2 "x" "y") "f<5, First, First>"))
    33 [first]
  -- parameters of a section and of the definition
  expectValue "under a section, written out"
    (outcome (underSection writtenOut "f<k = 5, X = First, j = 6, Y = Other>")) 39 [first, other]
  expectWait "under a section, loop of two"
    (outcome (underSection (loop 2 "x" "y") "f<k = 5, X = First, j = 6, Y = Other>")) twoMembers
  expectValue "under a section, one module twice"
    (outcome (underSection (loop 2 "x" "y") "f<k = 5, X = First, j = 6, Y = First>")) 33 [first]
  -- a protocol generic over the two modules
  expectValue "protocol, written out" (protocolOutcome (protocolOf writtenOut "Walk<First, Other>")) 0
    [first, other]
  expectWait "protocol, loop of two" (protocolOutcome (protocolOf (loop 2 "x" "y") "Walk<First, Other>"))
    twoMembers
  expectValue "protocol, one module twice"
    (protocolOutcome (protocolOf (loop 2 "x" "y") "Walk<First, First>")) 0 [first]
  IO.println ("a place typed more than once with different members waits (13 cases); the " ++
    "written-out forms and the places with one member mean what the source says (19 cases)")

end ZkcFormalTests.MemberResolution
