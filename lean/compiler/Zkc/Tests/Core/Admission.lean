import Zkc.Core.Admission.Theorems
import Zkc.Tests.Core.Facts

/-!
`check` and `admit` on programs of functions written by names, run by the kernel.

A program of two functions is admitted with its whole annotation. Admission stops at the first
definition that is refused, with every refusal of that definition and nothing of a later one:
one whose check of facts refuses an application, and one whose elaboration is refused. `check`,
one definition at a time, gives the headers of the admitted program. An association whose key
names a definition is resolved in the admitted program; one whose key is no definition is
refused by the rule `association`. Other cases exercise mixed admission and per-role bounds and refusals.
-/

namespace Zkc.Core.AdmissionTests

open FactsTests (field natural less plus item elements F lengthOf anyNat)

/-- Nothing beyond the definitions. -/
def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- What admission says of a program: its refusals, or the bounds of its annotation. -/
def admission (named : NamedProgram field) : List (AdmissionRefusal field) ⊕ List (Place × Nat) :=
  match admit named noAssociation with
  | .ok admitted => .inr admitted.annotation.bounds
  | .error refusals => .inl refusals

/-- The place of an instruction of the function with the key. -/
def at_ (definition instruction : Nat) : Place := ⟨⟨definition⟩, [], some ⟨instruction⟩, none⟩

/-! ## A program admitted -/

/-- A function that loops as often as its input, which it requires to be below 10. -/
def bounded : Definition field :=
  .fn ⟨1⟩ [.nat] [.nat] true none Summary.empty (.mk [0] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [0, 10],
    .guard ⟨3⟩ () 11 .reject,
    .loop ⟨4⟩ () (.count 0) [] [] (.mk [20] [] [])] [0])

/-- A function that calls `bounded` and loops as often as what it returns, which it requires to
be below 5. -/
def caller : Definition field :=
  .fn ⟨2⟩ [.nat] [.nat] true none Summary.empty (.mk [0] [
    .op ⟨1⟩ [10] (.call ⟨1⟩) [0],
    .op ⟨2⟩ [11] (natural 5) [],
    .op ⟨3⟩ [12] less [10, 11],
    .guard ⟨4⟩ () 12 .reject,
    .loop ⟨5⟩ () (.count 10) [] [] (.mk [20] [] [])] [10])

/-- Both functions are admitted; the annotation has the bound of each loop, the latest
definition's first. -/
example : admission ⟨[bounded, caller]⟩ = .inr [(at_ 2 5, 4), (at_ 1 4, 9)] := by decide +kernel

/-! ## The first refused definition, whole -/

/-- A function that adds its inputs. -/
def addition (key : Nat) : Definition field :=
  .fn ⟨key⟩ [.nat, .nat] [.nat] false none Summary.empty (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10])

/-- A function that reads an item at an index that nothing bounds. -/
def unguarded (key : Nat) : Definition field :=
  .fn ⟨key⟩ [elements, .nat] [F] false none Summary.empty (.mk [0, 1] [.op ⟨1⟩ [10] (item elements) [0, 1]] [10])

/-- A function that reads two items at indices that nothing bounds. -/
def unguardedTwice (key : Nat) : Definition field :=
  .fn ⟨key⟩ [elements, .nat, .nat] [F] false none Summary.empty (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (item elements) [0, 1],
    .op ⟨2⟩ [11] (item elements) [0, 2]] [11])

/-- The refusal of the read of an index that nothing bounds, at an instruction of a function. -/
def unguardedRefusal (key instruction : Nat) : ProgramRefusal field :=
  ⟨.domain, at_ key instruction,
    .unjustified (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]⟩

/-- The second function's check of facts refuses both of its reads: admission gives those two
refusals, and nothing of the third function, which is refused as well. -/
example : admission ⟨[addition 1, unguardedTwice 2, unguarded 3]⟩ =
    .inl [.definition (.fn (unguardedRefusal 2 1)), .definition (.fn (unguardedRefusal 2 2))] := by
  decide +kernel

/-- The first function's elaboration refuses an operand that is not in scope: admission gives
that refusal, and nothing of the second function. -/
example : admission ⟨[.fn ⟨1⟩ [.nat, .nat] [.nat] false none Summary.empty
      (.mk [0, 1] [.op ⟨1⟩ [2] plus [0, 5]] [2]), unguarded 2]⟩ =
    .inl [.definition (.fn ⟨.scope, at_ 1 1, .name 5⟩)] := by
  decide +kernel

/-! ## One definition at a time -/

/-- The headers of `bounded` and `caller`. -/
def boundedHeader : FnHeader field := ⟨⟨1⟩, [.nat], [.nat], true, none, Summary.empty⟩
def callerHeader : FnHeader field := ⟨⟨2⟩, [.nat], [.nat], true, none, Summary.empty⟩

-- The headers that the checks give are compared whole.
deriving instance DecidableEq for EventClass, Shape, Shapes, ProtocolHeader, FnHeader, Headers,
  Except

/-- `check`, one definition at a time from no headers, gives the headers of the admitted
program. -/
example : checkAll check ⟨[], []⟩ [bounded, caller] = .ok ⟨[callerHeader, boundedHeader], []⟩ := by
  decide +kernel
example : (admit ⟨[bounded, caller]⟩ noAssociation).map (·.program.headers) =
    .ok ⟨[callerHeader, boundedHeader], []⟩ := by
  decide +kernel

/-- `check` gives the refusals of a definition, against the headers before it: `caller` alone
calls a function that is not there. -/
example : check ⟨[], []⟩ caller = .error [.definition (.fn ⟨.callee, at_ 2 1, .callee ⟨1⟩ 0⟩)] := by
  rfl

/-! ## The association -/

/-- An association with one instance of the generic declaration with the key 7, at the argument
3, whose definition has the key `definition`. -/
def instanceOf (definition : Nat) : Association :=
  ⟨[⟨⟨7⟩, [.nat 3], ⟨definition⟩⟩], [], [], [], []⟩

/-- What admission says of a program with an association: its refusals, or for each instance
in the association, its generic declaration, its arguments and the key of the definition found
in the program. -/
def resolution (named : NamedProgram field) (association : Association) :
    List (AdmissionRefusal field) ⊕ List (Key × List Static × Key) :=
  match admit named association with
  | .ok admitted =>
      .inr (admitted.association.families.map fun family =>
        (family.generic, family.arguments, family.definition.key))
  | .error refusals => .inl refusals

/-- A key that names a definition of the program: admitted, with that definition found. -/
example : resolution ⟨[addition 1, addition 2]⟩ (instanceOf 2) =
    .inr [(⟨7⟩, [.nat 3], ⟨2⟩)] := by
  decide +kernel

/-- A key that is no definition of the program: refused by the rule `association`, at the
key. -/
example : resolution ⟨[addition 1, addition 2]⟩ (instanceOf 9) =
    .inl [.association (refuseWhole ⟨9⟩ .association (.key ⟨9⟩))] := by
  decide +kernel

/-! ## A protocol -/

/-- A function and an empty protocol are admitted together. -/
example : admission ⟨[addition 1, .protocol ⟨2⟩ 2 [] [] (.mk [] [] [])]⟩ = .inr [] := by
  decide +kernel

private def rolePlace (key instr : Nat) (r : Role) : Place :=
  ⟨⟨key⟩, [], some ⟨instr⟩, some r⟩

/-- Both participants run the bounded loop, while the third one skips its region. -/
private def locatedLoop : Definition field :=
  .protocol ⟨3⟩ 3 [] [] (.mk [] [
    .op ⟨1⟩ [0] (.compute [0,1] (natural 4)) [],
    .loop ⟨2⟩ [0,1] (.count 0) [] [] (.mk [1] [] [])] [])

example : admission ⟨[bounded, locatedLoop, caller]⟩ =
    .inr [(at_ 2 5, 4), (rolePlace 3 2 0, 4), (rolePlace 3 2 1, 4), (at_ 1 4, 9)] := by
  decide +kernel

/-- Each participant sees its own domain obligation when a shared read is out of proof. -/
private def unsafeRead : Definition field :=
  .protocol ⟨4⟩ 3 [⟨elements,[0,1]⟩, ⟨.nat,[0,1]⟩] [] (.mk [0,1]
    [.op ⟨8⟩ [2] (.compute [0,1] (item elements)) [0,1]] [])

private def rejectedReads : Option (List (Place × RoleRaw field)) :=
  match admission ⟨[unsafeRead]⟩ with
  | .inl refusals => refusals.mapM fun
    | .projection ⟨.domain, place, .unjustifiedAssertion op _⟩ => some (place, op)
    | _ => none
  | .inr _ => none

example : rejectedReads =
    some [(rolePlace 4 8 0, .compute [0,1] (item elements)),
     (rolePlace 4 8 1, .compute [0,1] (item elements))] := by decide +kernel

end Zkc.Core.AdmissionTests
