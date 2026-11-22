import Lean
import Lean.Replay

/-!
The check of a generated proof module outside the file.

A check of a subject runs Lean on a module that contains an author's text, and a text is
arbitrary Lean: it can turn off the kernel's check of its declarations, and Lean then accepts a
false theorem and reports no axiom for it. This program does not read what Lean printed. It
reads two objects that Lean compiled: the proof module (the candidate), and the module that the
generator writes without the text (the reference: the package and the propositions of the
goals, under the imports that the generator's statements need and none that a text asked for).
Then:

- the kernel **replays** the declarations of the candidate on the imports, so a declaration
  that the file's elaboration left unchecked is checked here, and refused if it does not hold.
  Lean's replay leaves out what the kernel never checks: a declaration marked `unsafe`, and the
  compiled body of a `partial` definition. Those are code; no theorem can use them, and the
  constant that a `partial` definition gives to proofs is replayed;
- each published theorem is read from the result of that replay, and is of its proposition
  under its full name, with no parameter of a universe;
- each such proposition, and every declaration of the module that it uses, is in the replayed
  candidate **the declaration that the reference has**: the text cannot have given the
  proposition, or a definition under it, another meaning;
- the axioms of each published theorem are read from the replayed proofs, and are among the
  allowed ones.

The imports are trusted: they are loaded as compiled, through the artifacts that Lake names for
the candidate's header, and are not replayed. The candidate imports what the reference imports,
and may import more (what a text asked for); it must declare no name that an import has. A
proposition that an import of the text made mean something else is then not the reference's
declaration, and is refused.

Arguments: the setup of the candidate as Lake prints it (`lake setup-file`), the object of the
reference, the object of the candidate, the allowed axioms separated by commas, and then each
published theorem with its proposition as `theorem=proposition`.
-/

open Lean

namespace Zkc.Tools.Formal.VerifyPublication

abbrev Declarations := Std.HashMap Name ConstantInfo

/-- The declarations of a compiled module, by name. -/
def declarations (m : ModuleData) : IO Declarations := do
  if m.isModule then throw <| IO.userError "the object is of a module of the module system"
  unless m.constNames.size == m.constants.size do
    throw <| IO.userError "the object's table of names does not fit its declarations"
  let mut map : Declarations := {}
  for n in m.constNames, c in m.constants do
    unless n == c.name && !map.contains n do
      throw <| IO.userError s!"a name is declared twice or under another name: {n}"
    map := map.insert n c
  return map

/-- The names that a declaration uses: in its type and its value, and for an inductive type its
family, its constructors' type and the rules of its recursor. -/
def dependencies (ci : ConstantInfo) : List Name :=
  let used := ci.getUsedConstantsAsSet.toList
  match ci with
  | .inductInfo v => v.all ++ used
  | .ctorInfo v => v.induct :: used
  | .recInfo v =>
    v.rules.foldl (init := used) fun acc r => r.ctor :: r.rhs.getUsedConstantsAsSet.toList ++ acc
  | _ => used

/-- Each of `roots`, and every declaration of the reference that it uses, is in the replayed
candidate the declaration that the reference has. A name that the reference does not declare is
one of the imports, which both modules share. -/
partial def sameAsReference (reference : Declarations) (base checked : Kernel.Environment)
    (roots : List Name) (seen : NameSet := {}) : IO Unit := do
  let n :: rest := roots | return
  if seen.contains n then return ← sameAsReference reference base checked rest seen
  let seen := seen.insert n
  let some expected := reference[n]? | do
    unless (base.find? n).isSome do
      throw <| IO.userError s!"the reference uses a name that nothing declares: {n}"
    return ← sameAsReference reference base checked rest seen
  let some actual := checked.find? n
    | throw <| IO.userError s!"the candidate does not declare `{n}`, which the reference does"
  unless actual == expected do
    let differs :=
      if actual.type != expected.type then "its type differs"
      else if actual.levelParams != expected.levelParams then "its universe parameters differ"
      else match actual, expected with
        | .defnInfo a, .defnInfo e => if a.value != e.value then "its value differs" else "its hints or safety differ"
        | .thmInfo _, .thmInfo _ => "its proof differs"
        | .opaqueInfo _, .opaqueInfo _ => "its value differs"
        | .inductInfo _, .inductInfo _ => "its family, parameters or constructors differ"
        | .ctorInfo _, .ctorInfo _ => "its place in its type differs"
        | .recInfo _, .recInfo _ => "its rules differ"
        | .axiomInfo _, .axiomInfo _ => "its safety differs"
        | .quotInfo _, .quotInfo _ => "its kind differs"
        | _, _ => "it is a declaration of another kind"
    throw <| IO.userError s!"`{n}` is not the declaration that the reference has: {differs}"
  sameAsReference reference base checked (dependencies expected ++ rest) seen

/-- The axioms that a declaration rests on, read from the replayed declarations. -/
partial def axiomsOf (env : Kernel.Environment) (todo : List Name)
    (seen axioms : NameSet := {}) : IO (Array Name) := do
  let n :: rest := todo | return axioms.toArray.qsort Name.lt
  if seen.contains n then return ← axiomsOf env rest seen axioms
  let some ci := env.find? n | throw <| IO.userError s!"a proof uses a name that nothing declares: {n}"
  let axioms := if ci matches .axiomInfo _ then axioms.insert n else axioms
  axiomsOf env (dependencies ci ++ rest) (seen.insert n) axioms

/-- The published theorems are of their propositions, the propositions are the reference's, and
the theorems rest on the allowed axioms. -/
def publications (reference candidate : Declarations) (base checked : Kernel.Environment)
    (allowed : List Name) (pairs : List (Name × Name)) : IO Unit := do
  if pairs.isEmpty then throw <| IO.userError "no published theorem was named"
  for (theorem_, proposition) in pairs do
    let some (.defnInfo stated) := reference[proposition]?
      | throw <| IO.userError s!"the reference does not define the proposition `{proposition}`"
    unless stated.levelParams.isEmpty && stated.type == mkSort .zero do
      throw <| IO.userError s!"`{proposition}` of the reference is no closed proposition"
    unless candidate.contains theorem_ do
      throw <| IO.userError s!"the candidate does not declare the theorem `{theorem_}`"
    let some (.thmInfo proved) := checked.find? theorem_
      | throw <| IO.userError s!"`{theorem_}` is no theorem after the replay"
    unless proved.levelParams.isEmpty && proved.type == mkConst proposition do
      throw <| IO.userError s!"`{theorem_}` is not of the proposition `{proposition}`"
  sameAsReference reference base checked (pairs.map (·.2))
  let within (axioms : Array Name) : Bool :=
    axioms.all fun a => allowed.contains a && (base.find? a matches some (.axiomInfo _))
  -- one walk for all the published theorems, which share most of what they use; where it
  -- finds an axiom beyond the allowed ones, each theorem is walked to say which rests on it
  let axioms ← axiomsOf checked (pairs.map (·.1))
  unless within axioms do
    for (theorem_, _) in pairs do
      let own ← axiomsOf checked [theorem_]
      unless within own do
        throw <| IO.userError s!"`{theorem_}` rests on {own}, beyond {allowed}"
    throw <| IO.userError s!"the published theorems rest on {axioms}, beyond {allowed}"
  for (theorem_, proposition) in pairs do
    IO.println s!"replayed {theorem_} : {proposition}"
  IO.println s!"axioms of the published theorems: {axioms}"

def run (args : List String) : IO Unit := do
  let setupPath :: referencePath :: candidatePath :: allowed :: pairs := args
    | throw <| IO.userError "expected: the candidate's setup, reference object, candidate object, allowed axioms, theorem=proposition …"
  let pairs ← pairs.mapM fun pair => match pair.splitOn "=" with
    | [theorem_, proposition] => pure (theorem_.toName, proposition.toName)
    | _ => throw <| IO.userError s!"not `theorem=proposition`: {pair}"
  let allowed := (allowed.splitOn ",").filter (· ≠ "") |>.map String.toName
  let setup ← ModuleSetup.load setupPath
  initSearchPath (← findSysroot)
  let (referenceData, _) ← readModuleData referencePath
  let (candidateData, _) ← readModuleData candidatePath
  let reference ← declarations referenceData
  let candidate ← declarations candidateData
  for needed in referenceData.imports do
    unless candidateData.imports.contains needed do
      throw <| IO.userError s!"the candidate does not import `{needed.module}`, which the reference imports"
  -- the candidate's imports, as compiled: both parts of the `Zkc` namespace through Lake's
  -- artifacts
  let (_, state) ← importModulesCore candidateData.imports (arts := setup.importArts) |>.run
  let base :=
    (← finalizeImport state candidateData.imports {} 0 false false (isModule := true)).toKernelEnv
  for (n, _) in candidate do
    if (base.find? n).isSome then
      throw <| IO.userError s!"the candidate declares `{n}`, which an import has"
  -- the kernel on the declarations of the candidate (all but `unsafe` ones and the compiled
  -- bodies of `partial` definitions, which the kernel does not check and no proof can use)
  let checked ←
    try base.replay candidate
    catch refusal =>
      throw <| IO.userError s!"the kernel refuses a declaration of the candidate on replay\n{refusal}"
  publications reference candidate base checked allowed pairs

end Zkc.Tools.Formal.VerifyPublication

def main (args : List String) : IO Unit := Zkc.Tools.Formal.VerifyPublication.run args
