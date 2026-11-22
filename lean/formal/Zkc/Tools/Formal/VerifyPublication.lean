import Lean
import Lean.Replay

/-!
The check of a generated proof module outside the file.

A check of a subject runs Lean on a module that contains an author's text, and a text is
arbitrary Lean: it can turn off the kernel's check of its declarations, or write into the
kernel's environment, and Lean then accepts a false theorem and reports no axiom for it. This
program does not read what Lean printed. It reads the object that Lean compiled from the proof
module (the candidate). The propositions that the candidate has to prove are not in it: they
are declarations of the module of the statements, which the generator wrote with no text, which
the check compiled before the proof module, and which the candidate imports. Then:

- the candidate imports the module of the statements, and declares no name that an import has:
  a text cannot put another declaration under a name of the statements or of the library;
- the kernel **replays** the declarations of the candidate on its imports, so a declaration that
  the file's elaboration left unchecked is checked here, against the imports as they were
  compiled, and refused if it does not hold. Lean's replay leaves out what the kernel never
  checks: a declaration marked `unsafe`, and the compiled body of a `partial` definition. Those
  are code; no theorem can use them, and the constant that a `partial` definition gives to
  proofs is replayed;
- each published theorem is read from the result of that replay: it is a theorem of the
  candidate, with no parameter of a universe, whose stored type is the constant of its
  proposition, and the proposition is a closed proposition that **the module of the statements
  declares** (the module that owns the name among the imports). Every pair that fails is named;
- the axioms of each published theorem, and then of every declaration of the candidate that
  the kernel checks, are read from the replayed proofs, and are among the allowed ones. Code
  that the replay leaves out (an `unsafe` definition, the compiled body of a `partial` one) is
  not walked: no theorem can use it, and a text may have it.

The imports are trusted: they are loaded as compiled, through the artifacts that the setup
names, and are not replayed. The setup is the one that the proof module was compiled with: what
Lake names for the imports of the generator and of the text, and for the name of the module of
the statements the object that the check compiled. The check writes it, and the manifest, where
a text cannot write.

- each theorem that the check lists for the proof module (those of the text, and what a check
  writes after the closing theorems) is a theorem of the candidate after the replay. A text can
  make a later command of the module elaborate nothing; the theorem that the command would have
  stated is then missing from the object, and Lean says nothing.

Arguments: the setup of the proof module, the manifest, and the object of the proof module. The
manifest is a JSON object: `statements`, the name of the module of the statements; `allowed`,
the allowed axioms; `pairs`, each published theorem with its proposition; `theorems`, the
theorems that the proof module has to have. A name is the list of its components.
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

/-- The axioms that declarations rest on, read from the replayed declarations. -/
partial def axiomsOf (env : Kernel.Environment) (todo : List Name)
    (seen axioms : NameSet := {}) : IO (Array Name) := do
  let n :: rest := todo | return axioms.toArray.qsort Name.lt
  if seen.contains n then return ← axiomsOf env rest seen axioms
  let some ci := env.find? n | throw <| IO.userError s!"a proof uses a name that nothing declares: {n}"
  let axioms := if ci matches .axiomInfo _ then axioms.insert n else axioms
  axiomsOf env (dependencies ci ++ rest) (seen.insert n) axioms

/-- What a check asks of a proof module. -/
structure Manifest where
  /-- The name of the module of the statements. -/
  statements : Name
  /-- The axioms beyond which nothing of the proof module may rest. -/
  allowed : List Name
  /-- Each published theorem with its proposition. -/
  pairs : List (Name × Name)
  /-- The theorems that the proof module has to have, the published ones among them or not. -/
  theorems : List Name

/-- A name from the list of its components. -/
def nameOf (json : Json) : Except String Name := do
  (← json.getArr?).foldlM (fun name part => return .str name (← part.getStr?)) .anonymous

def Manifest.read (path : System.FilePath) : IO Manifest := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept do
    let statements ← nameOf (← json.getObjVal? "statements")
    let allowed ← (← (← json.getObjVal? "allowed").getArr?).toList.mapM nameOf
    let pairs ← (← (← json.getObjVal? "pairs").getArr?).toList.mapM fun pair => do
      let #[theorem_, proposition] ← pair.getArr?
        | throw "a pair of the manifest is a theorem and its proposition"
      return (← nameOf theorem_, ← nameOf proposition)
    let theorems ← (← (← json.getObjVal? "theorems").getArr?).toList.mapM nameOf
    return { statements, allowed, pairs, theorems }

/-- Why a published theorem is not of its proposition, where it is not: the proposition is a
closed proposition that the module of the statements declares, and the theorem is a theorem of
the candidate whose stored type, after the replay, is the constant of the proposition. -/
def unpublished (manifest : Manifest) (candidate : Declarations) (imports : Environment)
    (checked : Kernel.Environment) (theorem_ proposition : Name) : Option String :=
  let owner := (imports.getModuleIdxFor? proposition).bind (imports.header.moduleNames[·.toNat]?)
  if owner != some manifest.statements then
    some s!"`{proposition}` is not declared by `{manifest.statements}`"
  else match imports.toKernelEnv.find? proposition with
    | some (.defnInfo stated) =>
      if !(stated.levelParams.isEmpty && stated.type == mkSort .zero) then
        some s!"`{proposition}` is no closed proposition"
      else if !candidate.contains theorem_ then
        some s!"the candidate does not declare the theorem `{theorem_}`"
      else match checked.find? theorem_ with
        | some (.thmInfo proved) =>
          if proved.levelParams.isEmpty && proved.type == mkConst proposition then none
          else some s!"`{theorem_}` is not of the proposition `{proposition}`"
        | _ => some s!"`{theorem_}` is no theorem after the replay"
    | _ => some s!"`{proposition}` is no definition of `{manifest.statements}`"

/-- The published theorems are of their propositions, which the module of the statements
declares, and the theorems, with every declaration of the candidate, rest on the allowed
axioms. -/
def publications (manifest : Manifest) (candidate : Declarations) (imports : Environment)
    (checked : Kernel.Environment) : IO Unit := do
  if manifest.pairs.isEmpty then throw <| IO.userError "no published theorem was named"
  let failures := (manifest.pairs.filterMap fun (theorem_, proposition) =>
    unpublished manifest candidate imports checked theorem_ proposition) ++
    manifest.theorems.filterMap fun theorem_ =>
      if candidate.contains theorem_ && (checked.find? theorem_ matches some (.thmInfo _)) then none
      else some s!"the candidate does not have the theorem `{theorem_}`, which the check lists"
  unless failures.isEmpty do throw <| IO.userError ("\n".intercalate failures)
  let base := imports.toKernelEnv
  let within (axioms : Array Name) : Bool :=
    axioms.all fun a => manifest.allowed.contains a && (base.find? a matches some (.axiomInfo _))
  -- one walk for all the published theorems, which share most of what they use; where it
  -- finds an axiom beyond the allowed ones, each theorem is walked to say which rests on it
  let axioms ← axiomsOf checked (manifest.pairs.map (·.1))
  unless within axioms do
    for (theorem_, _) in manifest.pairs do
      let own ← axiomsOf checked [theorem_]
      unless within own do
        throw <| IO.userError s!"`{theorem_}` rests on {own}, beyond {manifest.allowed}"
    throw <| IO.userError s!"the published theorems rest on {axioms}, beyond {manifest.allowed}"
  -- and nothing else that the candidate declares rests on another axiom: every declaration
  -- of it that the replay checked (the replay leaves out `unsafe` and `partial` ones)
  let whole ← axiomsOf checked
    (candidate.toList.filterMap fun (n, c) => if c.isUnsafe || c.isPartial then none else some n)
  unless within whole do
    throw <| IO.userError s!"the candidate rests on {whole}, beyond {manifest.allowed}"
  for (theorem_, proposition) in manifest.pairs do
    IO.println s!"replayed {theorem_} : {proposition}"
  IO.println s!"axioms of the candidate: {whole}"

def run (args : List String) : IO Unit := do
  let [setupPath, manifestPath, candidatePath] := args
    | throw <| IO.userError "expected: the setup of the proof module, the manifest, the object of the proof module"
  let manifest ← Manifest.read manifestPath
  let setup ← ModuleSetup.load setupPath
  initSearchPath (← findSysroot)
  unless (setup.importArts.find? manifest.statements).isSome do
    throw <| IO.userError s!"the setup names no object for `{manifest.statements}`, the module of the statements"
  let (candidateData, _) ← readModuleData candidatePath
  let candidate ← declarations candidateData
  unless candidateData.imports.any (·.module == manifest.statements) do
    throw <| IO.userError s!"the candidate does not import `{manifest.statements}`, the module of the statements"
  -- the candidate's imports, as compiled: both parts of the `Zkc` namespace through Lake's
  -- artifacts, and the module of the statements as the check compiled it
  let (_, state) ← importModulesCore candidateData.imports (arts := setup.importArts) |>.run
  let imports ← finalizeImport state candidateData.imports {} 0 false false (isModule := true)
  let base := imports.toKernelEnv
  for (n, _) in candidate do
    if (base.find? n).isSome then
      throw <| IO.userError s!"the candidate declares `{n}`, which an import has"
  -- the kernel on the declarations of the candidate (all but `unsafe` ones and the compiled
  -- bodies of `partial` definitions, which the kernel does not check and no proof can use)
  let checked ←
    try base.replay candidate
    catch refusal =>
      throw <| IO.userError s!"the kernel refuses a declaration of the candidate on replay\n{refusal}"
  publications manifest candidate imports checked

end Zkc.Tools.Formal.VerifyPublication

def main (args : List String) : IO Unit := Zkc.Tools.Formal.VerifyPublication.run args
