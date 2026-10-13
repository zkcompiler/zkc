module

public import Zkc.Source.Decoding

@[expose] public section

/-! Exact admission of selected native constructed participants.

Native type names are nominal; a semantic consumer explicitly supplies primitive
meanings. Local bodies have already been expanded by the checked native exporter.
No field in this vocabulary asserts construction or cryptographic soundness.
-/

set_option autoImplicit false
namespace Zkc.Source.Constructed

/-- A primitive leaf, including the complete native signature and binding.
`origin` identifies the participant and selected Local invocation chain. -/
structure Primitive where
  name : String
  attributes : String
  binding : String
  origin : String
  arguments : List String
  results : List String
  deriving DecidableEq, Repr

/-- Products preserve all primitive replies, including successor state. -/
abbrev Ty := List String

def scalar (ty : String) : Ty := [ty]

inductive Op where
  | primitive (operation : Primitive)
  | project (types : List String) (index : Fin types.length)
  | pack (types : List String)
  deriving DecidableEq, Repr

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .primitive op => op.arguments.map scalar
    | .project types _ => [types]
    | .pack types => types.map scalar
  result
    | .primitive op => op.results
    | .project types index => [types[index]]
    | .pack types => types
  condition := ["i1"]

inductive Instruction where
  | apply (operation : Primitive) (arguments : List Nat)
  | project (types : List String) (index tuple : Nat)
  | guard (condition : Nat) (attributes : String)
  | stop (reason : PIR.Stop) (attributes : String)
  deriving DecidableEq, Repr

/-- Flat JSON avoids imposing a JSON recursion limit on straight-line code. -/
def lower (outputs : List String) (returned : List Nat) :
    List Instruction → Except String (RawProgram Ty Op)
  | [] => .ok (.letOp (.pack outputs) returned (.ret 0))
  | .apply operation arguments :: rest => do
      return .letOp (.primitive operation) arguments (← lower outputs returned rest)
  | .project types index tuple :: rest => do
      if h : index < types.length then
        return .letOp (.project types ⟨index, h⟩) [tuple] (← lower outputs returned rest)
      else throw "constructed-source-project"
  | .guard condition _ :: rest => do
      return .branch condition (← lower outputs returned rest) (.stop .reject)

  | .stop reason _ :: rest =>
      if rest.isEmpty && returned.isEmpty then .ok (.stop reason)
      else .error "constructed-source-stop-tail"

structure Handler where
  name : String
  digest : String
  body : String
  deriving DecidableEq, Repr

structure Snapshot where
  source : String
  candidate : String
  entry : String
  role : String
  participant : String
  policy : String
  handlers : List Handler
  inputs : List String
  outputs : List String
  instructions : List Instruction
  returned : List Nat
  deriving DecidableEq, Repr

def Snapshot.raw (snapshot : Snapshot) : Except String (RawProgram Ty Op) :=
  lower snapshot.outputs snapshot.returned snapshot.instructions

/-- Identity metadata is not authentication. Native re-extraction is required. -/
def Snapshot.shapeValid (s : Snapshot) : Bool :=
  !s.entry.isEmpty && !s.role.isEmpty && !s.participant.isEmpty &&
  s.source.toList.take 7 == "sha256:".toList && s.source.length == 71 &&
  s.candidate.toList.take 7 == "sha256:".toList && s.candidate.length == 71 &&
  s.inputs.length ≤ 512 && s.outputs.length ≤ 512 &&
  s.instructions.length ≤ 2048 && s.handlers.length ≤ 256 &&
  (match s.instructions.getLast? with
    | some (.stop ..) => s.returned.isEmpty
    | _ => s.returned.length == s.outputs.length) &&
  (s.handlers.map Handler.name).eraseDups.length == s.handlers.length

structure Imported (snapshot : Snapshot) where
  program : Program language (snapshot.inputs.map scalar) snapshot.outputs

/-- The extra erasure check makes exact syntax preservation part of admission,
including unused effects and both sides of each guard. It is executable, not a
supplied correspondence premise. -/
def Snapshot.check (snapshot : Snapshot) : Except String (Imported snapshot) :=
  if snapshot.shapeValid then
    match snapshot.raw with
    | .error e => .error e
    | .ok raw =>
      match raw.elaborate (language := language) (snapshot.inputs.map scalar) snapshot.outputs with
      | .error _ => .error "constructed-source-operands"
      | .ok program =>
        if program.erase = raw then .ok ⟨program⟩ else .error "constructed-source-erasure"
  else .error "constructed-source-shape"

/-- Extract only an actually successful check, without a default program. -/
def Snapshot.imported (s : Snapshot) (checked : s.check.isOk = true) : Imported s :=
  match eq : s.check with
  | .ok imported => imported
  | .error _ => by simp [eq, Except.isOk, Except.toBool] at checked

theorem Snapshot.imported_checked (s : Snapshot) (checked : s.check.isOk = true) :
    s.check = .ok (s.imported checked) := by
  unfold Snapshot.imported
  split
  · assumption
  · rename_i e eq
    rw [eq] at checked
    contradiction

/-- All data movement introduced by import has a fixed mathematical meaning.
Only actual native primitive leaves require a selected provider interpretation. -/
structure Meaning (interface : PIR.Signature) where
  Value : String → Type
  condition : Value "i1" → Bool
  primitive : (op : Primitive) → Values Value op.arguments →
    PIR.Proc interface (Values Value op.results)

def unpack {V : String → Type} : (types : List String) →
    Values (Values V) (types.map scalar) → Values V types
  | [], .nil => .nil
  | _ :: types, .cons (.cons value .nil) rest => .cons value (unpack types rest)

def tupleAt {V : String → Type} {types : List String}
    (values : Values V types) (index : Fin types.length) : V types[index] :=
  match types, values, index with
  | _ :: _, .cons value _, ⟨0, _⟩ => value
  | _ :: _, .cons _ rest, ⟨n + 1, h⟩ => tupleAt rest ⟨n, Nat.lt_of_succ_lt_succ h⟩

def Meaning.interpretation {I : PIR.Signature} (meaning : Meaning I) :
    Interpretation language I where
  Value := Values meaning.Value
  condition := fun (.cons value .nil) => meaning.condition value
  operation
    | .primitive op, args => meaning.primitive op (unpack op.arguments args)
    | .project _ index, .cons tuple .nil => .done (.cons (tupleAt tuple index) .nil)
    | .pack types, args => .done (unpack types args)

def Imported.denote {snapshot : Snapshot} (imported : Imported snapshot)
    {I : PIR.Signature} (meaning : Meaning I)
    (inputs : Values (Values meaning.Value) (snapshot.inputs.map scalar)) :
    PIR.Proc I (Values meaning.Value snapshot.outputs) :=
  imported.program.denote meaning.interpretation inputs.get

/-- Exact erasure is established by the executable checker for its actual output. -/
theorem Snapshot.check_exact {s : Snapshot} {imported : Imported s}
    (checked : s.check = .ok imported) :
    s.raw = .ok imported.program.erase := by
  unfold Snapshot.check at checked
  split at checked
  · cases rawEq : s.raw with
    | error e => simp [rawEq] at checked
    | ok raw =>
      simp only [rawEq] at checked
      cases programEq : raw.elaborate (language := language) (s.inputs.map scalar) s.outputs with
      | error e => simp [programEq] at checked
      | ok program =>
        simp only [programEq] at checked
        split at checked
        · cases checked
          simp_all
        · contradiction
  · contradiction

/-- Admission followed by erasure and re-elaboration recovers the same complete
program, so any primitive interpretation sees identical effects, stops and state. -/
theorem Imported.reelaborate {s : Snapshot} (imported : Imported s) :
    imported.program.erase.elaborate (language := language) (s.inputs.map scalar) s.outputs =
      .ok imported.program := Program.elaborate_erase _

/-- Two successful admissions of the same exported body give the same denotation
for every primitive meaning and every input, including dishonest receives. -/
theorem Snapshot.check_denotation_unique {s : Snapshot} (a b : Imported s)
    (ha : s.check = .ok a) (hb : s.check = .ok b)
    {I : PIR.Signature} (meaning : Meaning I)
    (inputs : Values (Values meaning.Value) (s.inputs.map scalar)) :
    a.denote meaning inputs = b.denote meaning inputs := by
  have exactBody : a.program.erase = b.program.erase :=
    Except.ok.inj ((Snapshot.check_exact ha).symm.trans (Snapshot.check_exact hb))
  have same := congrArg (RawProgram.elaborate (language := language)
    (s.inputs.map scalar) s.outputs) exactBody
  rw [a.reelaborate, b.reelaborate] at same
  unfold Imported.denote
  rw [Except.ok.inj same]

/-- Re-admitting the checked raw carrier recovers the very same typed body. -/
theorem Snapshot.check_elaborate {s : Snapshot} {imported : Imported s}
    (checked : s.check = .ok imported) :
    (s.raw.bind fun raw => (raw.elaborate (language := language)
      (s.inputs.map scalar) s.outputs).mapError
        (fun _ => "constructed-source-operands")) = .ok imported.program := by
  rw [Snapshot.check_exact checked]
  simp only [Except.bind, Program.elaborate_erase, Except.mapError]

/-- The pack/projection normalization is independent of native primitive meaning. -/
@[simp] theorem project_reply {I : PIR.Signature} (meaning : Meaning I)
    (types : List String) (index : Fin types.length) (reply : Values meaning.Value types) :
    meaning.interpretation.operation (.project types index) (.cons reply .nil) =
      .done (.cons (tupleAt reply index) .nil) := rfl

@[simp] theorem pack_reply {I : PIR.Signature} (meaning : Meaning I)
    (types : List String) (args : Values (Values meaning.Value) (types.map scalar)) :
    meaning.interpretation.operation (.pack types) args = .done (unpack types args) := rfl

end Zkc.Source.Constructed
