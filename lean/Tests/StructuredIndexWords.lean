import Zkc.Source.Structured.RealizationTotality
import Zkc.Source.Structured.NormalForm.Presentation
import Zkc.Executable.Installed
import Mathlib.Data.ZMod.Basic

/-! Reader, meaning and installed-row controls for the total unsigned word
operations on indices: wrapping addition and subtraction, bitwise conjunction
and logical right shift, with shift counts of 64 and more. -/

set_option autoImplicit false
open Lean Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredIndexWords

private abbrev F := ZMod 97

/-! ## Total meanings on the 64-bit words -/

example : wrappingAdd (2 ^ 64 - 1) 1 = 0 := by decide
example : wrappingAdd 2 3 = 5 := by decide
example : wrappingSubtract 0 1 = 2 ^ 64 - 1 := by decide
example : wrappingSubtract 7 3 = 4 := by decide
example : bitAnd 12 10 = 8 := by decide
example : bitAnd (2 ^ 64 - 1) (2 ^ 64 + 5) = 5 := by decide
example : logicalShiftRight (2 ^ 64 - 1) 63 = 1 := by decide
example : logicalShiftRight (2 ^ 64 - 1) 0 = 2 ^ 64 - 1 := by decide
-- A shift count of 64 or more is not reduced modulo 64: the result is zero.
example : logicalShiftRight (2 ^ 64 - 1) 64 = 0 := by decide
example : logicalShiftRight (2 ^ 64 - 1) 65 = 0 := by decide
example : logicalShiftRight 1 (2 ^ 64 + 1) = 0 := by decide

example (a b : Nat) : wrappingAdd (wrappingSubtract a b) b = a % wordModulus :=
  wrappingAdd_wrappingSubtract a b
example (a b : Nat) : logicalShiftRight a (64 + b) = 0 :=
  logicalShiftRight_of_le a (Nat.le_add_right 64 b)
example (a b : Nat) : wrappingAdd a b < wordModulus ∧ wrappingSubtract a b < wordModulus ∧
    bitAnd a b < wordModulus ∧ logicalShiftRight a b < wordModulus :=
  ⟨wrappingAdd_lt a b, wrappingSubtract_lt a b, bitAnd_lt a b, logicalShiftRight_lt a b⟩

/-! ## Checked index arithmetic is distinct from the word operations

The checked primitives refuse an overflow, an underflow and an operand outside
the index range; the word operations reduce modulo `2^64` and never refuse. -/

example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] (.exec .indexAdd)
    (.cons (2 ^ 64 - 1) (.cons 1 .nil)) .nil = .halt .refused := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] .indexWrappingAdd
    (.cons (2 ^ 64 - 1) (.cons 1 .nil)) .nil = .done (.cons 0 .nil) := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] (.exec .indexSub)
    (.cons 0 (.cons 1 .nil)) .nil = .halt .refused := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] .indexWrappingSubtract
    (.cons 0 (.cons 1 .nil)) .nil = .done (.cons (2 ^ 64 - 1) .nil) := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] (.exec .indexAdd)
    (.cons (2 ^ 64) (.cons 0 .nil)) .nil = .halt .refused := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] .indexWrappingAdd
    (.cons (2 ^ 64) (.cons 0 .nil)) .nil = .done (.cons 0 .nil) := rfl

/-! ## One meaning in every evaluator -/

example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] .indexWrappingAdd
    (.cons (2 ^ 64 - 1) (.cons 2 .nil)) .nil = .done (.cons 1 .nil) := rfl
example : Evaluation.operationOn (ringModel F F) SiteObservations.closed [] .indexWrappingSubtract
    (.cons 1 (.cons 2 .nil)) .nil = .done (.cons (2 ^ 64 - 1) .nil) := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] .indexBitAnd
    (.cons 6 (.cons 3 .nil)) .nil = .done (.cons 2 .nil) := rfl
example : Evaluation.operationOn (ringModel F F) SiteObservations.closed [] .indexLogicalShiftRight
    (.cons 256 (.cons 64 .nil)) .nil = .done (.cons 0 .nil) := rfl
example (model : DomainModel) (a b : Nat) :
    Op.evalTotal model .indexLogicalShiftRight rfl (Values.cons a (.cons b .nil)) =
      Values.cons (logicalShiftRight a b) .nil := rfl

/-! ## Installed executable rows -/

private def binding (contract : String) : Zkc.Executable.Binding :=
  ⟨"word", contract, [], "native/" ++ contract, []⟩

example : Zkc.Executable.installed.resolve (binding "index.wrapping_add") [] =
    some (.calculate .indexWrappingAdd) := by decide +kernel
example : Zkc.Executable.installed.resolve (binding "index.wrapping_sub") [] =
    some (.calculate .indexWrappingSubtract) := by decide +kernel
example : Zkc.Executable.installed.resolve (binding "index.bit_and") [] =
    some (.calculate .indexBitAnd) := by decide +kernel
example : Zkc.Executable.installed.resolve (binding "index.logical_shift_right") [] =
    some (.calculate .indexLogicalShiftRight) := by decide +kernel
-- An operation row takes no parameter.
example : Zkc.Executable.installed.resolve (binding "index.bit_and") [.text "0"] = none := by
  decide +kernel

/-! ## Reader and admission -/

private def root : Definition := .function ⟨"main", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], some (.protocol ⟨"main", []⟩), .block [] (.ret [])⟩

private def snapshot (definitions : List Definition) (bindings : List Binding := []) : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], bindings, definitions,
    definitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩

private def mathHelper (name : String) (op : Descriptor) (inputs outputs : List Ty)
    (site : String := "") : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none,
    .block [.instruction op (List.range inputs.length) outputs [] site]
      (.ret (List.range outputs.length))⟩

private def refusedWith {α : Type} (result : Except String α) (expected : String) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false

private def words : List (String × Descriptor × (Nat → Nat → Nat)) := [
  ("index.wrapping_add", .indexWrappingAdd, wrappingAdd),
  ("index.wrapping_sub", .indexWrappingSubtract, wrappingSubtract),
  ("index.bit_and", .indexBitAnd, bitAnd),
  ("index.logical_shift_right", .indexLogicalShiftRight, logicalShiftRight)]

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  for (tag, descriptor, meaning) in words do
    test s!"{tag} decodes" ((Format.descriptor (.arr #[.str tag])).toOption == some descriptor)
    test s!"{tag} extra slot" (refusedWith (Format.descriptor (.arr #[.str tag, .str "extra"]))
      "structured-operation-unsupported")
    let helper := mathHelper "word" descriptor [.index, .index] [.index]
    let source := snapshot [root, helper]
    let .ok program := check source | throw (IO.userError s!"{tag}: Math helper did not admit")
    let table : Meanings F F :=
      program.payload.definitions.foldl (Evaluation.extendMeanings SiteObservations.closed) []
    let domainTable : MeaningsOn (ringModel F F).toCarriers :=
      program.payload.definitions.foldl (Evaluation.extendMeaningsOn (ringModel F F) SiteObservations.closed) []
    let signature : Helper := ⟨"word", .math, [.index, .index], [.index]⟩
    for (a, b) in [(0, 0), (2 ^ 64 - 1, 1), (5, 2 ^ 64 - 1), (2 ^ 64 - 1, 63), (2 ^ 64 - 1, 64),
        (12345, 65), (7, 2 ^ 64 - 1)] do
      let args : Values (assignment F F) [.index, .index] := .cons a (.cons b .nil)
      let value := fun (result : PIR.Process closedInterface (Values (assignment F F) [.index])) =>
        match result with | .done (.cons value .nil) => some value | _ => none
      test s!"{tag} {a} {b}" (value (invoke table signature args) == some (meaning a b))
      test s!"domain {tag} {a} {b}" (value (invoke domainTable signature args) == some (meaning a b))
    test s!"{tag} wrong input types" (refusedWith (check (snapshot [root,
      mathHelper "word" descriptor [.boolean, .index] [.index]])) "structured-formation")
    test s!"{tag} wrong output type" (refusedWith (check (snapshot [root,
      mathHelper "word" descriptor [.index, .index] [.boolean]])) "structured-formation")
    test s!"{tag} Math site" (refusedWith (check (snapshot [root,
      mathHelper "word" descriptor [.index, .index] [.index] "site"])) "structured-math-site")
    let .function f := helper | throw (IO.userError "expected function")
    test s!"{tag} Local spelling" (refusedWith (check (snapshot [root,
      .function { f with kind := .local, origin := some (.local "word" []) }])) "structured-local-operation")
    -- The word operations are not Local primitives: no binding installs them.
    test s!"{tag} Local binding" (refusedWith (check (snapshot [root] [⟨"word", tag, [], "", none⟩]))
      "structured-binding")
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"index word failures: {errors.reverse}")
  IO.println s!"structured-index-words: {← count.get} controls passed"

#eval run

end Tests.StructuredIndexWords
