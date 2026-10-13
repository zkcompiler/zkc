import ZkcClean.NativeExport
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Examples.FibonacciWithChannels
import Clean.Table.WitnessGeneration
import Mathlib.Tactic.NormNum.Prime

/-! Reproducible Clean clients for the native adapter.

FemtoCairo uses upstream transition constraints, witness generation and reference
execution. Fibonacci and the auxiliary-column control are locally authored Clean
constraints. Lookup interpretations and public bindings are explicit client inputs.
-/

namespace TestsClean.NativeClients

open Lean
open ZkcClean.NativeExport
open Examples.FemtoCairo
open Examples.FemtoCairo.Types

def koalaBear := 2130706433
set_option maxRecDepth 100000 in
instance : Fact koalaBear.Prime := ⟨by norm_num [koalaBear]⟩
instance : Fact (koalaBear > 512) := ⟨by decide⟩
abbrev K := F koalaBear

namespace Fibonacci
structure State (F : Type) where
  x : F
  y : F
instance : ProvableType State where
  size := 2
  toElements state := #v[state.x, state.y]
  fromElements values := ⟨values[0], values[1]⟩

def step : TwoRowsConstraint State K := do
  let current ← TableConstraint.getCurrRow
  let nextX ← copyToVar current.y
  assignVar (.next 0) nextX
  assign (.next 1) (current.x + current.y)

def source : Json := table ``step 8 [TableOperation.everyRowExceptLast step]
def initial : State K := ⟨0, 1⟩
def trace := witnesses step initial 8
def reference : Nat → K × K
  | 0 => (initial.x, initial.y)
  | n + 1 => let (x, y) := reference n; (y, x + y)

-- Two independently allocated one-row auxiliaries must not share a column.
def auxiliary (value : K) : SingleRowConstraint State K := do
  let current ← TableConstraint.getCurrRow
  let _ ← copyToVar (current.x + Expression.const value)
  pure ()
def scopes := table ``auxiliary 2 [.everyRow (auxiliary 1), .boundary (.fromEnd 0) (auxiliary 2)]

end Fibonacci

namespace Machine
-- The pinned Plonky3MemoryTestData program, instantiated directly in KoalaBear.
-- Its upstream BabyBear field instance uses native_decide; this client keeps
-- its own kernel-checked prime and program-validity proofs.
def data : Vector K 32 :=
  #v[212, 1, 2, 8, 213, 3, 4, 14, 244, 1, 10, 15, 233, 5, 2, 30,
     220, 100, 3, 107, 212, 4, 5, 12, 252, 0, 0, 0, 0, 0, 0, 0]
def program : Fin 32 → K := fun i => data[i]
theorem programSize : 32 < koalaBear := by decide
theorem validProgram :
    Spec.ValidProgramSize koalaBear 32 ∧ Spec.ValidProgram program := by
  constructor
  · show 32 + 3 < koalaBear; decide
  · intro i; fin_cases i <;> decide +kernel

def machine := femtoCairoTable program programSize validProgram 7
def initial : State K := ⟨0, 0, 0⟩
def final : State K := ⟨28, 0, 0⟩
def memoryValues : Array K := #[0, 5, 3, 7, 2, 10, 0, 0]
def memoryData : ProverData K := fun name width =>
  if name == "memory" then
    if h : width = 2 then
      h ▸ memoryValues.mapIdx (fun i value => (#v[(i : K), value] : Vector K 2))
    else #[]
  else #[]
def trace := witnessesWithData machine.inductiveConstraint (initial, ()) 8 memoryData
def reference := Spec.femtoCairoMachineBoundedExecution program
  (fun i : Fin memoryValues.size => memoryValues[i]) initial 7

def lookups : Json := Json.arr #[
  lookup ``Table.staticOfFn (Table.staticOfFn programSize "program" program).toRaw
    (.fixedIndexed (Array.ofFn program)),
  lookup ``MemoryTable (MemoryTable (p := koalaBear)).toRaw
    (.witnessIndexed memoryValues.size)]
end Machine

def inputs (publicValues trace witnessTables : Json) : Json :=
  Json.mkObj [("format", "zkc.clean-inputs/0"), ("public", publicValues),
    ("trace", trace), ("witness_tables", witnessTables)]

def noPublic : Json := Json.mkObj [("origin", "TestsClean.NativeClients.noPublic"),
  ("size", toJson (0 : Nat)), ("bindings", Json.arr #[])]

def write (output : System.FilePath) (name : String) (source inputs : Json)
    (reference : Option Json := none) : IO Unit := do
  let path := output / name
  IO.FS.createDirAll path
  IO.FS.writeFile (path / "source.json") (source.pretty ++ "\n")
  IO.FS.writeFile (path / "inputs.json") (inputs.pretty ++ "\n")
  if let some reference := reference then
    IO.FS.writeFile (path / "reference.json") (reference.pretty ++ "\n")

def run (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: CleanExamples OUTPUT_DIRECTORY")
  let path := System.FilePath.mk output
  -- Check non-endpoint relative rows through the actual extraction path.
  for (row, expected) in [(RowIndex.fromStart 1, (1 : Int)), (.fromEnd 1, -2)] do
    let encoded := operation 0 (TableOperation.boundary row (Fibonacci.auxiliary 0))
    if encoded.getObjValAs? Int "row" != .ok expected then
      throw (IO.userError "unexpected extracted boundary row")
  let empty := Json.arr #[]
  let source := source (ZkcClean.PrimePresentation.ofPrime "koala-bear" koalaBear)
  let (finalX, finalY) := Fibonacci.reference 7
  write path "fibonacci"
    (source Fibonacci.source (stateBoundary ``Fibonacci.State Fibonacci.State) empty empty)
    (inputs (toJson ((toElements Fibonacci.initial).toArray ++ #[finalX, finalY])) (toJson Fibonacci.trace) (Json.mkObj []))
    (some (toJson (#[ (Fibonacci.reference 7).1, (Fibonacci.reference 7).2 ] : Array K)))
  write path "table-scopes" (source Fibonacci.scopes noPublic empty empty)
    (inputs empty (toJson (#[#[0, 1, 1, 0], #[2, 3, 3, 4]] : Array (Array K))) (Json.mkObj []))
  let some result := Machine.reference | throw (IO.userError "Clean VM reference refused the program")
  let (table, publicLayout) := inductiveTable ``Machine.machine 8 Machine.machine
  write path "femtocairo" (source table publicLayout Machine.lookups empty)
    (inputs (toJson (toElements Machine.initial ++ toElements Machine.final).toArray) (toJson Machine.trace)
      (Json.mkObj [("memory", toJson Machine.memoryValues)]))
    (some (toJson (#[result.pc, result.ap, result.fp] : Array K)))
  let weights : Array K := (Array.range 256).map fun i => if i = 42 then 3 else 0
  write path "flat-channel"
    (source (component ``pushBytes 2 ⟨pushBytes (p := koalaBear)⟩) noPublic empty
      (Json.arr #[channel ``BytesChannel (BytesChannel (p := koalaBear)).toRaw]))
    (inputs empty (toJson #[weights, weights.map (- ·)]) (Json.mkObj []))

end TestsClean.NativeClients
