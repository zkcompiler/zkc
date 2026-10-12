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

def source : Json := table 8 [TableOperation.everyRowExceptLast step]
def trace := witnesses step (⟨0, 1⟩ : State K) 8
def reference : Nat → K × K
  | 0 => (0, 1)
  | n + 1 => let (x, y) := reference n; (y, x + y)

-- Two independently allocated one-row auxiliaries must not share a column.
def auxiliary (value : K) : SingleRowConstraint State K := do
  let current ← TableConstraint.getCurrRow
  let _ ← copyToVar (current.x + Expression.const value)
  pure ()
def scopes := table 2 [.everyRow (auxiliary 1), .boundary (.fromEnd 0) (auxiliary 2)]

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
  Json.mkObj [("name", "program"), ("interpretation", "fixed-indexed"),
    ("values", toJson ((List.finRange 32).map program))],
  Json.mkObj [("name", "memory"), ("interpretation", "witness-indexed"),
    ("height", toJson memoryValues.size)]]
end Machine

def document (source bindings publicData lookups trace witnessTables reference : Json) : Json :=
  Json.mkObj [("format", "zkc.clean-export/0"),
    ("field", toJson koalaBear), ("table", source),
    ("public_bindings", bindings), ("public", publicData),
    ("lookups", lookups), ("trace", trace),
    ("witness_tables", witnessTables), ("reference", reference)]

def run (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: CleanExamples OUTPUT_DIRECTORY")
  IO.FS.createDirAll output
  let fib := document Fibonacci.source (stateBindings 2)
    (toJson (#[0, 1, 13, 21] : Array K)) (Json.arr #[])
    (toJson Fibonacci.trace) (Json.mkObj [])
    (toJson (#[ (Fibonacci.reference 7).1, (Fibonacci.reference 7).2 ] : Array K))
  IO.FS.writeFile (System.FilePath.mk output / "fibonacci.json") (fib.pretty ++ "\n")
  let scopes := document Fibonacci.scopes (Json.arr #[]) (Json.arr #[]) (Json.arr #[])
    (toJson (#[#[0, 1, 1, 0], #[2, 3, 3, 4]] : Array (Array K))) (Json.mkObj []) (Json.arr #[])
  IO.FS.writeFile (System.FilePath.mk output / "table-scopes.json") (scopes.pretty ++ "\n")
  let some result := Machine.reference | throw (IO.userError "Clean VM reference refused the program")
  let reference := toJson (#[result.pc, result.ap, result.fp] : Array K)
  let vm := document
    (table 8 [TableOperation.everyRowExceptLast Machine.machine.inductiveConstraint])
    (stateBindings 3) (toJson (#[0, 0, 0, 28, 0, 0] : Array K)) Machine.lookups
    (toJson Machine.trace) (Json.mkObj [("memory", toJson Machine.memoryValues)]) reference
  IO.FS.writeFile (System.FilePath.mk output / "femtocairo.json") (vm.pretty ++ "\n")
  let weights : Array K := (Array.range 256).map fun i => if i = 42 then 3 else 0
  let flat := Json.mkObj [
    ("format", "zkc.clean-export/0"), ("field", toJson koalaBear),
    ("table", component 2 ⟨pushBytes (p := koalaBear)⟩),
    ("public_bindings", Json.arr #[]), ("public", Json.arr #[]),
    ("lookups", Json.arr #[]), ("witness_tables", Json.mkObj []),
    ("channels", Json.arr #[Json.mkObj [("name", "bytes"), ("arity", toJson (1 : Nat))]]),
    ("trace", toJson #[weights, weights.map (- ·)])]
  IO.FS.writeFile (System.FilePath.mk output / "flat-channel.json") (flat.pretty ++ "\n")

end TestsClean.NativeClients
