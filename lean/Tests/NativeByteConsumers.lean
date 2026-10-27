module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Module.Rat
public import ZkcExamples.Executable.SchnorrProof
public import ZkcExamples.Executable.DeferredRounds

@[expose] public section
/-! Concrete controls for real byte consumers. The StateM counter distinguishes
an effectful rejection after a query from a pure false result. -/
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace Tests.NativeByteConsumers
open Zkc.Construction Zkc.Executable
open ZkcExamples.Construction

def codec (type : PhysicalType) (_ : List UInt8) : Option (Payload ℚ ℚ) :=
  match type.sort with
  | .data (.field field) => some (.field field 0)
  | .data (.group group) => some (.group group 0)
  | _ => none

def challenge (_ : History ℚ ℚ) : StateM Nat ℚ := do
  modify (· + 1)
  pure 0

def binding : List UInt8 := List.replicate 32 0

def body : List UInt8 := frame [] ++ frame []

def bytes : List UInt8 := magic ++ binding ++ body

def schnorr (budget : Nat) (input : List UInt8 := bytes) : Bool × Nat :=
  (validate installed ZkcExamples.Executable.SchnorrProof.validator SchnorrProof.context challenge codec budget binding
    SchnorrProof.acceptancePosition (ZkcExamples.Executable.SchnorrProof.data (F := ℚ) (1 : ℚ) 0) [] input).run 0

def deferred (budget : Nat) (input : List UInt8 := bytes) : Bool × Nat :=
  (validate installed ZkcExamples.Executable.DeferredRounds.validator DeferredRounds.context challenge codec budget binding
    DeferredRounds.acceptancePosition (DeferredRounds.inputs (G := ℚ) (7 : ℚ)) [] input).run 0

/-- The exact native threshold is accepting with a valid concrete decoded proof. -/
theorem schnorr_threshold : schnorr 25 = (true, 1) := by decide +kernel

/-- Exhaustion after the query preserves that oracle action. -/
theorem schnorr_short_keeps_query : schnorr 24 = (false, 1) := by decide +kernel

theorem schnorr_bad_header : schnorr 25 [] = (false, 0) := by decide +kernel

/-- Returning true with a trailing byte is still rejected after the query. -/
theorem schnorr_unread_refuses : schnorr 25 (bytes ++ [1]) = (false, 1) := by decide +kernel

theorem deferred_threshold : deferred 35 = (true, 2) := by decide +kernel

theorem deferred_short_keeps_queries : deferred 34 = (false, 2) := by decide +kernel

/-- The second receive fails after the first challenge has already happened. -/
theorem deferred_truncated_keeps_first_query : deferred 35 (magic ++ binding ++ frame []) = (false, 1) := by
  decide +kernel

theorem deferred_unread_refuses : deferred 35 (bytes ++ [1]) = (false, 2) := by decide +kernel

/-- A wrong nominal response sort refuses after Schnorr's query. -/
def wrongResponse (type : PhysicalType) (raw : List UInt8) : Option (Payload ℚ ℚ) :=
  match type.sort with
  | .data (.field _) => some (.field "wrong.field" 0)
  | _ => codec type raw

def schnorrWrong : Bool × Nat :=
  (validate installed ZkcExamples.Executable.SchnorrProof.validator SchnorrProof.context challenge wrongResponse
    25 binding SchnorrProof.acceptancePosition (ZkcExamples.Executable.SchnorrProof.data (F := ℚ) (1 : ℚ) 0)
    [] bytes).run 0

theorem schnorr_wrong_nominal_response : schnorrWrong = (false, 1) := by decide +kernel

/-- Structural admission remains checked even for an arbitrary actual program. -/
theorem deferred_strong_admission (program : Zkc.Source.Structured.Program) :
    Zkc.Executable.DomainVM.checkNativeLowering program DeferredRounds.context installed DeferredRounds.participant
      ZkcExamples.Executable.DeferredRounds.validator = .ok (ZkcExamples.Executable.DeferredRounds.lowered, ZkcExamples.Executable.DeferredRounds.nativeFinal program) := ZkcExamples.Executable.DeferredRounds.native_checked program

/-- Finiteness does not make arbitrary coordinate-bearing origins static. -/
theorem arbitrary_origin_is_not_static :
    (Origin.withoutCoordinates ⟨"entry", ["query", "entry", "site", "port", "contract", "owner", "indices", "3"], none⟩) ≠
      ⟨"entry", ["query", "entry", "site", "port", "contract", "owner", "indices", "3"], none⟩ := by decide +kernel

end Tests.NativeByteConsumers
