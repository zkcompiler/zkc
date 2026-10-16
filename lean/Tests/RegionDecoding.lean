import Zkc.Source.RegionDecoding

/-! Formation controls for the independent canonical Lean region carrier.
Successes reuse both universal roundtrip directions; failures compute the
exact diagnostic constructor, without an operation meaning or native execution.
-/

namespace RegionDecodingTests
open Zkc.Source

inductive Ty where
  | scalar
  | flag
  deriving DecidableEq, Repr

inductive Op where
  | split
  | discard
  | tick
  | callback
  | choose
  | emptyCallback

abbrev dialect : Dialect where
  Ty := Ty
  Op := Op
  arguments
    | .split | .discard | .callback => [.scalar]
    | .choose => [.flag, .scalar]
    | .tick | .emptyCallback => []
  results
    | .split | .callback | .choose => [.scalar, .flag]
    | .discard | .tick | .emptyCallback => []
  regions
    | .callback => [([.scalar], [.scalar, .flag])]
    | .choose => [([.scalar], [.scalar, .flag]), ([.scalar], [.scalar, .flag])]
    | .emptyCallback => [([], [])]
    | .split | .discard | .tick => []

abbrev Raw := RawRegion Ty Op
abbrev Bodies := RawRegions Ty Op

def decode (inputs outputs : List Ty) (raw : Raw) :=
  raw.elaborate (dialect := dialect) inputs outputs

def decodeBodies (signatures : List (List Ty × List Ty)) (raw : Bodies) :=
  raw.elaborate (dialect := dialect) signatures

def pair : Region dialect [.scalar] [.scalar, .flag] :=
  .letOp .split (.cons .here .nil) .nil
    (.ret (.cons .here (.cons (.there .here) .nil)))

def rawPair : Raw := .letOp .split [0] [.scalar, .flag] .nil (.ret [0, 1])

example : pair.erase = rawPair := rfl
example : decode [.scalar] [.scalar, .flag] rawPair = .ok pair :=
  Region.elaborate_erase pair

/-- An empty result prefix retains the original caller context. -/
def discard : Region dialect [.scalar] [.scalar] :=
  .letOp .discard (.cons .here .nil) .nil (.ret (.cons .here .nil))

example : discard.erase = .letOp .discard [0] [] .nil (.ret [0]) := rfl
example : decode [.scalar] [.scalar] discard.erase = .ok discard :=
  Region.elaborate_erase discard

def tick : Region dialect [] [] := .letOp .tick .nil .nil (.ret .nil)

example : tick.erase = .letOp .tick [] [] .nil (.ret []) := rfl
example : decode [] [] tick.erase = .ok tick := Region.elaborate_erase tick

/-- Bind puts its two results in order before the retained input. -/
def boundPair : Region dialect [.scalar] [.flag, .scalar, .scalar] :=
  .bind pair (.ret (.cons (.there .here)
    (.cons .here (.cons (.there (.there .here)) .nil))))

example : boundPair.erase = .bind [.scalar, .flag] rawPair (.ret [1, 0, 2]) := rfl
example : decode [.scalar] [.flag, .scalar, .scalar] boundPair.erase = .ok boundPair :=
  Region.elaborate_erase boundPair

def emptyBind : Region dialect [.scalar] [.scalar] :=
  .bind (.letOp .discard (.cons .here .nil) .nil (.ret .nil))
    (.ret (.cons .here .nil))

example : emptyBind.erase =
    .bind [] (.letOp .discard [0] [] .nil (.ret [])) (.ret [0]) := rfl
example : decode [.scalar] [.scalar] emptyBind.erase = .ok emptyBind :=
  Region.elaborate_erase emptyBind

def withCallback (body : Region dialect [.scalar] [.scalar, .flag]) :
    Region dialect [.scalar] [.scalar, .flag] :=
  .letOp .callback (.cons .here .nil) (.cons body .nil)
    (.ret (.cons .here (.cons (.there .here) .nil)))

/-- Two nested callback edges lead to the split operation. -/
def nested : Region dialect [.scalar] [.scalar, .flag] := withCallback (withCallback pair)

def rawNested : Raw :=
  .letOp .callback [0] [.scalar, .flag]
    (.cons [.scalar] [.scalar, .flag]
      (.letOp .callback [0] [.scalar, .flag]
        (.cons [.scalar] [.scalar, .flag] rawPair .nil) (.ret [0, 1])) .nil)
    (.ret [0, 1])

example : nested.erase = rawNested := rfl
example : decode [.scalar] [.scalar, .flag] nested.erase = .ok nested :=
  Region.elaborate_erase nested

/-- Raw acceptance preserves all metadata at both nested multiresult callbacks. -/
theorem nested_acceptance_preserves_raw {typed : Region dialect [.scalar] [.scalar, .flag]}
    (accepted : decode [.scalar] [.scalar, .flag] rawNested = .ok typed) :
    typed.erase = rawNested :=
  RawRegion.erase_of_elaborate (dialect := dialect) rawNested accepted

-- Compute acceptance from the explicit raw payload, then consume the converse.
example : decode [.scalar] [.scalar, .flag] rawNested = .ok nested := rfl
example : nested.erase = rawNested := nested_acceptance_preserves_raw (by rfl)

def callbacks : Regions dialect
    [([.scalar], [.scalar, .flag]), ([.scalar], [.scalar, .flag])] :=
  .cons pair (.cons nested .nil)

def rawCallbacks : Bodies :=
  .cons [.scalar] [.scalar, .flag] rawPair
    (.cons [.scalar] [.scalar, .flag] rawNested .nil)

example : decodeBodies
    [([.scalar], [.scalar, .flag]), ([.scalar], [.scalar, .flag])] callbacks.erase = .ok callbacks :=
  Regions.elaborate_erase callbacks

/-- Callback-list acceptance preserves declared signatures and the nested raw tree. -/
theorem callbacks_acceptance_preserves_raw
    {typed : Regions dialect [([.scalar], [.scalar, .flag]), ([.scalar], [.scalar, .flag])]}
    (accepted : decodeBodies
      [([.scalar], [.scalar, .flag]), ([.scalar], [.scalar, .flag])] rawCallbacks = .ok typed) :
    typed.erase = rawCallbacks :=
  RawRegions.erase_of_elaborate (dialect := dialect) rawCallbacks accepted

example : decodeBodies
    [([.scalar], [.scalar, .flag]), ([.scalar], [.scalar, .flag])] rawCallbacks = .ok callbacks := rfl
example : callbacks.erase = rawCallbacks := callbacks_acceptance_preserves_raw (by rfl)

def choose : Region dialect [.flag, .scalar] [.scalar, .flag] :=
  .letOp .choose (.cons .here (.cons (.there .here) .nil)) callbacks
    (.ret (.cons .here (.cons (.there .here) .nil)))

example : decode [.flag, .scalar] [.scalar, .flag] choose.erase = .ok choose :=
  Region.elaborate_erase choose

def emptyCallback : Region dialect [] [] :=
  .letOp .emptyCallback .nil (.cons (.ret .nil) .nil) (.ret .nil)

example : decode [] [] emptyCallback.erase = .ok emptyCallback :=
  Region.elaborate_erase emptyCallback

/-- A stopped region retains its reason without producing the expected results. -/
def stopped : Region dialect [] [.scalar, .flag] := .stop .reject

example : stopped.erase = .stop .reject := rfl
example : decode [] [.scalar, .flag] stopped.erase = .ok stopped :=
  Region.elaborate_erase stopped

-- Return arity and ordered types, including missing and extra results.
example : decode [.scalar] [.scalar, .flag] (.ret [0]) =
    .error (.operand (.operandCount 1 0)) := rfl
example : decode [.scalar] [] (.ret [0]) =
    .error (.operand (.operandCount 0 1)) := rfl
example : decode [.scalar, .flag] [.scalar, .flag] (.ret [1, 0]) =
    .error (.operand (.invalidOperand 1 .scalar)) := rfl
example : decode [] [.scalar] (.ret [0]) =
    .error (.operand (.invalidOperand 0 .scalar)) := rfl

-- Operation operands require the exact count, types and in-scope positions.
example : decode [.scalar] [] (.letOp .split [] [.scalar, .flag] .nil (.ret [])) =
    .error (.operand (.operandCount 1 0)) := rfl
example : decode [.scalar] [] (.letOp .split [0, 0] [.scalar, .flag] .nil (.ret [])) =
    .error (.operand (.operandCount 0 1)) := rfl
example : decode [.flag] [] (.letOp .split [0] [.scalar, .flag] .nil (.ret [])) =
    .error (.operand (.invalidOperand 0 .scalar)) := rfl
example : decode [.scalar] [] (.letOp .split [1] [.scalar, .flag] .nil (.ret [])) =
    .error (.operand (.invalidOperand 1 .scalar)) := rfl

-- The declared operation result list must agree in arity, order and types.
example : decode [.scalar] [] (.letOp .split [0] [.flag, .scalar] .nil (.ret [])) =
    .error (.resultTypes [.scalar, .flag] [.flag, .scalar]) := rfl
example : decode [.scalar] [] (.letOp .split [0] [.scalar, .scalar] .nil (.ret [])) =
    .error (.resultTypes [.scalar, .flag] [.scalar, .scalar]) := rfl
example : decode [.scalar] [] (.letOp .split [0] [.scalar] .nil (.ret [])) =
    .error (.resultTypes [.scalar, .flag] [.scalar]) := rfl
example : decode [.scalar] [] (.letOp .split [0] [.scalar, .flag, .scalar] .nil (.ret [])) =
    .error (.resultTypes [.scalar, .flag] [.scalar, .flag, .scalar]) := rfl
example : decode [] [] (.letOp .tick [] [.scalar] .nil (.ret [])) =
    .error (.resultTypes [] [.scalar]) := rfl

-- A caller value at index one cannot be captured by a one-input callback.
example : decode [.scalar, .flag] []
    (.letOp .callback [0] [.scalar, .flag]
      (.cons [.scalar] [.scalar, .flag] (.ret [0, 1]) .nil) (.ret [])) =
    .error (.operand (.invalidOperand 1 .flag)) := rfl

-- Empty callbacks are closed even when the caller has a suitable value.
example : decode [.scalar] []
    (.letOp .emptyCallback [] []
      (.cons [] [] (.letOp .discard [0] [] .nil (.ret [])) .nil) (.ret [])) =
    .error (.operand (.invalidOperand 0 .scalar)) := rfl

-- Missing and extra callbacks, both at the head and after a valid callback.
example : decode [.scalar] [] (.letOp .callback [0] [.scalar, .flag] .nil (.ret [])) =
    .error (.regionCount 1 0) := rfl
example : decode [] []
    (.letOp .tick [] [] (.cons [] [] (.ret []) .nil) (.ret [])) =
    .error (.regionCount 0 1) := rfl
example : decode [.scalar] []
    (.letOp .callback [0] [.scalar, .flag]
      (.cons [.scalar] [.scalar, .flag] rawPair
        (.cons [.scalar] [.scalar, .flag] rawPair .nil)) (.ret [])) =
    .error (.regionCount 0 1) := rfl
example : decode [.flag, .scalar] []
    (.letOp .choose [0, 1] [.scalar, .flag]
      (.cons [.scalar] [.scalar, .flag] rawPair .nil) (.ret [])) =
    .error (.regionCount 1 0) := rfl

-- Callback annotations are checked before their bodies, even for stopped bodies.
example : decodeBodies [([.scalar], [.scalar, .flag])]
    (.cons [.flag] [.scalar, .flag] (.stop .reject) .nil) =
    .error (.regionInputs [.scalar] [.flag]) := rfl
example : decodeBodies [([.scalar], [.scalar, .flag])]
    (.cons [.scalar, .flag] [.scalar, .flag] (.stop .reject) .nil) =
    .error (.regionInputs [.scalar] [.scalar, .flag]) := rfl
example : decodeBodies [([.scalar], [.scalar, .flag])]
    (.cons [.scalar] [.flag, .scalar] (.stop .reject) .nil) =
    .error (.regionOutputs [.scalar, .flag] [.flag, .scalar]) := rfl
example : decodeBodies [([.scalar], [.scalar, .flag])]
    (.cons [.scalar] [.scalar] (.stop .reject) .nil) =
    .error (.regionOutputs [.scalar, .flag] [.scalar]) := rfl

-- A correct annotation does not admit an ill-typed or malformed body.
example : decodeBodies [([.scalar, .flag], [.scalar, .flag])]
    (.cons [.scalar, .flag] [.scalar, .flag] (.ret [1, 0]) .nil) =
    .error (.operand (.invalidOperand 1 .scalar)) := rfl
example : decode [.flag, .scalar] []
    (.letOp .choose [0, 1] [.scalar, .flag]
      (.cons [.scalar] [.scalar, .flag] rawPair
        (.cons [.scalar] [.scalar, .flag] (.ret [0]) .nil)) (.ret [])) =
    .error (.operand (.operandCount 1 0)) := rfl

-- Every nested level is checked, including a capture two callbacks deep.
example : decode [.scalar, .flag] []
    (.letOp .callback [0] [.scalar, .flag]
      (.cons [.scalar] [.scalar, .flag]
        (.letOp .callback [0] [.scalar, .flag]
          (.cons [.scalar] [.scalar, .flag] (.ret [0, 1]) .nil) (.ret [0, 1])) .nil)
      (.ret [])) = .error (.operand (.invalidOperand 1 .flag)) := rfl

-- Suffix scope and ordered operation results are checked independently.
example : decode [.scalar] [.flag, .scalar]
    (.letOp .split [0] [.scalar, .flag] .nil (.ret [0, 1])) =
    .error (.operand (.invalidOperand 0 .flag)) := rfl
example : decode [.scalar] [.scalar]
    (.letOp .split [0] [.scalar, .flag] .nil (.ret [3])) =
    .error (.operand (.invalidOperand 3 .scalar)) := rfl
example : decode [] [.scalar] (.letOp .tick [] [] .nil (.ret [0])) =
    .error (.operand (.invalidOperand 0 .scalar)) := rfl

-- Bind checks both the intermediate result list and the resulting suffix context.
example : decode [] [] (.bind [.scalar] (.ret [0]) (.ret [])) =
    .error (.operand (.invalidOperand 0 .scalar)) := rfl
example : decode [.scalar] [] (.bind [.flag, .scalar] rawPair (.ret [])) =
    .error (.operand (.invalidOperand 0 .flag)) := rfl
example : decode [.scalar] [] (.bind [.scalar] rawPair (.ret [])) =
    .error (.operand (.operandCount 0 1)) := rfl
example : decode [.scalar] [.scalar] (.bind [.scalar, .flag] rawPair (.ret [1])) =
    .error (.operand (.invalidOperand 1 .scalar)) := rfl
example : decode [.scalar] [.scalar] (.bind [.scalar, .flag] rawPair (.ret [3])) =
    .error (.operand (.invalidOperand 3 .scalar)) := rfl
example : decode [] [.scalar] (.bind [] (.ret []) (.ret [0])) =
    .error (.operand (.invalidOperand 0 .scalar)) := rfl

-- Formation never skips a suffix merely because its preceding body stops.
example : decode [] [.scalar] (.bind [.scalar] (.stop .reject) (.ret [1])) =
    .error (.operand (.invalidOperand 1 .scalar)) := rfl

/-- Universal theorem reuse with abstract dialects, contexts and arbitrary trees. -/
example {d : Dialect} [DecidableEq d.Ty] {inputs outputs}
    (region : Region d inputs outputs) :
    region.erase.elaborate inputs outputs = .ok region := Region.elaborate_erase region

example {d : Dialect} [DecidableEq d.Ty] {signatures} (bodies : Regions d signatures) :
    bodies.erase.elaborate signatures = .ok bodies := Regions.elaborate_erase bodies

/-- Acceptance of arbitrary raw trees cannot discard payload or annotations. -/
example {d : Dialect} [DecidableEq d.Ty] {inputs outputs}
    (raw : RawRegion d.Ty d.Op) {typed : Region d inputs outputs}
    (accepted : raw.elaborate inputs outputs = .ok typed) : typed.erase = raw :=
  RawRegion.erase_of_elaborate raw accepted

example {d : Dialect} [DecidableEq d.Ty] {signatures}
    (raw : RawRegions d.Ty d.Op) {typed : Regions d signatures}
    (accepted : raw.elaborate signatures = .ok typed) : typed.erase = raw :=
  RawRegions.erase_of_elaborate raw accepted

end RegionDecodingTests
