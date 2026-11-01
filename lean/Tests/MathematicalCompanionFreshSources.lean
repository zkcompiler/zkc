import ZkcExamples.Structured.GkrGateGoals
import Tests.ConnectionHelperCertificate
import ZkcTools.StructuredSource.HelperPresentation
import ZkcTools.StructuredSource.NamedValues

/-! Authored retained typed-source fixtures, derived from existing actual
helper Regions. These are not fresh native exports or compiled endpoints.
All wrapper/layout/guard AST authoring below counts as fixture cost. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace Tests.MathematicalCompanionFreshSources
open Zkc.Source Zkc.Source.Structured

abbrev field : Ty := .field scalarDomain

/-- Reorder the four same-typed inputs, add a bind wrapper, and return two
original operands as well as the gate value. This changes more than a count. -/
def wrappedGate : Region dialect [field, field, field, field] [field, field, field] :=
  .bind (ZkcExamples.Structured.GkrGateGoals.Value.body.rename (by
    intro ty position
    cases position with
    | here => exact .there (.there .here)
    | there position => cases position with
      | here => exact .there .here
      | there position => cases position with
        | here => exact .there (.there (.there .here))
        | there position => cases position with
          | here => exact .here
          | there position => cases position))
    (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))))

helper_presentation WrappedGate inputs [right, mulWeight, addWeight, left]
  outputs [value, retainedRight, retainedLeft] := wrappedGate

named_values WrappedInputs [right, mulWeight, addWeight, left] :=
  ([field, field, field, field] : List Ty)

abbrev readInputs : List Ty := [.boolean, .vector scalarDomain, .index, field]
abbrev readOutputs : List Ty := [field, .vector scalarDomain, .index]

/-- Reuse the retained bounded-read Region; preserve the original vector and
index alongside the arithmetic result. The guard precedes every read. -/
def readThenSubtract : Region dialect readInputs readOutputs :=
  .bind (Tests.ConnectionHelperCertificate.readLeafBody.rename (by
    intro ty position
    cases position with
    | here => exact .there .here
    | there position => cases position with
      | here => exact .there (.there .here)
      | there position => cases position))
    (.letOp (.fieldSubtract scalarDomain)
      (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil
      (.ret (.cons .here (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) .nil)))))

def guardedRead : Region dialect readInputs readOutputs :=
  .letOp (.branch [] []) (.cons .here .nil)
    (.cons (.ret .nil) (.cons (.stop .reject) .nil)) readThenSubtract

helper_presentation GuardedRead inputs [enabled, values, index, expected]
  outputs [residual, retainedValues, retainedIndex] := guardedRead

helper_presentation UnguardedRead inputs [enabled, values, index, expected]
  outputs [residual, retainedValues, retainedIndex] := readThenSubtract

named_values ReadInputs [enabled, values, index, expected] := readInputs

end Tests.MathematicalCompanionFreshSources
