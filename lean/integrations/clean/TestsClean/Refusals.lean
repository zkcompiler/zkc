import ZkcClean.Specification
import TestsClean.KoalaBear
import Clean.Gadgets.Addition8.Addition8
import Clean.Examples.FibonacciWithChannels

/-! Refusal controls. The export restriction is checked on the flattened
operations, so a lookup inside a nested subcircuit is refused even though the
circuit's own operation list has no shallow lookup. Import admission refuses
artifacts that are not canonical for the declared field and width.
-/

set_option autoImplicit false

namespace TestsClean.Refusals

open ZkcClean Zkc.Relation

/-- Upstream `Addition8Full`: its only lookup is inside the nested
`Addition8FullCarry` subcircuit. -/
def nestedLookup : Air.Flat.Component KoalaBear :=
  ⟨(Gadgets.Addition8Full.circuit (p := koalaBear)).isGeneralFormalCircuit⟩

theorem nestedLookup_shallow :
    ((Gadgets.Addition8Full.circuit (p := koalaBear)).main default |>.operations 0).shallowLookups
      = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

theorem nestedLookup_flattened :
    (FlatOperation.lookups (flatten nestedLookup.operations)).length = 1 := by
  decide +kernel

theorem nestedLookup_refused : exportComponent nestedLookup = .error .lookup := by
  decide +kernel

/-- Upstream `add8` from `Clean.Examples.FibonacciWithChannels`: channel pull
and emit interactions. -/
def channel : Air.Flat.Component KoalaBear := ⟨add8 (p := koalaBear)⟩

theorem channel_interactions :
    (FlatOperation.interactions (flatten channel.operations)).length = 2 := by
  decide +kernel

theorem channel_refused : exportComponent channel = .error .interaction := by
  decide +kernel

/-- Clean reads an out-of-range variable as zero ... -/
theorem outOfRange_reads_zero :
    Expression.eval (Environment.fromArray #[(5 : KoalaBear)] noData) (var ⟨1⟩) = 0 := by
  decide +kernel

/-- ... so the exporter refuses it rather than inventing a finite read. -/
theorem outOfRange_refused :
    exportOperations (F := KoalaBear) 1 [.assert (var ⟨1⟩)] = .error (.variableOutOfRange 1) := by
  decide +kernel

theorem inRange_accepted :
    exportOperations (F := KoalaBear) 2 [.assert (var ⟨1⟩)] =
      .ok { fieldSize := koalaBear, width := 2, assertions := [.column 1] } := by
  decide +kernel

/-- Import admission refuses a noncanonical constant, an out-of-range column
and a field-size mismatch. -/
theorem decode_refusals :
    (({ fieldSize := koalaBear, width := 1, assertions := [.constant koalaBear] } : Artifact).decode
        KoalaBear).isNone ∧
    (({ fieldSize := koalaBear, width := 1, assertions := [.column 1] } : Artifact).decode
        KoalaBear).isNone ∧
    (({ fieldSize := 7, width := 1, assertions := [.column 0] } : Artifact).decode
        KoalaBear).isNone := by
  decide +kernel

theorem decode_accepts_canonical :
    (({ fieldSize := koalaBear, width := 1,
        assertions := [.add (.column 0) (.constant (koalaBear - 1))] } : Artifact).decode
      KoalaBear).isSome := by
  decide +kernel

end TestsClean.Refusals
