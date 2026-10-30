module

public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentPrefix
public import ZkcSecurity.Bindings.Transcript.NominalField

@[expose] public section

/-! A table component with explicit nominal transcript occurrences. Occurrences
are caller data checked against the generated actual source view. The component
does not infer them from helper names or identify distinct nominal domains.
The full actual SSA Process remains the structural binding's subject; this
interface is its checked transcript reading.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir

variable {F G Frame : Type} [Field F] [DecidableEq F]

structure Schedule (field : String) where
  low : Nat → Origin
  high : Nat → Origin
  query : Nat → Origin
  delivery : Nat → Origin
  request : ∀ index, (query index).request = some (.draw field)

noncomputable def program (field : String) :
    Program (NominalField.signature F field) (Schedule field) (PrefixState F Frame) (Message.endpoints F) where
  claim state := state.scalar
  receive schedule state :=
    .call (.receive (schedule.low state.point.length)) fun low =>
      .call (.receive (schedule.high state.point.length)) fun high => .done (some (low, high))
  query schedule state _ := .query (schedule.query state.point.length) (schedule.request _)
  challenge _ _ _ reply := reply
  deliver schedule state _ challenge :=
    .call (.deliver (schedule.delivery state.point.length) challenge) fun _ => .done ()
  advance _ state message challenge := state.advance message challenge

noncomputable def layout (field : String) :
    Layout (program (F := F) (Frame := Frame) field) where
  entries := PrefixState.entries
  shape := PrefixState.entries_shape
  advance _ state message challenge := PrefixState.advance_entries state message challenge
  claim _ _ _ _ := rfl

noncomputable def queries (field : String) :
    QueryInterface (program (F := F) (Frame := Frame) field) (NominalField.interface (G := G) field) where
  event schedule state _ := .challenge (schedule.query state.point.length)
  decode schedule state _ raw := by
    change Option F
    exact some (by simpa only [Domain.Raw, schedule.request _, Request.draw] using raw)
  challenge schedule state _ raw :=
    by simpa only [Domain.Raw, schedule.request _, Request.draw] using raw
  absorbed _ _ _ := rfl
  decoded schedule state message raw reply same := by
    dsimp only [program] at same ⊢
    exact Option.some.inj same.symm

end ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
