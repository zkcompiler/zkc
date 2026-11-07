module

public import ZkcArkLib.Fri.PhasesReadback
public import Zkc.Source.Structured.RegisteredWord

/-! # Published-word readback for the source FRI phases

The ideal source provider discharges the mathematical phase's local readback obligation.
Words may have fixed or unsized shape annotations. The invariant is exact membership of the
previously published word; subsequent publications and ordinary auxiliary effects preserve it.
This does not assume a source-to-protocol equation or authenticate an arbitrary read handler.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.SourcePublication

open OracleComp
open Zkc Zkc.Source Zkc.Source.Structured

/-- Availability and exact return value for a word installed by the source
provider. The query may originate directly or inside a virtual expansion. -/
theorem read_fixed_word {model : DomainModel} {d : String} {n : Nat} {Aux E : Type}
    (anchor : OracleAnchor) (word : Fin (2 ^ n) → model.Field d)
    (stored : PublishedWords.Word model (.field d))
    (answer : stored.kind.answer = .field d)
    (shape : OracleStore.validRows stored.kind stored.rows = true)
    (rows : stored.rows = 2 ^ n) (cells : stored.cells = List.ofFn word)
    (position : Fin (2 ^ n)) (location : OracleLocation)
    (expansion : List (OracleAnchor × OracleLocation))
    (state : PublishedWords.State model Aux)
    (found : PublishedWords.find state.words (.field d) anchor = some stored) :
    PublishedWords.read (E := E) (Phases.publishedRequest d anchor position.val location expansion) state =
      ⟨.returned (word position), state, []⟩ :=
  PublishedWords.readAt (model := model) (row := .field d) (size := 2 ^ n) (E := E) anchor word stored answer shape rows cells position location expansion state found

theorem readback {model : DomainModel} {d : String} {n : Nat} {Aux E : Type}
    (anchor : OracleAnchor) (word : Fin (2 ^ n) → model.Field d)
    (stored : PublishedWords.Word model (.field d))
    (answer : stored.kind.answer = .field d)
    (shape : OracleStore.validRows stored.kind stored.rows = true)
    (rows : stored.rows = 2 ^ n) (cells : stored.cells = List.ofFn word) :
    Phases.PublishedReadback model d n (PublishedWords.readM (E := E)) anchor word
      (fun state : PublishedWords.State model Aux ↦
        PublishedWords.find state.words (.field d) anchor = some stored) where
  read position location expansion state found result member value returned := by
    have same := eq_of_mem_support_pure _ member
    rw [same, read_fixed_word anchor word stored answer shape rows cells position location expansion
      state found] at returned ⊢
    exact ⟨(PIR.Outcome.returned.inj returned).symm, found⟩

/-- The same publication invariant survives every independently proved table frame step. -/
theorem live_of_frame {model : DomainModel} {Aux : Type} {d : String}
    {before after : PublishedWords.State model Aux} {anchor : OracleAnchor}
    {stored : PublishedWords.Word model (.field d)}
    (frame : PublishedWords.Preserves before.words after.words)
    (live : PublishedWords.find before.words (.field d) anchor = some stored) :
    PublishedWords.find after.words (.field d) anchor = some stored :=
  frame.lookup (.field d) anchor stored live

end ZkcSecurity.ArkLib.Fri.SourcePublication
