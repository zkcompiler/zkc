module

public import ZkcArkLib.Fri.PhasesReadback
public import Zkc.Source.Structured.PublishedWordsLaws

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

/-- The source provider's fixed table supplies every successful local read, at the actual
occurrence and expansion path. Its exact unchanged poststate retains the publication invariant. -/
theorem readback {model : DomainModel} {d : String} {n : ℕ} {Aux E : Type}
    (anchor : OracleAnchor) (stored : PublishedWords.Word model (.field d))
    (word : Fin (2 ^ n) → model.Field d)
    (answer : stored.kind.answer = .field d)
    (shape : OracleStore.validRows stored.kind stored.rows = true)
    (rows : stored.rows = 2 ^ n) (cells : stored.cells = List.ofFn word)
    (supported : 2 ^ n < indexLimit) :
    Phases.PublishedReadback model d n (PublishedWords.readM (m := ProbComp) (E := E))
      anchor word (fun state : PublishedWords.State model Aux ↦
        PublishedWords.find state.words (.field d) anchor = some stored) := by
  constructor
  intro position location expansion state found result member value returned
  have requested : OracleStore.validRows
      (Phases.publishedRequest d anchor position.val location expansion).kind stored.rows = true := by
    simp [Phases.publishedRequest, OracleStore.validRows, OracleKind.rows, rows, supported]
  have selected : stored.cells[position.val]? = some (word position) := by
    simp [cells, position.isLt]
  have length : stored.cells.length = stored.rows := by
    rw [cells]
    exact (List.length_ofFn (f := word)).trans rows.symm
  have exactRead := PublishedWords.read_compatible_cell (E := E)
    (Phases.publishedRequest d anchor position.val location expansion) state stored (word position)
    found answer shape requested length
    (by simpa only [Phases.publishedRequest, rows] using position.isLt)
    selected
  have result_eq : result = ⟨.returned (word position), state, []⟩ := by
    simpa only [PublishedWords.readM, exactRead, mem_support_pure_iff] using member
  rw [result_eq] at returned ⊢
  cases returned
  exact ⟨rfl, found⟩

/-- The same publication invariant survives every independently proved table frame step. -/
theorem live_of_frame {model : DomainModel} {Aux : Type} {d : String}
    {before after : PublishedWords.State model Aux} {anchor : OracleAnchor}
    {stored : PublishedWords.Word model (.field d)}
    (frame : PublishedWords.Preserves before.words after.words)
    (live : PublishedWords.find before.words (.field d) anchor = some stored) :
    PublishedWords.find after.words (.field d) anchor = some stored :=
  frame.lookup (.field d) anchor stored live

end ZkcSecurity.ArkLib.Fri.SourcePublication
