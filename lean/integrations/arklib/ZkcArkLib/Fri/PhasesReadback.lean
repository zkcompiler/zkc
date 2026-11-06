module

public import ZkcArkLib.Fri.PhasesCausal
public import Zkc.Source.Structured.PublishedWordsLaws

/-!
# Local source readback obligation

This is the source-owned semantic fact needed to connect ideal words with actual base reads.
It is a local, typed obligation, not a constructed commitment implementation. The word is
a parameter fixed at publication. `live` is the parent's registry/state invariant and must
also be preserved by all intervening successful actions. Every read occurrence retains its
actual location and expansion path. Stops have no replacement value and keep their state
and events. The installed virtual Fold already supplies the two ordered child reads.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

open OracleComp
open Zkc Zkc.Source Zkc.Source.Structured

/-- Exact local read request for one published base word; no source cursor is invented. -/
def publishedRequest (d : String) (anchor : OracleAnchor) (position : ℕ)
    (location : OracleLocation) (expansion : List (OracleAnchor × OracleLocation)) : OracleRead :=
  ⟨.table (.field d) none, anchor, position, location, expansion⟩

/-- An obligation for the parent's causal publication profile over the existing source
action semantics. Successful reads must observe the already fixed word and retain `live`.
This structure has no default inhabitant and assumes no root equality or security bound. -/
structure PublishedReadback (model : DomainModel) (d : String) (n : ℕ)
    {S E : Type} (base : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) S E)
    (anchor : OracleAnchor) (word : Fin (2 ^ n) → model.Field d) (live : S → Prop) : Prop where
  read : ∀ (position : Fin (2 ^ n)) (location : OracleLocation)
    (expansion : List (OracleAnchor × OracleLocation)) (state : S), live state →
    ∀ result ∈ support (base (publishedRequest d anchor position.val location expansion) state),
    ∀ value, result.outcome = .returned value → value = word position ∧ live result.state

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
    PublishedWords.read (E := E) (publishedRequest d anchor position.val location expansion) state =
      ⟨.returned (word position), state, []⟩ := by
  have within := position.isLt
  have limit : stored.rows < indexLimit := (Bool.and_eq_true_iff.mp shape).1 |> of_decide_eq_true
  exact PublishedWords.read_compatible_cell (publishedRequest d anchor position.val location expansion)
    state stored (word position) found answer shape
    (by simp [publishedRequest, OracleStore.validRows, OracleKind.rows, limit])
    (by rw [cells, rows]; exact List.length_ofFn)
    (show position.val < stored.rows from rows.symm ▸ within) (by
      change stored.cells[position.val]? = _
      rw [cells, List.getElem?_ofFn, dite_eq_left within]
      rfl)

theorem fixed_word_readback {model : DomainModel} {d : String} {n : Nat} {Aux E : Type}
    (anchor : OracleAnchor) (word : Fin (2 ^ n) → model.Field d)
    (stored : PublishedWords.Word model (.field d))
    (answer : stored.kind.answer = .field d)
    (shape : OracleStore.validRows stored.kind stored.rows = true)
    (rows : stored.rows = 2 ^ n) (cells : stored.cells = List.ofFn word) :
    PublishedReadback model d n (PublishedWords.readM (E := E)) anchor word
      (fun state : PublishedWords.State model Aux ↦
        PublishedWords.find state.words (.field d) anchor = some stored) where
  read position location expansion state found result member value returned := by
    have same := eq_of_mem_support_pure _ member
    rw [same, read_fixed_word anchor word stored answer shape rows cells position location expansion
      state found] at returned ⊢
    exact ⟨(PIR.Outcome.returned.inj returned).symm, found⟩

set_option backward.isDefEq.respectTransparency false in
/-- A discharged local readback law rewrites only the successful reply at this occurrence.
The existing continuation and stopped poststate/event prefix remain intact. -/
theorem PublishedReadback.continuation {model : DomainModel} {d : String} {n : ℕ}
    {S E A : Type}
    {base : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) S E}
    {anchor : OracleAnchor} {word : Fin (2 ^ n) → model.Field d} {live : S → Prop}
    (law : PublishedReadback model d n base anchor word live)
    (position : Fin (2 ^ n)) (location : OracleLocation)
    (expansion : List (OracleAnchor × OracleLocation)) (state : S) (valid : live state)
    (next : model.Field d → S → ProbComp (PIR.Execution S E A)) (post : A → Prop) :
    Pr{let result ← (base (publishedRequest d anchor position.val location expansion) state >>=
      fun head ↦ head.followM next)}[returned post result] =
    Pr{let result ← (base (publishedRequest d anchor position.val location expansion) state >>=
      fun head ↦ head.followM (fun _ after ↦ next (word position) after))}[
        returned post result] := by
  simp only [← bind_pure_comp, bind_assoc]
  apply prEvent_bind_congr_of_support
  intro head member
  simp only [bind_pure_comp]
  rw [prEvent_followM, prEvent_followM]
  cases eq : head.outcome with
  | stopped why => rfl
  | returned value => rw [(law.read position location expansion state valid head member value eq).1]

end ZkcSecurity.ArkLib.Fri.Phases
