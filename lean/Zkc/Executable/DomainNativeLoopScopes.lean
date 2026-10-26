module

public import Zkc.Executable.DomainNativeReadback

@[expose] public section
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform

def NativeScope.loopBody (scope : NativeScope) (carried : List NativeSlot) : NativeScope :=
  ⟨scope.slots ++ .data .index :: carried,
    match transcriptPosition (carried.map NativeSlot.sort) with
    | some position => scope.slots.length + 1 + position | none => scope.current⟩

def NativeScope.loopResult (scope : NativeScope) (carried : List NativeSlot) : NativeScope :=
  ⟨scope.slots ++ carried,
    match transcriptPosition (carried.map NativeSlot.sort) with
    | some position => scope.slots.length + position | none => scope.current⟩

theorem nativeLoop_results (program : Structured.Program) (context : Context)
    (scope final : NativeScope) (site : String) (maximum count : Nat) (references yielded : List Nat)
    (declared : List ValueSort) (body : List Code)
    (checked : checkNativeItem program context (.loop site maximum yielded (count :: references) declared body) scope = some final) :
    ∃ carried innerFinal,
      scope.slots[count]? = some (.data .index) ∧
      references.map (scope.slots[·]?) = carried.map some ∧
      declared = carried.map NativeSlot.sort ∧
      custody scope.reading.sorts scope.current references = true ∧
      checkNativeCode program context body (scope.loopBody carried) = some innerFinal ∧
      yielded.map (innerFinal.slots[·]?) = carried.map some ∧
      custody innerFinal.reading.sorts innerFinal.current yielded = true ∧
      (transcriptPosition declared = none → innerFinal.current = scope.current) ∧
      final = scope.loopResult carried := by
  simp only [checkNativeItem] at checked
  split at checked
  · cases checked
  · rename_i countSort
    have countChecked : scope.slots[count]? = some (.data .index) := by simpa using countSort
    cases read : references.mapM (scope.slots[·]?) with
    | none => simp [read] at checked
    | some carried =>
      simp only [read, bind, Option.bind] at checked
      split at checked
      · cases checked
      · rename_i admitted
        have declaredEq : carried.map NativeSlot.sort = declared := by tauto
        have initialCustody : custody scope.reading.sorts scope.current references = true := by
          have : (!(custody scope.reading.sorts scope.current references)) = false := by
            by_contra different
            apply admitted
            right
            simpa [NativeScope.reading] using different
          simpa using this
        subst declared
        change ((checkNativeCode program context body (scope.loopBody carried)).bind _) = some final at checked
        obtain ⟨innerFinal, bodyCheck, checked⟩ := Option.bind_eq_some_iff.mp checked
        split at checked
        · cases checked
        · rename_i invariants
          cases checked
          have yieldedEq : yielded.map (innerFinal.slots[·]?) = carried.map some := by tauto
          have finalCustody : custody innerFinal.reading.sorts innerFinal.current yielded = true := by
            have : (!(custody innerFinal.reading.sorts innerFinal.current yielded)) = false := by
              by_contra different
              apply invariants
              right; left
              simpa [NativeScope.reading] using different
            simpa using this
          exact ⟨carried, innerFinal, countChecked, mapM_optional _ read, rfl, initialCustody,
            bodyCheck, yieldedEq, finalCustody, by intro none; by_contra different; exact invariants (Or.inr (Or.inr ⟨none, different⟩)), rfl⟩

variable {F G : Type}

theorem Reached.extendSlots {suite : String} {key : Origin → Origin} {initial : History F G}
    {data scalar : List (Value F G)} {scope : NativeScope} {state next : State F G}
    {env values : Environment F G} {results : List (Value F G)}
    (reached : Reached suite key initial data scope.reading state env scalar)
    {slots : List NativeSlot} {current : Nat}
    (erases : Erases suite key initial values results)
    (holds : List.Forall₂ NativeSlot.Holds slots values)
    (live : (scalar ++ results)[current]? = some (.transcript next.live)) :
    Reached suite key initial data (⟨scope.slots ++ slots, current⟩ : NativeScope).reading next
      (env ++ values) (scalar ++ results) := by
  have schema := NativeScope.Holds.schema (scope := ⟨slots, 0⟩) holds
  refine ⟨reached.erases.append erases, ?_, ?_⟩
  · simpa [NativeScope.reading] using reached.native.extend
      (by rw [← erases.length]; simpa using congrArg List.length schema) (erases.sorted schema) live
  · simp [NativeScope.reading, List.map_append, reached.schema, schema]

end Zkc.Executable.DomainVM
