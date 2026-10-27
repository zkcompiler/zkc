module

public import Zkc.Executable.DomainNativeOperationSoundness

@[expose] public section
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source

private def advancesTranscript : Operation → Bool
  | .observe _ _ | .challenge _ _ _ => true
  | _ => false

private theorem readOperation_advances (sorts : List ValueSort) (current : Nat) (site : String)
    (resolved : Resolved) (references : List Nat) (operation : Operation) (declared : List ValueSort)
    (advances : Bool) (reading : readOperation sorts current site resolved references = .ok (operation, declared, advances)) :
    advances = advancesTranscript operation := by
  unfold readOperation at reading
  split at reading <;> try (cases reading; rfl)
  all_goals first | (simp at reading) | (split at reading <;> cases reading)
  all_goals rfl

private theorem nativeResults_advances (program : Structured.Program) (context : Context) (scope : NativeScope)
    (operation : Operation) (references : List Nat) (slots : List NativeSlot) (advances : Bool)
    (checked : nativeResults program context scope operation references = some (slots, advances)) :
    advances = advancesTranscript operation := by
  unfold nativeResults at checked
  split at checked <;> try (cases checked; rfl)
  all_goals repeat' split at checked
  all_goals cases checked
  all_goals rfl

theorem nativeOperation_reading (program : Structured.Program) (context : Context) (scope final : NativeScope)
    (site : String) (resolved : Resolved) (references : List Nat) (operation : Operation)
    (declared : List ValueSort) (advances : Bool)
    (reading : readOperation scope.reading.sorts scope.current site resolved references = .ok (operation, declared, advances))
    (checked : checkNativeItem program context (.step ⟨operation, references, declared, []⟩ 1) scope = some final) :
    final.reading = ⟨scope.reading.sorts ++ declared,
      if advances then scope.reading.sorts.length + declared.length - 1 else scope.current⟩ := by
  obtain ⟨slots, moves, resultCheck, rfl, rfl⟩ := checkNativeStep_results program context scope final operation references declared 1 checked
  have same := (nativeResults_advances program context scope operation references slots moves resultCheck).trans
    (readOperation_advances scope.reading.sorts scope.current site resolved references operation _ advances reading).symm
  subst moves
  simp [NativeScope.reading, NativeScope.append]

end Zkc.Executable.DomainVM
