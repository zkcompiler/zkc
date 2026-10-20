module

public import ZkcSecurity.Examples.CompiledGuessFiatShamir

@[expose] public section

/-! The application claim of the subject `guess`.

The guessing fixture's source retains no contract. Its claim is the language of
the imported ArkLib verifier (`CompiledGuessFiatShamir.verifier`), whose
worst-case round-by-round soundness is stated at the empty language
(`CompiledGuessFiatShamir.sound`): an offset is false when it is outside that
language, so every offset is false. The claim is read from the upstream
security statement the family's certificate is imported from, not chosen by the
evidence: `language` is the language argument of `sound`. -/

namespace ZkcSecurity.Examples.Subjects.Guess.Contract
open Zkc.Source Zkc.Source.Structured

/-- The language at which the imported verifier's soundness is stated. -/
def language (F : Type) : Set F := ∅

/-- The imported soundness theorem is stated at `language`. -/
theorem sound {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] :
    (ZkcSecurity.Examples.CompiledGuessFiatShamir.verifier (F := F)).rbrSoundnessWorstCase
      ZkcSecurity.Examples.CompiledGuessFiatShamir.init ZkcSecurity.Examples.CompiledGuessFiatShamir.impl
      (language F) {true} ZkcSecurity.Examples.CompiledGuessFiatShamir.error :=
  ZkcSecurity.Examples.CompiledGuessFiatShamir.sound

/-- The offset of a statement. -/
def offset {F G : Type} : Values (assignment F G) [.field "bls12-381.fr"] → F
  | .cons value .nil => value

/-- A statement is false when its offset is outside the imported language. -/
def falseStatement {F G : Type} (statement : Values (assignment F G) [.field "bls12-381.fr"]) : Prop :=
  offset statement ∉ language F

theorem falseStatement_all {F G : Type} (statement : Values (assignment F G) [.field "bls12-381.fr"]) :
    falseStatement statement :=
  fun member => member

end ZkcSecurity.Examples.Subjects.Guess.Contract
