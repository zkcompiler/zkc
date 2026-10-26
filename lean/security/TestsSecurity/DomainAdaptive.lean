module

public import ZkcSecurity.FiatShamir.DomainAdaptive
public import ZkcSecurity.FiatShamir.DomainBinding
public import ZkcSecurity.FiatShamir.DomainUniform
public import TestsSecurity.DomainReduction

@[expose] public section

/-! Adaptive binding controls: the whole raw statement is bound, including
malformed vectors. The bridge retains the existing typed/keyed theorem. -/
set_option autoImplicit false
namespace TestsSecurity.DomainAdaptive
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir
open ZkcSecurity.FiatShamir.DomainReduction
abbrev carriers := Structured.uniformCarriers Bool Unit
abbrev types : List Structured.Ty := [.vector "scalar", .index]
abbrev Statement := Values carriers.Value types

def statement (data : List Bool) (count : Nat) : Statement := .cons data (.cons count .nil)

theorem binding_contains_vector_and_count (data : List Bool) (count : Nat) :
    (publicCodec (carriers := carriers) types [0, 1] rfl rfl "application").encode (statement data count) =
      [.publicBinding ⟨"application", [(0, .vector "scalar" data), (1, .index count)]⟩] :=
  rfl

/-- A malformed empty table remains a distinct, representable statement. -/
theorem malformed_not_erased :
    (publicCodec (carriers := carriers) types [0, 1] rfl rfl "application").encode (statement [] 1) ≠
      (publicCodec (carriers := carriers) types [0, 1] rfl rfl "application").encode (statement [false, true] 1) := by
  intro same
  have equal := (publicCodec (carriers := carriers) types [0, 1] rfl rfl "application").injective same
  cases equal

theorem binding_determines :
    Typed.Determined (publicCodec (carriers := carriers) types [0, 1] rfl rfl "application").encode :=
  (publicCodec types [0, 1] rfl rfl "application").determined

/-- Resetting every statement to an empty history loses adaptive determination. -/
theorem empty_binding_refused :
    ¬ Typed.Determined (fun _ : Bool => ([] : Domain.History carriers)) := by
  intro determined
  have bad := determined false true [] [] rfl
  cases bad

#print axioms ZkcSecurity.FiatShamir.DomainReduction.Bridge.soundness_charged
#print axioms ZkcSecurity.FiatShamir.DomainReduction.Compiled.soundness_charged
#print axioms ZkcSecurity.FiatShamir.DomainReduction.Compiled.adaptive_soundness_charged
#print axioms ZkcSecurity.FiatShamir.DomainReduction.CoherentTo.run_congr

end TestsSecurity.DomainAdaptive

namespace TestsSecurity.DomainAdaptive
open OracleComp OracleSpec Zkc.Construction ZkcSecurity.FiatShamir

/-- An adaptive adversary may revisit a cached key before choosing its proof. -/
def repeatedQuery : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw carriers)))
    (Domain.Proof carriers) := do
  let _ ← Typed.ask (Raw := @Domain.Raw carriers) (R := Typed.ByLast Domain.Raw) []
    (.challenge TestsSecurity.DomainReduction.origin)
  let _ ← Typed.ask (Raw := @Domain.Raw carriers) (R := Typed.ByLast Domain.Raw) []
    (.challenge TestsSecurity.DomainReduction.origin)
  pure []

/-- Both visits remain in the ordered log and read the same table answer. -/
theorem repeated_log (table : (key : Domain.History carriers) → Typed.ByLast Domain.Raw key) :
    tableQueryLog repeatedQuery table =
      [⟨[.challenge TestsSecurity.DomainReduction.origin],
          table [.challenge TestsSecurity.DomainReduction.origin]⟩,
        ⟨[.challenge TestsSecurity.DomainReduction.origin],
          table [.challenge TestsSecurity.DomainReduction.origin]⟩] := by
  simp [repeatedQuery, Typed.ask, Typed.answer, bind_map_left, Typed.tableQueryLog_map]

end TestsSecurity.DomainAdaptive
