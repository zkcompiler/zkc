module

public import Zkc.Obligations.Component
public import ZkcSecurity.Families.Sumcheck.Derivation
public import ZkcSecurity.Families.Sumcheck.Completeness

public section

/-! Sumcheck exports the same component boundary for every representation and
remaining dimension. The reference, degree laws and sampler are explicit
mathematical inputs. A caller's source/body equation is reused by the sound and
honest consumers; no protocol name participates in the contract.
-/

namespace ZkcSecurity.Families.Sumcheck
open Zkc.Obligations Zkc.Transcript ZkcSecurity.Obligations

variable {F : Type} [Field F] [DecidableEq F] {I : PIR.Signature} {Context : Type}
  {State : Nat → Type} {message : Message F} {reference : Reference F}
  {program : Program I Context State message} {E P : Type} {Raw : E → Type}

namespace Representation

/-- Admissibility belongs to both sides. Ill-shaped states are outside this
family relation; the enclosing actual verifier must handle them separately. -/
@[expose] def relation (representation : Representation program reference) (n : Nat) :
    ClaimRelation (State n) Unit where
  Holds state _ := representation.Yes state
  No := representation.No
  no_excludes _ _ wrong yes := wrong.2 yes.2

end Representation

namespace Contract

@[expose] noncomputable def component (representation : Representation program reference)
    (n count : Nat) (actual : Context × State (n + count) → PIR.Process I (State n)) :
    ComponentInterface I E (Context × State (n + count)) (State n) where
  Parameters := Unit
  Input := State (n + count)
  InputWitness := Unit
  Output := State n
  OutputWitness := Unit
  input := representation.relation (n + count)
  output := representation.relation n
  body := actual
  Scope _ _ _ := True
  inputView _ runtime _ := some runtime.2
  outputView _ _ _ result := some result

/-- The only new wrapper is a typed application of the existing residual
theorem. Malformed roots cannot use this by assuming admissibility: their entry
law must establish the input relation or prove the actual refusal branch. -/
noncomputable def soundness
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (absorb : Interface I E P Raw) [∀ event, SampleableType (Raw event)]
    (queries : QueryInterface program absorb)
    (charge : List E → E → ENNReal)
    (sampling : queries.ConditionalBound representation messageDegree referenceDegree charge)
    (n count : Nat) (actual : Context × State (n + count) → PIR.Process I (State n))
    (binding : ∀ runtime, actual runtime = program.remaining count runtime.1 runtime.2) :
    SoundnessContract (component representation n count actual) absorb (boundedEscape charge) :=
  SoundnessContract.ofFamily (fun runtime => program.remaining count runtime.1 runtime.2) binding
    (fun _ runtime _ => representation.No runtime.2)
    (fun _ _ _ result => representation.No result)
    (fun _ _ _ _ wrong => ReadbackHolds.some.mp wrong)
    (fun _ runtime history wrong => Consumers.residual representation messageLaws referenceLaws
      queries sampling count runtime.1 runtime.2 history wrong)
    (fun _ _ _ result wrong => ⟨result, rfl, wrong⟩)

/-- Independent all-replies scope preservation; no claim truth or falsity is
assumed. It can frame an earlier true or gap call before a later false claim. -/
theorem preserves
    (interaction : PIR.Interaction I)
    (invariant : {k : Nat} → State k → Prop)
    (preserved : ∀ {k} (context : Context) (state : State (k + 1)), invariant state →
      ∀ m r, invariant (program.advance context state m r))
    (n count : Nat) (actual : Context × State (n + count) → PIR.Process I (State n))
    (binding : ∀ runtime, actual runtime = program.remaining count runtime.1 runtime.2)
    (runtime : Context × State (n + count)) (phase : interaction.Phase)
    (initial : invariant runtime.2) :
    PIR.Boundary.Returns interaction (fun result _ => invariant result) (actual runtime) phase := by
  rw [binding]
  exact program.returns interaction invariant preserved count runtime.1 runtime.2 phase initial

/-- Honest execution uses exactly the same binding argument as soundness,
with additional producer/handler laws at the actual reached state. -/
theorem honest {H O : Type}
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (handler : PIR.Handler I H O)
    (invariant : Nat → {k : Nat} → Context → State k → H → Prop)
    (ready : Nat → {k : Nat} → Context → State (k + 1) → message.Carrier → H → Prop)
    (execution : HonestRunLaws program handler invariant ready)
    (honestMessage : HonestMessageLaw representation ready)
    (n count : Nat) (actual : Context × State (n + count) → PIR.Process I (State n))
    (binding : ∀ runtime, actual runtime = program.remaining count runtime.1 runtime.2)
    (runtime : Context × State (n + count)) (state : H)
    (yes : representation.Yes runtime.2) (initial : invariant count runtime.1 runtime.2 state) :
    ∃ result final events,
      (actual runtime).run handler state = ⟨.returned result, final, events⟩ ∧
      representation.Yes result ∧ invariant 0 runtime.1 result final :=
  Consumers.bound_honest_run representation messageLaws referenceLaws handler invariant ready
    execution honestMessage count runtime.1 runtime.2 state (actual runtime) (binding runtime) yes initial

end Contract
end ZkcSecurity.Families.Sumcheck
