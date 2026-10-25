module

public import Zkc.Claims.Wire

public section

/-! Kernel contexts retain typed parameters, readings, captures and path facts.
An attachment string has no logical force. Substitution must establish every
target premise in the source context.
-/

set_option autoImplicit false
namespace Zkc.Obligations
universe u v w

structure Context (Parameters : Type u) where
  facts : Parameters → Prop

namespace Context
variable {S : Type u} {T : Type v} {U : Type w}

@[expose] def Entails (context : Context S) (goal : S → Prop) : Prop :=
  ∀ parameters, context.facts parameters → goal parameters

structure Morphism (source : Context S) (target : Context T) where
  substitution : S → T
  valid : ∀ parameters, source.facts parameters → target.facts (substitution parameters)

def Morphism.identity (context : Context S) : Morphism context context :=
  ⟨id, fun _ holds => holds⟩

def Morphism.then {first : Context S} {middle : Context T} {last : Context U}
    (left : Morphism first middle) (right : Morphism middle last) : Morphism first last :=
  ⟨right.substitution ∘ left.substitution, fun parameters holds => right.valid _ (left.valid parameters holds)⟩

theorem Morphism.pullback {source : Context S} {target : Context T}
    (morphism : Morphism source target) {goal : T → Prop} (proof : target.Entails goal) :
    source.Entails (goal ∘ morphism.substitution) :=
  fun parameters holds => proof _ (morphism.valid parameters holds)

@[expose] def withFact (context : Context S) (fact : S → Prop) : Context S :=
  ⟨fun parameters => context.facts parameters ∧ fact parameters⟩

def establish (context : Context S) {fact : S → Prop} (proof : context.Entails fact) :
    Morphism context (context.withFact fact) :=
  ⟨id, fun parameters holds => ⟨holds, proof parameters holds⟩⟩

/-- Returned facts can depend on the original captures and returned value. -/
@[expose] def extend (context : Context S) (Value : S → Type v)
    (returned : (parameters : S) → Value parameters → Prop) : Context (Sigma Value) :=
  ⟨fun values => context.facts values.1 ∧ returned values.1 values.2⟩

end Context

structure Obligation (Parameters : Type u) where
  identifier : String
  context : Context Parameters
  goal : Parameters → Prop
  responsibility : Zkc.Claims.Responsibility

@[expose] def Obligation.Proof {Parameters : Type u} (obligation : Obligation Parameters) : Prop :=
  obligation.context.Entails obligation.goal

@[expose] def Obligation.record {Parameters : Type u} (obligation : Obligation Parameters)
    (attachment : String) : Zkc.Claims.Obligation :=
  ⟨obligation.identifier, attachment, obligation.Proof, obligation.responsibility⟩

end Zkc.Obligations
