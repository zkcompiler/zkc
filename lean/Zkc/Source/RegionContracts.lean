module

public import Zkc.Source.RegionTotality

@[expose] public section

/-! Conditional mathematical contracts on the existing structured carrier.
Inputs may require representability or checked indexing bounds. The postcondition
relates ordered returned values to the original environment, so it can express
identity and length facts without confusing either with unconditional totality.
-/

namespace Zkc.Source

variable {dialect : Dialect} {interface : PIR.Signature}

/-- Immediate return with a postcondition, under an explicit input premise.
This is a predicate usable by `Verification.Certificate`, not another program
representation or a security judgment. -/
def Region.Contract (meaning : RegionMeaning dialect interface) {Γ out}
    (body : Region dialect Γ out)
    (pre : Environment meaning.Value Γ → Prop)
    (post : Environment meaning.Value Γ → Values meaning.Value out → Prop) : Prop :=
  ∀ env, pre env → ∃ values, body.denote meaning env = .done values ∧ post env values

theorem Region.Contract.consequence (meaning : RegionMeaning dialect interface) {Γ out}
    (body : Region dialect Γ out)
    {pre pre' : Environment meaning.Value Γ → Prop}
    {post post' : Environment meaning.Value Γ → Values meaning.Value out → Prop}
    (contract : body.Contract meaning pre post)
    (input : ∀ env, pre' env → pre env)
    (output : ∀ env values, pre' env → post env values → post' env values) :
    body.Contract meaning pre' post' := by
  intro env valid
  obtain ⟨values, returned, facts⟩ := contract env (input env valid)
  exact ⟨values, returned, output env values valid facts⟩

/-- The suffix can use facts about both original inputs and returned values.
The law is conditional on reachable intermediate results. -/
theorem Region.Contract.bind (meaning : RegionMeaning dialect interface) {Γ mid out}
    (body : Region dialect Γ mid) (next : Region dialect (mid ++ Γ) out)
    (pre : Environment meaning.Value Γ → Prop)
    (between : Environment meaning.Value Γ → Values meaning.Value mid → Prop)
    (post : Environment meaning.Value Γ → Values meaning.Value out → Prop)
    (bodyLaw : body.Contract meaning pre between)
    (nextLaw : ∀ env values, pre env → between env values →
      ∃ result, next.denote meaning (env.prepend values) = .done result ∧ post env result) :
    (body.bind next).Contract meaning pre post := by
  intro env valid
  obtain ⟨values, bodyReturns, facts⟩ := bodyLaw env valid
  obtain ⟨result, nextReturns, resultFacts⟩ := nextLaw env values valid facts
  refine ⟨result, ?_, resultFacts⟩
  rw [Region.bind_return meaning body next env values bodyReturns]
  exact nextReturns

/-- Exact process equality transports a conditional contract, retaining its
premises. Equal returned values alone would not establish this law. -/
theorem Region.Contract.of_equivalent (meaning : RegionMeaning dialect interface) {Γ out}
    {left right : Region dialect Γ out}
    {pre : Environment meaning.Value Γ → Prop}
    {post : Environment meaning.Value Γ → Values meaning.Value out → Prop}
    (same : left.Equivalent meaning right) (contract : left.Contract meaning pre post) :
    right.Contract meaning pre post := by
  intro env valid
  obtain ⟨values, returned, facts⟩ := contract env valid
  exact ⟨values, (same env).symm.trans returned, facts⟩

end Zkc.Source
