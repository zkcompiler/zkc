module

/-! Typed verification interfaces independent of protocol-specific proof search.

An imported subject carries admission of the exact raw program. A contract is a
predicate on its actual meaning. Independent consumers turn this conformance
proof into conditional properties. Interfaces compose through proved adapters;
property conjunction does not invent independence or compatible security games.
-/

@[expose] public section

namespace Zkc.Verification

/-- An admitted program tied to one fixed decoder and the exact raw input. -/
structure Imported {Raw Program Error : Type}
    (decode : Raw → Except Error Program) (raw : Raw) where
  program : Program
  admitted : decode raw = .ok program

/-- Successful deterministic admission has only one program subject. -/
theorem Imported.unique {Raw Program Error : Type}
    {decode : Raw → Except Error Program} {raw : Raw}
    (first second : Imported decode raw) : first.program = second.program := by
  have h := first.admitted.symm.trans second.admitted
  exact Except.ok.inj h

/-- Assumptions describe the selected mathematical experiment, not inferred
properties of native providers. They remain visible in the resulting theorem. -/
structure Property (Model : Type) where
  assumptions : Model → Prop
  conclusion : Model → Prop

structure Consumer {Model : Type} (contract : Model → Prop) (property : Property Model) : Prop where
  prove : ∀ model, contract model → property.assumptions model → property.conclusion model

/-- One source-specific contract certificate can be reused by many consumers. -/
structure Certificate {Raw Program Error Model : Type}
    {decode : Raw → Except Error Program} {raw : Raw}
    (source : Imported decode raw) (denote : Program → Model) (contract : Model → Prop) : Prop where
  conforms : contract (denote source.program)

theorem Certificate.verify {Raw Program Error Model : Type}
    {decode : Raw → Except Error Program} {raw : Raw}
    {source : Imported decode raw} {denote : Program → Model}
    {contract : Model → Prop} (certificate : Certificate source denote contract)
    {property : Property Model} (consumer : Consumer contract property) :
    property.assumptions (denote source.program) →
      property.conclusion (denote source.program) :=
  consumer.prove _ certificate.conforms

/-- A contract adapter relates meanings explicitly; changing a model requires
a proof of conformance for its translated meaning. -/
structure Adapter {Left Right : Type} (source : Left → Prop) (target : Right → Prop) where
  translate : Left → Right
  preserves : ∀ model, source model → target (translate model)

def Adapter.then {A B C : Type} {first : A → Prop} {middle : B → Prop} {last : C → Prop}
    (left : Adapter first middle) (right : Adapter middle last) : Adapter first last where
  translate model := right.translate (left.translate model)
  preserves model conforms := right.preserves _ (left.preserves model conforms)

/-- Transport the complete property, including its actual experiment assumptions. -/
def Property.pullback {Left Right : Type} (property : Property Right) (translate : Left → Right) :
    Property Left where
  assumptions model := property.assumptions (translate model)
  conclusion model := property.conclusion (translate model)

theorem Consumer.along {Left Right : Type} {source : Left → Prop} {target : Right → Prop}
    {property : Property Right} (consumer : Consumer target property)
    (adapter : Adapter source target) : Consumer source (property.pullback adapter.translate) :=
  ⟨fun model conforms => consumer.prove _ (adapter.preserves model conforms)⟩

/-- Reuse two independent consumers of one contract without asserting a relation
between their different experiments or multiplying their error bounds. -/
def Property.and {Model : Type} (first second : Property Model) : Property Model where
  assumptions model := first.assumptions model ∧ second.assumptions model
  conclusion model := first.conclusion model ∧ second.conclusion model

theorem Consumer.and {Model : Type} {contract : Model → Prop} {first second : Property Model}
    (left : Consumer contract first) (right : Consumer contract second) :
    Consumer contract (first.and second) :=
  ⟨fun model conforms assumptions =>
    ⟨left.prove model conforms assumptions.1, right.prove model conforms assumptions.2⟩⟩

end Zkc.Verification
