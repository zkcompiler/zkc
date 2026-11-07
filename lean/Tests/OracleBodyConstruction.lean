module

public import Zkc.Source.Structured.OracleBody
public import Zkc.Source.DeriveRegion
public meta import Zkc.Source.OperationFacts

@[expose] public section
set_option autoImplicit false
namespace Tests.OracleBodyConstruction
open Zkc.Source Zkc.Source.Structured

def kind : OracleKind := .table .index none

def helper : Helper := ⟨"combine", .math, [.index, .index, .index], [.index]⟩

/-- A structurally independent virtual component, with two distinct source
handles and one captured parameter passed to its mathematical helper. -/
def body (first second : OracleLocation) :
    Region protocolDialect [.oracle kind, .oracle kind, .index, .index] [.index] :=
  .letOp (.oracle (.query kind none) first)
    (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.oracle (.query kind none) second)
    (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.calculate (.invoke helper) rfl)
    (.cons (.there .here) (.cons .here
      (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .ret (.cons .here .nil)

/-- The author supplies only the mathematical helper equation. Query sites,
operand installation, captures and final layout follow from the source body. -/
theorem composed (model : DomainModel)
    (tables : Evaluation.ComponentTablesOn model.toCarriers
      (oracleReadInterface model.toCarriers))
    (first second : OracleLocation) (left right : OracleAnchor) (position captured : Nat)
    (combine : Nat → Nat → Nat)
    (law : ∀ a b, invoke tables.components helper
      (Values.cons (Value := model.Value) (ty := .index) a
        (.cons b (.cons captured .nil))).present =
      .done (Values.cons (Value := model.Value) (ty := .index) (combine a b) .nil).present) :
    (body first second).denote (oracleBodyMeaning model tables)
      (Values.cons (Value := model.Value) (ty := .oracle kind) left
        (.cons right (.cons position (.cons captured .nil)))).present.get =
      .call ⟨kind, left, position, first, []⟩ fun a ↦
      .call ⟨kind, right, position, second, []⟩ fun b ↦
      .done (.cons (some (combine a b)) .nil) := by
  derive_process using
    (apply RegionMeaning.OperationLaw.identity
     source_facts [law])

#print axioms composed

/-- Equal handle types do not permit changing the first requested publication.
This follows from the actual source equation, independently of the helper's
mathematics or whether two queried cells happen to agree. -/
theorem swapped_handles (model : DomainModel)
    (tables : Evaluation.ComponentTablesOn model.toCarriers
      (oracleReadInterface model.toCarriers))
    (first second : OracleLocation) (left right : OracleAnchor) (position captured : Nat)
    (combine : Nat → Nat → Nat) (different : left ≠ right)
    (law : ∀ a b, invoke tables.components helper
      (Values.cons (Value := model.Value) (ty := .index) a
        (.cons b (.cons captured .nil))).present =
      .done (Values.cons (Value := model.Value) (ty := .index) (combine a b) .nil).present) :
    (body first second).denote (oracleBodyMeaning model tables)
      (Values.cons (Value := model.Value) (ty := .oracle kind) left
        (.cons right (.cons position (.cons captured .nil)))).present.get ≠
      .call ⟨kind, right, position, first, []⟩ (fun a ↦
      .call ⟨kind, left, position, second, []⟩ fun b ↦
      .done (.cons (some (combine a b)) .nil)) := by
  rw [composed model tables first second left right position captured combine law]
  intro same
  exact different (congrArg OracleRead.anchor (PIR.Process.call.inj same).1)

/-- Matching parameters does not discard the supplied law's mathematical premise. -/
theorem conditional_fact (condition : Nat → Prop) (a b : Nat) (valid : condition a)
    (law : ∀ value, condition value → some value = some b) : some a = some b := by
  source_facts [law, valid]

/-- An output can be determined by an association premise after matching the
operation. It must not become a separate value-search obligation first. -/
theorem inferred_association (certificate : Nat → Prop) (a : Nat)
    (law : ∀ result, result = a + 1 → certificate result) : ∃ result, certificate result := by
  apply Exists.intro
  source_facts [law]

example (condition : Nat → Prop) (_a b : Nat)
    (_law : ∀ value, condition value → some value = some b) : True := by
  fail_if_success
    have : some _a = some b := by source_facts [_law]
  trivial

#print axioms swapped_handles
#print axioms conditional_fact
#print axioms inferred_association

end Tests.OracleBodyConstruction
