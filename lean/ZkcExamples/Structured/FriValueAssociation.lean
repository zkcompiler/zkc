module

public import ZkcExamples.Structured.FriIndexCollections
public import Zkc.Source.Structured.BranchDerivation
public import Zkc.Source.Structured.OracleQueryDerivation

@[expose] public section

/-! The FRI checker compares the published value with the claimed value at
the query ordinal. Unassociated Query skips the lookup, including for an
empty supplied vector. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriValueAssociation
open Zkc.Source Zkc.Source.Structured
open FriSource (extension)
open FriSourceBodies FriSourceViews
attribute [local implicit_reducible] Op.arguments Op.results Op.regions Numerical.arguments Numerical.results
variable {model : DomainModel}

private theorem getChecked (xs : List (model.Field extension)) (size : xs.length < indexLimit)
    (i : Nat) (inside : i < xs.length) (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw (fun op ↦ .call op .done)
      (.exec (.numerical .vectorGet extension "")) (.cons xs (.cons i .nil)) .nil
      (.done (.cons xs[i] .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  let numeric := {model.toFieldModel with inverse := fun _ ↦ none}
  change primitiveOutcome (I := closedInterface) (Numerical.checkedEvaluateOn numeric extension ""
    .vectorGet (.cons xs (.cons i .nil))) = _
  have ingress : Numerical.checkValues numeric
      (.cons xs (.cons i .nil) : Values numeric.Value [.vector extension, .index]) = .ok () := by
    change (do Numerical.size xs.length; Numerical.require (i < indexLimit); pure ()) =
      (Except.ok () : Numerical.Result Unit)
    simp [Numerical.size, Numerical.require, size, inside.trans size, bind, Except.bind, pure, Except.pure]
  simp [Numerical.checkedEvaluateOn, ingress, Numerical.evaluateOn, Numerical.finish,
    List.getElem?_eq_getElem inside, pure, Except.pure, primitiveOutcome]
  rfl

def law (model : DomainModel) : ReferenceLaw model helper31Helper.inputs helper31Helper.outputs where
  body := helper31Body
  Requires _
    | .cons enabled (.cons xs (.cons i (.cons _ .nil))) =>
      enabled = true → xs.length < indexLimit ∧ i < xs.length
  reference
    | .cons enabled (.cons xs (.cons i (.cons actual .nil))) =>
      if enabled then
        match xs[i]? with
        | some claimed => .returned (.cons (decide (actual = claimed)) .nil)
        | none => .stopped .refused
      else .returned (.cons true .nil)
  valid table
    | .cons enabled (.cons xs (.cons i (.cons actual .nil))), checked => by
      cases enabled with
      | false => rfl
      | true =>
        obtain ⟨size, inside⟩ := checked rfl
        simp only [↓reduceIte, List.getElem?_eq_getElem inside]
        derive_process using (apply RegionMeaning.OperationLaw.identity; rfl)
          summarizing
            (apply branchAt true rfl
             derive_region using
               (first
                | exact getChecked xs size i inside table
                | apply RegionMeaning.OperationLaw.identity; rfl))

/-- Open the installed selected call while retaining its checked operands.
In particular the index is the query ordinal, independently of the sampled
position used in the table query. -/
theorem installed (enabled : Bool) (xs : List (model.Field extension)) (i : Nat)
    (actual : model.Field extension) (valid : enabled = true → xs.length < indexLimit ∧ i < xs.length) :
    OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper31Helper
      (.cons (OracleProtocol.concrete model .boolean enabled)
        (.cons (OracleProtocol.concrete model (.vector extension) xs) (.cons (OracleProtocol.concrete model .index i)
          (.cons (OracleProtocol.concrete model (.field extension) actual) .nil)))) =
      .done (.cons (OracleProtocol.concrete model .boolean
        (if enabled then xs[i]?.any (fun x ↦ decide (actual = x)) else true)) .nil) := by
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper31Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .boolean) enabled
      (.cons (ty := .vector extension) xs (.cons (ty := .index) i (.cons (ty := .field extension) actual .nil)))).present) = _
  rw [OracleProtocol.owned_present, (law model).invokeOn (helper := helper31Helper) unit.definitions unit.linked
    (by exact_body helper31Definition) (.cons enabled (.cons xs (.cons i (.cons actual .nil)))) valid]
  cases enabled with
  | false => rfl
  | true => simp only [law, ↓reduceIte, List.getElem?_eq_getElem (valid rfl).2]; rfl

end ZkcExamples.Structured.FriValueAssociation
