import Zkc.Source.RegionDerivation
import ZkcSecurity.ProgramLogic.Derivation
import Tests.Obligations

/-! One typed structured body connects the source derivation rules to the
obligation calculus and its security export. The guard has an explicit stopped
branch; the successful branch calls an effectful component and repeats it.
This is a structural control, not a new cryptographic protocol or native claim.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.StructuredObligations
open Zkc.Source Zkc.Obligations ZkcSecurity.Obligations Tests.Obligations

abbrev State := Nat × Nat
abbrev Value (_ : Unit) := State
abbrev Tuple := Values Value [()]
def pack (state : State) : Tuple := .cons state .nil

inductive Op where
  | guard (allowed : Bool)
  | component
  | repeat (count : Nat)

abbrev dialect : Dialect where
  Ty := Unit
  Op := Op
  arguments _ := [()]
  results _ := [()]
  regions
    | .guard _ => [([()], [()]), ([()], [()])]
    | .component => []
    | .repeat _ => [([()], [()])]

def lift (process : State → PIR.Process sendSignature State)
    (args : Tuple) : PIR.Process sendSignature Tuple :=
  (process (args.get .here)).bind (fun state => .done (pack state))

def meaning : RegionMeaning dialect sendSignature where
  Value := Value
  operation
    | .guard allowed, args, .cons yes (.cons no .nil) =>
        if allowed = true then yes args else no args
    | .component, args, .nil => lift increment args
    | .repeat count, args, .cons body .nil => PIR.repeatN count body args

abbrev identity : PIR.OperationInterpretation sendSignature sendSignature :=
  fun operation => .call operation .done

theorem callbacks_identity {signatures : List (List Unit × List Unit)}
    (bodies : Values (RegionFunction Value sendSignature) signatures) :
    RegionFunctions.translate (dialect := dialect) identity bodies = bodies := by
  induction bodies with
  | nil => rfl
  | cons body rest ih => simp [RegionFunctions.translate, ih]

theorem operation_law (op : Op) (args : Values Value (dialect.arguments op))
    (callbacks : Values (RegionFunction Value sendSignature) (dialect.regions op)) :
    meaning.OperationLaw identity op args callbacks (meaning.operation op args callbacks) := by
  intro bodies same
  have equal : bodies = callbacks := by simpa only [callbacks_identity] using same
  subst bodies
  exact PIR.Process.interpret_identity _

def returns {Γ : List Unit} (reference : Var Γ ()) : Region dialect Γ [()] :=
  .ret (.cons reference .nil)

def component : Region dialect [()] [()] :=
  .letOp .component (.cons .here .nil) .nil (returns .here)

theorem tuple_cases {property : Tuple → Prop}
    (step : ∀ state, property (pack state)) : ∀ tuple, property tuple := by
  intro tuple
  cases tuple with
  | cons value rest => cases rest; exact step value

theorem prepend_here {Γ : List Unit} (env : Environment Value Γ) (values : Tuple) :
    (env.prepend values) .here = values.get .here := by
  cases values with
  | cons value rest => cases rest; rfl

theorem component_derived (args : Tuple) :
    Region.Derivation meaning identity component args.get (lift increment args) := by
  apply tuple_cases (property := fun args => Region.Derivation meaning identity component args.get (lift increment args))
  intro state
  unfold component
  have law := Region.Derivation.letOp (meaning := meaning) (operations := identity)
    (env := (pack state).get) .component (.cons .here .nil) .nil
    (operation_law _ _ _) (fun values => Region.Derivation.ret (.cons .here .nil) _)
  simpa [meaning, returns, lift, pack, Operands.eval, Environment.prepend, Environment.push,
    Values.get, PIR.Process.bind_assoc, PIR.Process.bind] using law

def continuing (count : Nat) : Region dialect [()] [()] :=
  .letOp .component (.cons .here .nil) .nil
    (.letOp (.repeat count) (.cons .here .nil) (.cons component .nil) (returns .here))

theorem continuing_derived (count : Nat) (args : Tuple) :
    Region.Derivation meaning identity (continuing count) args.get
      ((lift increment args).bind (PIR.repeatN count (lift increment))) := by
  unfold continuing
  have law := Region.Derivation.letOp (meaning := meaning) (operations := identity)
    (env := args.get) .component (.cons .here .nil) .nil
    (operation_law _ _ _) (fun values =>
      Region.Derivation.letOp (meaning := meaning) (operations := identity) (.repeat count) (.cons .here .nil)
        (.cons component_derived .nil) (operation_law _ _ _)
        (fun result => Region.Derivation.ret (.cons .here .nil) _))
  have eta : ∀ values : Tuple, Values.cons (values.get .here) .nil = values :=
    tuple_cases (fun _ => rfl)
  simpa only [meaning, returns, Operands.eval, prepend_here, Values.get,
    PIR.Process.bind_assoc, eta, PIR.Process.bind_done] using law

def body (allowed : Bool) (count : Nat) : Region dialect [()] [()] :=
  .letOp (.guard allowed) (.cons .here .nil)
    (.cons (continuing count) (.cons (.stop .reject) .nil)) (returns .here)

def view (allowed : Bool) (count : Nat) (args : Tuple) : PIR.Process sendSignature Tuple :=
  if allowed = true then (lift increment args).bind (PIR.repeatN count (lift increment)) else .halt .reject

theorem body_derived (allowed : Bool) (count : Nat) (args : Tuple) :
    Region.Derivation meaning identity (body allowed count) args.get (view allowed count args) := by
  unfold body
  have law := Region.Derivation.letOp (meaning := meaning) (operations := identity)
    (env := args.get) (.guard allowed) (.cons .here .nil)
    (.cons (continuing_derived count) (.cons (fun _ => .stop .reject _) .nil))
    (operation_law _ _ _) (fun values => Region.Derivation.ret (.cons .here .nil) _)
  have eta : ∀ values : Tuple, Values.cons (values.get .here) .nil = values := tuple_cases (fun _ => rfl)
  simpa only [view, meaning, returns, Operands.eval, Values.get, prepend_here,
    eta, PIR.Process.bind_done] using law

theorem repeat_lift (count : Nat) (state : State) :
    PIR.repeatN count (lift increment) (pack state) =
      (PIR.repeatN count increment state).bind (fun result => .done (pack result)) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    change ((increment state).bind (fun result => .done (pack result))).bind _ = _
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, PIR.repeatN, ih]

theorem view_equation (allowed : Bool) (count : Nat) (state : State) :
    view allowed count (pack state) =
      (slice allowed count state).bind (fun result => .done (pack result)) := by
  simp only [view, slice]
  split
  · change ((increment state).bind (fun result => .done (pack result))).bind _ = _
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, repeat_lift]
  · rfl

def Post (state : State) (count : Nat) (history reached : List Nat) (result : Tuple) : Prop :=
  (result.get .here).1 = state.1 + count + 1 ∧ (result.get .here).2 = state.2 ∧
    reached.length = history.length + count + 1

def derived (allowed : Bool) (count : Nat) (history : List Nat) (state : State) :
    Derivation sendInterface sendEscape (Post state count history) history
      ((body allowed count).denote meaning (pack state).get) := by
  have equation := (body_derived allowed count (pack state)).sound
  rw [PIR.Process.interpret_identity, view_equation] at equation
  apply Derivation.transport equation
  exact (slice_derived allowed count history state).bind _ (fun _ _ valid => .done valid)

noncomputable def exported (allowed : Bool) (count : Nat) (history : List Nat) (state : State)
    (charge : List Nat → Nat → ENNReal) :
    (chargedCapability sendInterface (Post state count history) charge).Export
      (history, (body allowed count).denote meaning (pack state).get) :=
  exportCapability ((derived allowed count history state).mapEscape
    (fun _ _ _ impossible => impossible.elim))

theorem stopped (count : Nat) (state : State) :
    (body false count).denote meaning (pack state).get = .halt .reject := by
  simpa only [PIR.Process.interpret_identity, view, Bool.false_eq_true, ite_false]
    using (body_derived false count (pack state)).sound

end TestsSecurity.StructuredObligations

#print axioms TestsSecurity.StructuredObligations.exported
