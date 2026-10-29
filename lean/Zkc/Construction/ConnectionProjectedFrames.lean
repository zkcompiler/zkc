module

public import Zkc.Construction.ConnectionRepeatSupport
public import Zkc.Construction.ConnectionLibrary

@[expose] public section

/-! Physical rows for role-private symbolic repeat state. Hidden logical
components remain absent and consume no physical cell. The complete caller
prefix and the reached transcript are retained independently of projection. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

def rosterCheck (context : ProtocolContext) (role roster : Nat) : Bool :=
  (List.range roster).all (fun other => other == role || context.roles other != context.roles role)

theorem rosterCheck_sound (context : ProtocolContext) (role roster : Nat)
    (checked : rosterCheck context role roster = true) : RosterDistinct context role roster := by
  intro other bounded different
  have selected := List.all_eq_true.mp checked other (List.mem_range.mpr bounded)
  simpa [different] using selected

def visibility (role : Nat) (scopes : List (List Nat)) : List Bool :=
  scopes.map (fun scope => scope.contains role)

theorem mask_visibility {model : DomainModel} {role other : Nat}
    {scopes elsewhere : List (List Nat)} (same : visibility role scopes = visibility other elsewhere)
    {types : List Ty} (values : Values (Component model.Value) types) :
    maskValues role scopes values = maskValues other elsewhere values := by
  induction values generalizing scopes elsewhere with
  | nil => rfl
  | cons value values ih =>
    cases scopes with
    | nil => cases elsewhere <;> simp_all [visibility, maskValues]
    | cons scope scopes =>
      cases elsewhere with
      | nil => simp [visibility] at same
      | cons otherScope otherScopes =>
        have bits := List.cons.inj same
        simp only [maskValues, List.headD_cons, List.tail_cons, ih bits.2, bits.1]

theorem roleValues_visibility {model : DomainModel} {role other : Nat}
    {scopes elsewhere : List (List Nat)} (same : visibility role scopes = visibility other elsewhere)
    {types : List Ty} (values : Values (Component model.Value) types) :
    Original.roleOutputValues role scopes values = Original.roleOutputValues other elsewhere values := by
  induction values generalizing scopes elsewhere with
  | nil =>
    cases scopes <;> cases elsewhere <;> simp_all [visibility, Original.roleOutputValues]
  | cons value values ih =>
    cases scopes with
    | nil => cases elsewhere <;> simp_all [visibility, Original.roleOutputValues]
    | cons scope scopes =>
      cases elsewhere with
      | nil => simp [visibility] at same
      | cons otherScope otherScopes =>
        have bits := List.cons.inj same
        have visible : (role ∈ scope) = (other ∈ otherScope) := by
          simpa only [List.contains_iff_mem] using congrArg (fun bit => bit = true) bits.1
        simp only [Original.roleOutputValues, ih bits.2, visible]

def roleCells {scope : Scope} (role : Nat) : List (List Nat) → {types : List Ty} →
    Values (Comp [] scope) types → Layout scope
  | _, _, .nil => []
  | scopes, _, .cons value values =>
      (if (scopes.headD []).contains role then [.data value] else []) ++
        roleCells role scopes.tail values

theorem roleCells_frame {model : DomainModel} {scope : Scope} (role : Nat)
    (scopes : List (List Nat)) (binders : Binders model scope)
    (history : Domain.History model.toCarriers) {types : List Ty}
    (components : Values (Comp [] scope) types) {physical : Domain.Environment model.toCarriers}
    (encoded : Original.roleOutputValues role scopes
      (Comps.eval (LawResults.empty model) components binders) = some physical) :
    Holds model binders history (roleCells role scopes components) physical := by
  induction components generalizing scopes physical with
  | nil =>
    cases scopes with
    | nil =>
      simp only [Original.roleOutputValues, Comps.eval, Option.some.injEq] at encoded
      subst physical
      exact .nil
    | cons => simp [Original.roleOutputValues] at encoded
  | @cons ty types component components ih =>
    cases scopes with
    | nil => simp [Original.roleOutputValues] at encoded
    | cons scope scopes =>
      cases rest : Original.roleOutputValues role scopes (Comps.eval (LawResults.empty model) components binders) with
      | none => simp [Original.roleOutputValues, Comps.eval, rest] at encoded
      | some remaining =>
        have tail := ih scopes rest
        by_cases visible : role ∈ scope
        · cases evaluated : component.eval (LawResults.empty model) binders with
          | none => simp [Original.roleOutputValues, Comps.eval, rest, visible, evaluated] at encoded
          | some value =>
            cases found : Domain.Value.encode ty value with
            | none => simp [Original.roleOutputValues, Comps.eval, rest, visible, evaluated, found] at encoded
            | some head =>
              simp only [Original.roleOutputValues, Comps.eval, rest, visible, ↓reduceIte,
                evaluated, found, bind, Option.bind, Option.some.injEq] at encoded
              subst physical
              have head : Cell.Holds model binders history (.data component) head := ⟨value,evaluated,found⟩
              have bit : scope.contains role = true := List.contains_iff_mem.mpr visible
              unfold Holds
              simpa only [roleCells, List.headD_cons, List.tail_cons, bit, ↓reduceIte,
                List.singleton_append] using (List.Forall₂.cons head tail)
        · cases evaluated : component.eval (LawResults.empty model) binders with
          | none =>
            simp only [Original.roleOutputValues, Comps.eval, rest, visible, ↓reduceIte,
              evaluated, bind, Option.bind, Option.some.injEq] at encoded
            subst physical
            simpa [roleCells, visible] using tail
          | some => simp [Original.roleOutputValues, Comps.eval, rest, visible, evaluated] at encoded

/-- Masked state terms tell normalization that private components are absent. -/
def projectedState {scope : Scope} (role : Nat) (scopes : List (List Nat)) (types : List Ty) :
    Values (Comp [] (RepeatScope types scope)) types :=
  mapValues (Comp.rename .there) (calleeOutputs role scopes (Operands.identity types))

def projectedInputs {scope : Scope} (role : Nat) {spec : RepeatSpec}
    (captures : Values (Comp [] scope) spec.captures) :
    Values (Comp [] (RepeatScope spec.state scope)) (.index :: (spec.state ++ spec.captures)) :=
  .cons (.present (.var .here)) ((projectedState role spec.stateScopes spec.state).append
    (mapValues (Comp.rename repeatLift) captures))

def projectedLayout {scope : Scope} (context : Context) (role : Nat) (scopes : List (List Nat))
    (layout : Layout scope) (types : List Ty) : Layout (RepeatScope types scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename repeatLift) ++ [.data (.present (.var .here))] ++
    roleCells role scopes (projectedState role scopes types) ++ profileCells context

def projectedExitLayout {scope : Scope} (context : Context) (role : Nat) (scopes : List (List Nat))
    (layout : Layout scope) (types : List Ty) : Layout (.tuple types :: scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename .there) ++
    roleCells role scopes (calleeOutputs role scopes (Operands.identity types)) ++ profileCells context

theorem projectedState_eval {model : DomainModel} {scope : Scope} {types : List Ty}
    (role : Nat) (scopes : List (List Nat)) (binders : Binders model scope)
    (values : Values (Component model.Value) types) (index : Nat) :
    Comps.eval (LawResults.empty model) (projectedState role scopes types) (.cons index (.cons values binders)) =
      maskValues role scopes values := by
  have renamed := comps_eval_map (LawResults.empty model) (Comp.rename .there)
    (show Binders model (.tuple types :: scope) from .cons values binders)
    (show Binders model (RepeatScope types scope) from .cons index (.cons values binders))
    (fun {_} component => comp_eval_rename (LawResults.empty model) .there
      (show Binders model (.tuple types :: scope) from .cons values binders)
      (show Binders model (RepeatScope types scope) from .cons index (.cons values binders)) (fun _ => rfl) component)
    (calleeOutputs (laws := []) (Δ := scope) role scopes (Operands.identity types))
  exact renamed.trans ((comps_eval_calleeOutputs (LawResults.empty model) binders role values scopes
    (Operands.identity types)).trans (InputVisibility.staticMask_identity role scopes values))

theorem projectedInputs_eval {model : DomainModel} {scope : Scope} {spec : RepeatSpec}
    (role : Nat) (binders : Binders model scope) (values : Values (Component model.Value) spec.state)
    (index : Nat) (captures : Values (Comp [] scope) spec.captures) :
    Comps.eval (LawResults.empty model) (projectedInputs role captures) (.cons index (.cons values binders)) =
      .cons (some index) ((maskValues role spec.stateScopes values).append
        (Comps.eval (LawResults.empty model) captures binders)) := by
  have renamed := comps_eval_map (LawResults.empty model) (Comp.rename repeatLift) binders
    (.cons index (.cons values binders))
    (comp_eval_rename (LawResults.empty model) repeatLift binders _ (fun _ => rfl)) captures
  simp only [projectedInputs, Comps.eval, Comp.eval, Term.eval, entryAt, firstEntry_cons,
    comps_eval_append, projectedState_eval, renamed]

theorem projectedProfile_frame {model : DomainModel} {scope : Scope} (context : Context)
    (role : Nat) (scopes : List (List Nat)) (binders : Binders model scope)
    (history : Domain.History model.toCarriers) {types : List Ty}
    (components : Values (Comp [] scope) types) {physical : Domain.Environment model.toCarriers}
    (encoded : Original.roleOutputValues role scopes
      (Comps.eval (LawResults.empty model) components binders) = some physical) :
    Holds model binders history (roleCells role scopes components ++ profileCells context)
      (Domain.inputFrame context physical history) := by
  have row := roleCells_frame role scopes binders history components encoded
  cases profile : context.profile with
  | plain => simpa only [profileCells, Domain.inputFrame, profile, List.append_nil] using row
  | fiatShamir replacement =>
    have historyFrame : Holds model binders history [.history context.suite]
        [.transcript context.suite history] := .cons rfl .nil
    simpa [profileCells, Domain.inputFrame, Context.suite, Context.replacement?, profile] using row.append historyFrame

theorem Holds.projectedEnter {model : DomainModel} {scope : Scope} {types : List Ty}
    (context : Context) (role : Nat) (scopes : List (List Nat)) (binders : Binders model scope)
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers} (related : Holds model binders history layout environment)
    (values : Values (Component model.Value) types) (index : Nat) (nextHistory : Domain.History model.toCarriers)
    {physical : Domain.Environment model.toCarriers} (encoded : Original.roleOutputValues role scopes (maskValues role scopes values) = some physical) :
    Holds model (.cons index (.cons values binders)) nextHistory (projectedLayout context role scopes layout types)
      (environment ++ .data (.index index) :: Domain.inputFrame context physical nextHistory) := by
  have retainedFrame := (related.retireHistory nextHistory).rename (repeatLift (types := types))
    (next := .cons index (.cons values binders)) (fun _ => rfl)
  have row := projectedProfile_frame context role scopes (.cons index (.cons values binders)) nextHistory
    (projectedState role scopes types) (by rw [projectedState_eval]; exact encoded)
  have indexFrame : Holds model (scope := RepeatScope types scope) (.cons index (.cons values binders)) nextHistory
      [.data (ty := .index) (.present (.var .here))] [.data (.index index)] := .cons ⟨index,rfl,rfl⟩ .nil
  simpa [projectedLayout, List.append_assoc] using retainedFrame.append (indexFrame.append row)

theorem Holds.projectedExit {model : DomainModel} {scope : Scope} {types : List Ty}
    (context : Context) (role : Nat) (scopes : List (List Nat)) (binders : Binders model scope)
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers} (related : Holds model binders history layout environment)
    (values : Values (Component model.Value) types) (nextHistory : Domain.History model.toCarriers)
    {physical : Domain.Environment model.toCarriers} (encoded : Original.roleOutputValues role scopes (maskValues role scopes values) = some physical) :
    Holds model (.cons values binders) nextHistory (projectedExitLayout context role scopes layout types)
      (environment ++ Domain.inputFrame context physical nextHistory) := by
  have retainedFrame := (related.retireHistory nextHistory).rename (target := .tuple types :: scope) .there
    (next := .cons values binders) (fun _ => rfl)
  have row := projectedProfile_frame context role scopes (.cons values binders) nextHistory
    (calleeOutputs role scopes (Operands.identity types)) (by
      rw [comps_eval_calleeOutputs, InputVisibility.staticMask_identity]
      exact encoded)
  simpa only [projectedExitLayout, List.append_assoc] using retainedFrame.append row

end Zkc.Construction.ConnectionFrame
