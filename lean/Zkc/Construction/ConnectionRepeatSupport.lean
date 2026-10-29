module

public import Zkc.Construction.ConnectionComputation
public import Zkc.Construction.ConnectionContext
public import Zkc.Construction.ConnectionLoopFrames

@[expose] public section

/-! Finite frame assembly for symbolic repeats. The carried interface is the
complete, role-visible data row. Captures retain the entire physical prefix;
iteration binders and ordered source frames are introduced once per body
certificate, independently of the count and maximum. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionComputation

/-- A complete data state visible to this role, with an exact scope row. -/
def visibleState (role : Nat) : List (List Nat) → List Ty → Bool
  | [], [] => true
  | scope :: scopes, ty :: types => scope.contains role && !ty.isHandle && visibleState role scopes types
  | _, _ => false

theorem visibleState_mask {role : Nat} {scopes : List (List Nat)} {types : List Ty}
    (checked : visibleState role scopes types = true) (model : DomainModel)
    (values : Values (Component model.Value) types) : maskValues role scopes values = values := by
  induction values generalizing scopes with
  | nil => rfl
  | cons value values ih =>
    cases scopes with
    | nil => simp [visibleState] at checked
    | cons scope scopes =>
      have visible : scope.contains role = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1
      have tail := (Bool.and_eq_true_iff.mp checked).2
      simp only [maskValues, List.headD_cons, List.tail_cons, Participant.restrict, visible, ↓reduceIte,
        ih tail]

theorem visibleState_data {role : Nat} {scopes : List (List Nat)} {types : List Ty}
    (checked : visibleState role scopes types = true) : types.all Domain.dataType = true := by
  induction types generalizing scopes with
  | nil => rfl
  | cons ty types ih =>
    cases scopes with
    | nil => simp [visibleState] at checked
    | cons scope scopes =>
      simp only [visibleState, Bool.and_eq_true_iff, Bool.not_eq_true'] at checked
      simp only [List.all_cons, Domain.dataType, checked.1.2, Bool.not_false, Bool.true_and, ih checked.2]

theorem visibleState_schema {role : Nat} {scopes : List (List Nat)} {types : List Ty}
    (checked : visibleState role scopes types = true) :
    Original.roleOutputSorts role scopes types = some (types.map ValueSort.data) := by
  induction types generalizing scopes with
  | nil => cases scopes <;> simp_all [visibleState, Original.roleOutputSorts]
  | cons ty types ih =>
    cases scopes with
    | nil => simp [visibleState] at checked
    | cons scope scopes =>
      simp only [visibleState, Bool.and_eq_true_iff, Bool.not_eq_true'] at checked
      simp [Original.roleOutputSorts, List.contains_iff_mem.mp checked.1.1, checked.1.2, ih checked.2]

/-- The complete encoder recovers actual present state values. -/
theorem visibleState_values {role : Nat} {scopes : List (List Nat)} {types : List Ty}
    (checked : visibleState role scopes types = true) (model : DomainModel)
    (values : Values (Component model.Value) types) {encoded : Domain.Environment model.toCarriers}
    (found : Original.roleOutputValues role scopes values = some encoded) :
    ∃ actual : Values model.Value types, values = actual.present ∧ Domain.encodeValues actual = some encoded := by
  induction values generalizing scopes encoded with
  | nil =>
    cases scopes with
    | nil => exact ⟨.nil, rfl, found⟩
    | cons => simp [visibleState] at checked
  | cons value values ih =>
    cases scopes with
    | nil => simp [visibleState] at checked
    | cons scope scopes =>
      simp only [visibleState, Bool.and_eq_true_iff, Bool.not_eq_true'] at checked
      have visible := List.contains_iff_mem.mp checked.1.1
      cases rest : Original.roleOutputValues role scopes values with
      | none => simp [Original.roleOutputValues, rest] at found
      | some physicals =>
        obtain ⟨actuals, same, encodedTail⟩ := ih checked.2 rest
        cases value with
        | none => simp [Original.roleOutputValues, rest, visible] at found
        | some actual =>
          cases encodedHead : Domain.Value.encode _ actual with
          | none => simp [Original.roleOutputValues, rest, visible, encodedHead] at found
          | some physical =>
            simp only [Original.roleOutputValues, rest, visible, ↓reduceIte, bind, Option.bind,
              encodedHead, Option.some.injEq] at found
            subst encoded
            exact ⟨.cons actual actuals, by rw [same]; rfl,
              by simp [Domain.encodeValues, encodedHead, encodedTail]⟩

theorem visibleState_encode {role : Nat} {scopes : List (List Nat)} {types : List Ty}
    (checked : visibleState role scopes types = true) (model : DomainModel)
    (values : Values model.Value types) :
    Original.roleOutputValues role scopes values.present = Domain.encodeValues values := by
  induction values generalizing scopes with
  | nil =>
    cases scopes with
    | nil => rfl
    | cons => simp [visibleState] at checked
  | cons value values ih =>
    cases scopes with
    | nil => simp [visibleState] at checked
    | cons scope scopes =>
      simp only [visibleState, Bool.and_eq_true_iff, Bool.not_eq_true'] at checked
      simp only [Original.roleOutputValues, Values.present, List.contains_iff_mem.mp checked.1.1,
        ↓reduceIte, ih checked.2, Domain.encodeValues, bind, Option.bind]
      cases Domain.encodeValues values <;> cases Domain.Value.encode _ value <;> rfl

abbrev RepeatScope (types : List Ty) (scope : Scope) : Scope := .value .index :: .tuple types :: scope

def repeatLift {types : List Ty} {scope : Scope} : Rename scope (RepeatScope types scope) :=
  fun binder => .there (.there binder)

def repeatState {scope : Scope} (types : List Ty) : Values (Comp [] (RepeatScope types scope)) types :=
  mapValues (fun position => .read (.there .here) position) (Operands.identity types)

def repeatInputs {scope : Scope} {spec : RepeatSpec} (captures : Values (Comp [] scope) spec.captures) :
    Values (Comp [] (RepeatScope spec.state scope)) (.index :: (spec.state ++ spec.captures)) :=
  .cons (.present (.var .here)) ((repeatState spec.state).append (mapValues (Comp.rename repeatLift) captures))

def profileCells {scope : Scope} (context : Context) : Layout scope :=
  match context.profile with
  | .plain => []
  | .fiatShamir _ => [.history context.suite]

def repeatLayout {scope : Scope} (context : Context) (layout : Layout scope) (types : List Ty) :
    Layout (RepeatScope types scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename repeatLift) ++
    [.data (.present (.var .here))] ++ cells (repeatState types) ++ profileCells context

def repeatExitLayout {scope : Scope} (context : Context) (layout : Layout scope) (types : List Ty) :
    Layout (.tuple types :: scope) :=
  (layout.map Cell.retireHistory).map (Cell.rename .there) ++ cells (readComps types) ++ profileCells context

def repeatFrames {scope : Scope} {types : List Ty} (frames : ScopedFrames scope) (site : String) :
    ScopedFrames (RepeatScope types scope) :=
  frames.rename repeatLift ++ [⟨site, .var .here⟩]

theorem repeatState_eval {model : DomainModel} {scope : Scope} {types : List Ty}
    (binders : Binders model scope) (values : Values (Component model.Value) types) (index : Nat) :
    Comps.eval (LawResults.empty model) (repeatState types) (.cons index (.cons values binders)) = values := by
  apply values_ext
  intro ty position
  rw [comps_get_eval, repeatState, get_mapValues, Operands.identity_get]
  rfl

theorem repeatInputs_eval {model : DomainModel} {scope : Scope} {spec : RepeatSpec}
    (binders : Binders model scope) (values : Values (Component model.Value) spec.state) (index : Nat)
    (captures : Values (Comp [] scope) spec.captures) :
    Comps.eval (LawResults.empty model) (repeatInputs captures) (.cons index (.cons values binders)) =
      .cons (some index) (values.append (Comps.eval (LawResults.empty model) captures binders)) := by
  have renamed := comps_eval_map (LawResults.empty model) (Comp.rename repeatLift) binders
    (.cons index (.cons values binders))
    (comp_eval_rename (LawResults.empty model) repeatLift binders _ (fun _ => rfl)) captures
  simp only [repeatInputs, Comps.eval, Comp.eval, Term.eval, entryAt, firstEntry_cons,
    comps_eval_append, repeatState_eval, renamed]

/-- A full nominal row and the profile-owned reached history. -/
theorem profile_frame {model : DomainModel} {scope : Scope} {types : List Ty}
    (context : Context) (binders : Binders model scope) (history : Domain.History model.toCarriers)
    (components : Values (Comp [] scope) types) (values : Values model.Value types)
    (evaluated : Comps.eval (LawResults.empty model) components binders = values.present)
    {physical : Domain.Environment model.toCarriers} (encoded : Domain.encodeValues values = some physical) :
    Holds model binders history (cells components ++ profileCells context)
      (Domain.inputFrame context physical history) := by
  have row := cells_encoded binders history components values evaluated encoded
  cases profile : context.profile with
  | plain => simpa only [profileCells, Domain.inputFrame, profile, List.append_nil] using row
  | fiatShamir replacement =>
    have historyFrame : Holds model binders history [.history context.suite]
        [.transcript context.suite history] := .cons rfl .nil
    simpa [profileCells, Domain.inputFrame, Context.suite, Context.replacement?, profile] using row.append historyFrame

theorem Holds.repeatEnter {model : DomainModel} {scope : Scope} {types : List Ty}
    (context : Context) (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment)
    (values : Values model.Value types) (index : Nat) (nextHistory : Domain.History model.toCarriers) {physical : Domain.Environment model.toCarriers}
    (encoded : Domain.encodeValues values = some physical) :
    Holds model (.cons index (.cons values.present binders)) nextHistory (repeatLayout context layout types)
      (environment ++ .data (.index index) :: Domain.inputFrame context physical nextHistory) := by
  have retainedFrame := (related.retireHistory nextHistory).rename (repeatLift (types := types))
    (next := .cons index (.cons values.present binders)) (fun _ => rfl)
  have row := profile_frame context (.cons index (.cons values.present binders)) nextHistory
    (repeatState types) values (repeatState_eval binders values.present index) encoded
  have indexFrame : Holds model (scope := RepeatScope types scope) (.cons index (.cons values.present binders)) nextHistory
      [.data (ty := .index) (.present (.var .here))] [.data (.index index)] := by
    exact .cons ⟨index, rfl, rfl⟩ .nil
  simpa [repeatLayout, List.append_assoc] using
    retainedFrame.append (indexFrame.append row)

theorem Holds.repeatExit {model : DomainModel} {scope : Scope} {types : List Ty}
    (context : Context) (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment)
    (values : Values model.Value types) (nextHistory : Domain.History model.toCarriers)
    {physical : Domain.Environment model.toCarriers} (encoded : Domain.encodeValues values = some physical) :
    Holds model (.cons values.present binders) nextHistory (repeatExitLayout context layout types)
      (environment ++ Domain.inputFrame context physical nextHistory) := by
  have retainedFrame := (related.retireHistory nextHistory).rename (target := .tuple types :: scope) .there
    (next := .cons values.present binders) (fun _ => rfl)
  have row := profile_frame context (.cons values.present binders) nextHistory
    (readComps types) values (comps_eval_reads (LawResults.empty model) binders values.present) encoded
  simpa only [repeatExitLayout, List.append_assoc] using retainedFrame.append row

theorem repeatFrames_eval {model : DomainModel} {scope : Scope} {types : List Ty}
    (frames : ScopedFrames scope) (site : String) (binders : Binders model scope)
    (values : Values (Component model.Value) types) (index : Nat) :
    (repeatFrames frames site).eval model (.cons index (.cons values binders)) =
      frames.eval model binders ++ [⟨site, index⟩] := by
  rw [repeatFrames, ScopedFrames.eval_append, ScopedFrames.eval_rename repeatLift binders _ (fun _ => rfl)]
  rfl

end Zkc.Construction.ConnectionFrame
