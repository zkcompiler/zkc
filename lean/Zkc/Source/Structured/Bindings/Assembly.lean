module

public import Zkc.Source.Structured.Bindings.Component
public import Zkc.Source.Structured.NormalForm.Presentation

@[expose] public section

/-! Assembly of a checked normal form at an actual admitted invocation.
Only the existing normalizer and participant denotation give meaning here.
Helper and callee obligations concern their exact operational tables. -/

namespace Zkc.Source.Structured.Bindings
open NormalForm

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The helper table used by the silent open participant and its normal form. -/
abbrev helpers (payload : UnitPayload) : Evaluation.ComponentTables F G (participantInterface F G) :=
  payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩

/-- Helper laws are anchored to complete admitted bodies, including captured
dependencies. Names and source hashes alone never establish this equation. -/
theorem helper_body (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (helpers payload).components definition.helper args =
      definition.body.component (Evaluation.meaning (.silent _) (helpers payload).closed)
        (Evaluation.componentOperation (.silent _) (helpers payload)) args.get := by
  calc
    _ = (invoke (payload.tables F G).components definition.helper args).interpret forgetSites :=
      ((Evaluation.ComponentTables.fold_forgetSites payload.definitions).components definition.helper args).symm
    _ = _ := by
      rw [payload.component_invoke_body definition member args]
      exact Evaluation.component_interpret forgetSites observedSites_forgetSites
        (Evaluation.ComponentTables.fold_forgetSites payload.definitions) definition.body args.get

/-- Glue for an actual retained callee or root. Inputs and outputs keep their
complete optional-component ABI; masks are those of the admitted declaration. -/
theorem invocation (payload : UnitPayload) (definition : CheckedProtocol)
    (member : definition ∈ payload.protocols)
    (sig : Signature) (role roster : Nat) (pattern : InputPattern definition.inputs)
    (form : Form sig.laws sig.callees pattern.scope definition.outputs)
    (normalized : normalize sig definition.body role roster pattern = .ok form)
    (matched : form.CallsMatch)
    (results : LawResults (ringModel F G) sig.laws)
    (processes : CalleeProcesses (ringModel F G) sig.callees)
    (context : ProtocolContext) (distinct : RosterDistinct context role roster)
    (input : Values (Component (assignment F G)) definition.inputs)
    (binders : Binders (ringModel F G) pattern.scope)
    (environment : pattern.environment (ringModel F G) binders =
      maskValues (context.roles role) (context.mapScopes definition.inputScopes) input)
    (laws : LawsHold (helpers payload).toOn results
      (maskValues (context.roles role) (context.mapScopes definition.inputScopes) input))
    (callees : CalleesHold (payload.plainProtocolTable F G) processes
      (maskValues (context.roles role) (context.mapScopes definition.inputScopes) input)) :
    invokeProtocol (payload.plainProtocolTable F G) definition.signature context (context.roles role) input =
      (form.denote (ringModel F G) (helpers payload).toOn results context
        (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) context (context.roles role))
        processes binders).bind fun out =>
          .done (maskValues (context.roles role) (context.mapScopes definition.outputScopes) out) := by
  refine (protocol_invoke_body_view (.silent _) (participantActions F G) (helpers payload)
    payload.protocols payload.protocolsLinked definition member definition.body definition.exactBody.symm context
    (context.roles role) input).trans ?_
  exact bind_congr_left (sound_uniform sig definition.body role roster pattern form normalized matched
    context distinct (helpers payload) (payload.plainProtocolTable F G) results processes binders _
    environment laws callees) _

/-- Empty law catalogues introduce no hidden implementation assumption. -/
def emptyResults (model : DomainModel) : LawResults model [] := ⟨fun entry => entry.elim0⟩

theorem emptyLaws {model : DomainModel} {I : PIR.Signature}
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) {inputs : List Ty}
    (input : Values (Component model.Value) inputs) :
    LawsHold tables (emptyResults model) input := fun entry => entry.elim0

/-- Substitute already proved whole-process bindings at callee sites. Context
renaming and the callee's complete return mask stay in the existing rule. -/
theorem callees_from_bindings {model : DomainModel} {keys : List CalleeKey}
    (protocols : ProtocolTable model.Value (Interface model))
    (actual presented : CalleeProcesses model keys) {inputs : List Ty}
    (input : Values (Component model.Value) inputs)
    (known : CalleesHold protocols actual input)
    (equations : ∀ entry context binders,
      RosterDistinct context (calleeAt keys entry).role (calleeAt keys entry).signature.roles.length →
      actual entry context binders = presented entry context binders) :
    CalleesHold protocols presented input := by
  intro entry context binders others pinned distinct
  exact (known entry context binders others pinned distinct).trans
    (bind_congr_left (equations entry context binders distinct) _)

/-- Replace one dependent callee entry using its whole-process equation to a
checked reference table. Other entries retain their existing proofs, so a
sequence of selected bindings need not recheck the complete dispatch table. -/
theorem callees_update {model : DomainModel} {keys : List CalleeKey}
    (protocols : ProtocolTable model.Value (Interface model))
    (reference presented : CalleeProcesses model keys) (entry : Fin keys.length)
    (replacement : (context : ProtocolContext) →
      Binders model (calleeAt keys entry).pattern.scope →
      PIR.Process (Interface model)
        (Values (Component model.Value) (calleeAt keys entry).signature.outputs))
    {inputs : List Ty} (input : Values (Component model.Value) inputs)
    (referenceHold : CalleesHold protocols reference input)
    (presentedHold : CalleesHold protocols presented input)
    (equation : ∀ context binders,
      RosterDistinct context (calleeAt keys entry).role (calleeAt keys entry).signature.roles.length →
      reference entry context binders = replacement context binders) :
    CalleesHold protocols (Function.update presented entry replacement) input := by
  intro selected context binders others pinned distinct
  by_cases same : selected = entry
  · subst selected
    rw [Function.update_self]
    exact (referenceHold entry context binders others pinned distinct).trans
      (bind_congr_left (equation context binders distinct) _)
  · rw [Function.update_of_ne same]
    exact presentedHold selected context binders others pinned distinct

/-- Context substitution cannot make an unrelated, admitted local role visible. -/
theorem mapped_contains (context : ProtocolContext) (role roster : Nat)
    (distinct : RosterDistinct context role roster) (scope : List Nat)
    (bounded : ∀ other ∈ scope, other < roster) :
    (scope.map context.roles).contains (context.roles role) = scope.contains role := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨other, member, same⟩
    by_cases equal : other = role
    · simpa [equal] using member
    · exact False.elim (distinct other (bounded other member) equal same)
  · intro member
    exact ⟨role, member, rfl⟩

theorem mask_context {Value : Ty → Type} (context : ProtocolContext) (role roster : Nat)
    (distinct : RosterDistinct context role roster) :
    {types : List Ty} → (scopes : List (List Nat)) →
    (bounded : ∀ scope ∈ scopes, ∀ other ∈ scope, other < roster) →
    (values : Values (Component Value) types) →
    maskValues (context.roles role) (context.mapScopes scopes) values = maskValues role scopes values
  | [], _, _, .nil => rfl
  | ty :: _, scopes, bounded, .cons value rest => by
    have headBound : ∀ other ∈ scopes.headD [], other < roster := by
      cases scopes with
      | nil => simp
      | cons head tail => exact bounded head List.mem_cons_self
    have same := mapped_contains context role roster distinct (scopes.headD []) headBound
    have tailBound : ∀ scope ∈ scopes.tail, ∀ other ∈ scope, other < roster := by
      intro scope member
      exact bounded scope (List.mem_of_mem_tail member)
    cases scopes with
    | nil => simpa [maskValues, ProtocolContext.mapScopes, Participant.restrict] using
        congrArg (Values.cons (ty := ty) (Value := Component Value) none) (mask_context context role roster distinct [] tailBound rest)
    | cons head tail =>
      simp only [maskValues, ProtocolContext.mapScopes, List.map_cons, List.headD_cons,
        List.tail_cons] at *
      rw [same]
      exact congrArg (Values.cons _) (mask_context context role roster distinct tail tailBound rest)

/-- Static output masking commutes with operand selection. -/
theorem staticMask_eval {Value : Ty → Type} (role : Nat) {types kept : List Ty}
    (values : Values (Component Value) types) (scopes : List (List Nat))
    (positions : Operands types kept) :
    staticMask role values scopes positions = maskValues role scopes (Operands.eval values.get positions) := by
  induction positions generalizing scopes with
  | nil => rfl
  | cons position positions ih =>
    simp only [staticMask, Operands.eval, maskValues, Participant.restrict, ih]

/-- Static masking of the full ABI is the ordinary local-role mask. -/
theorem staticMask_identity {Value : Ty → Type} (role : Nat) {types : List Ty}
    (scopes : List (List Nat)) (values : Values (Component Value) types) :
    staticMask role values scopes (Operands.identity types) = maskValues role scopes values := by
  rw [staticMask_eval]
  congr 1
  exact values_ext fun position => by simp only [Operands.get_eval, Operands.identity_get]

/-- Reapplying the local output mask preserves the entire actual invocation. -/
theorem invocation_mask (payload : UnitPayload) (definition : CheckedProtocol)
    (member : definition ∈ payload.protocols) (context : ProtocolContext)
    (role roster : Nat) (distinct : RosterDistinct context role roster)
    (bounded : ∀ scope ∈ definition.outputScopes, ∀ other ∈ scope, other < roster)
    (input : Values (Component (assignment F G)) definition.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition.signature context (context.roles role) input =
      (invokeProtocol (payload.plainProtocolTable F G) definition.signature context (context.roles role) input).bind
        fun out => .done (staticMask role out definition.outputScopes (Operands.identity definition.outputs)) := by
  have equation := protocol_invoke_body_view (.silent _) (participantActions F G) (helpers payload)
    payload.protocols payload.protocolsLinked definition member definition.body definition.exactBody.symm
    context (context.roles role) input
  dsimp only [CheckedProtocol.signature] at *
  refine equation.trans ?_
  refine Eq.trans ?_ (congrArg (fun p => p.bind fun out => .done
    (staticMask role out definition.outputScopes (Operands.identity definition.outputs))) equation.symm)
  rw [PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext out
  simp only [PIR.Process.bind, staticMask_identity]
  rw [← mask_context context role roster distinct definition.outputScopes bounded,
    maskValues_idempotent]

/-- A structural fallback keeps actual callees and their complete returned ABI.
A mathematical callee presentation can replace it only through CalleesHold. -/
def actualCallees (payload : UnitPayload) (keys : List CalleeKey) :
    CalleeProcesses (ringModel F G) keys := fun entry context binders =>
  invokeProtocol (payload.plainProtocolTable F G) (calleeAt keys entry).signature context
    (context.roles (calleeAt keys entry).role)
    ((calleeAt keys entry).pattern.environment (ringModel F G) binders)

/-- The fallback is checked from exact declarations, fill and mask equations,
never a callee's name or the claimed target. -/
theorem actualCallees_hold (payload : UnitPayload) (keys : List CalleeKey)
    (declarations : ∀ entry : Fin keys.length,
      ∃ definition ∈ payload.protocols, definition.signature = (calleeAt keys entry).signature)
    (fills : ∀ (entry : Fin keys.length)
      (binders : Binders (ringModel F G) (calleeAt keys entry).pattern.scope)
      (others : Values (Component (assignment F G)) (calleeAt keys entry).pattern.absentTypes),
      (calleeAt keys entry).pattern.fill (ringModel F G) binders others =
        (calleeAt keys entry).pattern.environment (ringModel F G) binders)
    (bounded : ∀ entry : Fin keys.length, ∀ scope ∈ (calleeAt keys entry).signature.outputScopes,
      ∀ other ∈ scope, other < (calleeAt keys entry).signature.roles.length)
    {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) (actualCallees payload keys) input := by
  intro entry context binders others _ distinct
  rw [fills entry binders others]
  obtain ⟨definition, member, signature⟩ := declarations entry
  have bound : ∀ scope ∈ definition.outputScopes, ∀ other ∈ scope,
      other < definition.roles.length := by
    simpa only [← signature, CheckedProtocol.signature] using bounded entry
  have same := fun input => invocation_mask (F := F) (G := G) payload definition member context
    (calleeAt keys entry).role definition.roles.length
    (by simpa only [← signature, CheckedProtocol.signature] using distinct) bound input
  change ∀ input : Values (Component (assignment F G)) definition.signature.inputs,
    invokeProtocol (payload.plainProtocolTable F G) definition.signature context _ input =
      (invokeProtocol (payload.plainProtocolTable F G) definition.signature context _ input).bind
        (fun out => .done (staticMask (calleeAt keys entry).role out definition.signature.outputScopes
          (Operands.identity definition.signature.outputs))) at same
  rw [signature] at same
  exact same _

/-- An unrestricted component binder for every ABI position. -/
def optionalPattern : (types : List Ty) → InputPattern types
  | [] => .nil
  | _ :: rest => .cons .optional (optionalPattern rest)

def optionalBinders (model : DomainModel) : {types : List Ty} →
    Values (Component model.Value) types → Binders model (optionalPattern types).scope
  | [], _ => .nil
  | ty :: rest, values =>
    let values : Values (Component model.Value) (ty :: rest) := values
    match values with
    | .cons value values => .cons value (optionalBinders model values)

theorem optional_environment (model : DomainModel) : {types : List Ty} →
    (input : Values (Component model.Value) types) →
    (optionalPattern types).environment model (optionalBinders model input) = input
  | [], .nil => rfl
  | ty :: rest, input => by
    cases input with
    | cons value input =>
      change Values.cons value ((optionalPattern rest).environment model (optionalBinders model input)) = _
      rw [optional_environment model input]

theorem optional_absentTypes : (types : List Ty) → (optionalPattern types).absentTypes = []
  | [] => rfl
  | _ :: rest => optional_absentTypes rest

theorem optional_fill (model : DomainModel) : (types : List Ty) →
    (binders : Binders model (optionalPattern types).scope) →
    (others : Values (Component model.Value) (optionalPattern types).absentTypes) →
    (optionalPattern types).fill model binders others = (optionalPattern types).environment model binders
  | [], _, _ => rfl
  | ty :: rest, binders, others => by
    change Values (Slot.Value model) (.component ty :: (optionalPattern rest).scope) at binders
    cases binders with
    | cons value binders =>
      change Values.cons (Value := Component model.Value) (ty := ty) value ((optionalPattern rest).fill model binders others) = _
      rw [optional_fill model rest binders others]
      rfl

end Zkc.Source.Structured.Bindings
