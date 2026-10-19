module

public import Zkc.Source.Structured.NormalForm.Soundness
public import Zkc.Source.Structured.ProtocolLinking
public import Zkc.Source.Structured.OpenLaws

@[expose] public section

/-! Presentations of forms and the instances of the soundness theorem that
generated modules cite.

* The uniform interpretation (one ring `F`, one module `G`) is the instance of
  the domain-model statement at `ringModel F G`, through the existing equation
  between the two participant meanings.
* An entry's participant is the entry body between its input and output masks.
  At the root context the masks are concrete, so an instance presents the
  masked process directly.
* A repeat callback returns its whole carried state; a role presents only its
  own positions, as values when they are always present and as components
  otherwise. `Form.finishes` checks, once per form, that every returned tuple
  has that shape, and the callback theorem factors the process through the
  presented tuple. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace NormalForm

variable {model : DomainModel} {laws : List LawKey}

/-! Presented tuples. -/

/-- A carried position's presented value: the value, or the component. -/
abbrev Presented (Value : Ty → Type) : Ty × Bool → Type
  | (ty, false) => Value ty
  | (ty, true) => Option (Value ty)

/-- One position is presented as itself, several as right-nested pairs. -/
abbrev Tuple (Value : Ty → Type) : List (Ty × Bool) → Type
  | [] => Unit
  | [position] => Presented Value position
  | position :: next :: rest => Presented Value position × Tuple Value (next :: rest)

section Tuples
variable {Value : Ty → Type}

def Tuple.ofValues : {positions : List (Ty × Bool)} → Values (Presented Value) positions → Tuple Value positions
  | [], .nil => ()
  | [_], .cons value .nil => value
  | _ :: _ :: _, .cons value rest => (value, Tuple.ofValues rest)

def Tuple.toValues : {positions : List (Ty × Bool)} → Tuple Value positions → Values (Presented Value) positions
  | [], _ => .nil
  | [_], value => .cons value .nil
  | _ :: _ :: _, value => .cons value.1 (Tuple.toValues value.2)

theorem Tuple.toValues_ofValues :
    {positions : List (Ty × Bool)} → (values : Values (Presented Value) positions) →
      Tuple.toValues (Tuple.ofValues values) = values
  | [], .nil => rfl
  | [_], .cons _ .nil => rfl
  | _ :: _ :: _, .cons value rest => by
    simp only [Tuple.ofValues, Tuple.toValues, Tuple.toValues_ofValues rest]

end Tuples

/-- The full returned tuple of the presented positions: other positions are absent. -/
def embed (Value : Ty → Type) : {out : List Ty} → (spec : Values (fun _ => Carried) out) →
    Values (Presented Value) (carried spec) → Values (Component Value) out
  | [], .nil, .nil => .nil
  | _ :: _, .cons .absent spec, values => .cons none (embed Value spec values)
  | ty :: _, .cons .present spec, values =>
    let values : Values (Presented Value) ((ty, false) :: carried spec) := values
    match values with
    | .cons value values => .cons (some value) (embed Value spec values)
  | ty :: _, .cons .optional spec, values =>
    let values : Values (Presented Value) ((ty, true) :: carried spec) := values
    match values with
    | .cons value values => .cons value (embed Value spec values)

/-- Every presented position's scope contains the role. -/
def covers : {out : List Ty} → Values (fun _ => Carried) out → Nat → List (List Nat) → Bool
  | [], .nil, _, _ => true
  | _ :: _, .cons .absent spec, role, scopes => covers spec role scopes.tail
  | _ :: _, .cons .present spec, role, scopes => (scopes.headD []).contains role && covers spec role scopes.tail
  | _ :: _, .cons .optional spec, role, scopes => (scopes.headD []).contains role && covers spec role scopes.tail

/-- Masking a presented tuple to scopes that contain the role keeps it: the
role-local embeddings of carried state are fixed points of the state's masks. -/
theorem maskValues_embed {Value : Ty → Type} (context : ProtocolContext) (role : Nat) :
    {out : List Ty} → (spec : Values (fun _ => Carried) out) → (scopes : List (List Nat)) →
      covers spec role scopes = true → (values : Values (Presented Value) (carried spec)) →
        maskValues (context.roles role) (context.mapScopes scopes) (embed Value spec values) =
          embed Value spec values
  | [], .nil, _, _, .nil => rfl
  | _ :: _, .cons .absent spec, scopes, covered, values => by
    simp only [covers] at covered
    have rest := maskValues_embed context role spec scopes.tail covered values
    simp only [embed, maskValues, Participant.restrict]
    rw [show (context.mapScopes scopes).tail = context.mapScopes scopes.tail by
      simp [ProtocolContext.mapScopes, List.map_tail], rest]
    split <;> rfl
  | ty :: _, .cons .present spec, scopes, covered, values => by
    simp only [covers, Bool.and_eq_true] at covered
    have contained : ((context.mapScopes scopes).headD []).contains (context.roles role) = true := by
      cases scopes with
      | nil => simp at covered
      | cons scope rest =>
        simp only [ProtocolContext.mapScopes, List.map_cons, List.headD_cons, List.contains_iff_mem,
          List.mem_map] at covered ⊢
        exact ⟨role, by simpa using covered.1, rfl⟩
    have tail : (context.mapScopes scopes).tail = context.mapScopes scopes.tail := by
      simp [ProtocolContext.mapScopes, List.map_tail]
    have step : ∀ values : Values (Presented Value) ((ty, false) :: carried spec),
        maskValues (context.roles role) (context.mapScopes scopes)
            (embed Value (Values.cons (ty := ty) Carried.present spec) values) =
          embed Value (Values.cons (ty := ty) Carried.present spec) values := by
      intro values
      cases values with
      | cons value values =>
        show Values.cons _ (maskValues _ _ _) = Values.cons _ _
        rw [tail, maskValues_embed context role spec scopes.tail covered.2 values]
        simp only [Participant.restrict, contained, ite_true]
    exact step values
  | ty :: _, .cons .optional spec, scopes, covered, values => by
    simp only [covers, Bool.and_eq_true] at covered
    have contained : ((context.mapScopes scopes).headD []).contains (context.roles role) = true := by
      cases scopes with
      | nil => simp at covered
      | cons scope rest =>
        simp only [ProtocolContext.mapScopes, List.map_cons, List.headD_cons, List.contains_iff_mem,
          List.mem_map] at covered ⊢
        exact ⟨role, by simpa using covered.1, rfl⟩
    have tail : (context.mapScopes scopes).tail = context.mapScopes scopes.tail := by
      simp [ProtocolContext.mapScopes, List.map_tail]
    have step : ∀ values : Values (Presented Value) ((ty, true) :: carried spec),
        maskValues (context.roles role) (context.mapScopes scopes)
            (embed Value (Values.cons (ty := ty) Carried.optional spec) values) =
          embed Value (Values.cons (ty := ty) Carried.optional spec) values := by
      intro values
      cases values with
      | cons value values =>
        show Values.cons _ (maskValues _ _ _) = Values.cons _ _
        rw [tail, maskValues_embed context role spec scopes.tail covered.2 values]
        simp only [Participant.restrict, contained, ite_true]
    exact step values

/-- Whether a returned tuple has the presentation's shape. -/
def shapeMatches {Δ : Scope} : {out : List Ty} → Values (fun _ => Carried) out → Values (Comp laws Δ) out → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons .absent spec, .cons comp comps => comp.isAbsent && shapeMatches spec comps
  | _ :: _, .cons .present spec, .cons comp comps => comp.term?.isSome && shapeMatches spec comps
  | _ :: _, .cons .optional spec, .cons _ comps => shapeMatches spec comps

/-- The presented positions of a returned tuple of the presentation's shape. -/
def presented (results : LawResults model laws) {Δ : Scope} :
    {out : List Ty} → (spec : Values (fun _ => Carried) out) → Values (Comp laws Δ) out → Binders model Δ →
      Option (Values (Presented model.Value) (carried spec))
  | [], .nil, .nil, _ => some .nil
  | _ :: _, .cons .absent spec, .cons _ comps, binders => presented results spec comps binders
  | _ :: _, .cons .present spec, .cons comp comps, binders =>
    match comp.term? with
    | some term => (presented results spec comps binders).map (.cons (term.eval results binders))
    | none => none
  | _ :: _, .cons .optional spec, .cons comp comps, binders =>
    (presented results spec comps binders).map (.cons (comp.eval results binders))

theorem presented_embed (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ) :
    {out : List Ty} → (spec : Values (fun _ => Carried) out) → (comps : Values (Comp laws Δ) out) →
      shapeMatches spec comps = true →
        ∃ values, presented results spec comps binders = some values ∧
          embed model.Value spec values = Comps.eval results comps binders
  | [], .nil, .nil, _ => ⟨.nil, rfl, rfl⟩
  | _ :: _, .cons .absent spec, .cons comp comps, shaped => by
    simp only [shapeMatches, Bool.and_eq_true] at shaped
    obtain ⟨values, found, same⟩ := presented_embed results binders spec comps shaped.2
    refine ⟨values, found, ?_⟩
    cases comp <;> simp [Comp.isAbsent] at shaped
    show Values.cons none (embed model.Value spec values) = Values.cons none (Comps.eval results comps binders)
    rw [same]
  | _ :: _, .cons .present spec, .cons comp comps, shaped => by
    simp only [shapeMatches, Bool.and_eq_true] at shaped
    obtain ⟨values, found, same⟩ := presented_embed results binders spec comps shaped.2
    cases comp <;> simp [Comp.term?] at shaped
    rename_i term
    refine ⟨.cons (term.eval results binders) values, ?_, ?_⟩
    · show Option.map (Values.cons (Value := Presented model.Value) (ty := (_, false)) (term.eval results binders))
        (presented results spec comps binders) = _
      rw [found]
      rfl
    · show Values.cons (some (term.eval results binders)) (embed model.Value spec values) =
        Values.cons (some (term.eval results binders)) (Comps.eval results comps binders)
      rw [same]
  | _ :: _, .cons .optional spec, .cons comp comps, shaped => by
    simp only [shapeMatches] at shaped
    obtain ⟨values, found, same⟩ := presented_embed results binders spec comps shaped
    refine ⟨.cons (comp.eval results binders) values, ?_, ?_⟩
    · show Option.map (Values.cons (Value := Presented model.Value) (ty := (_, true)) (comp.eval results binders))
        (presented results spec comps binders) = _
      rw [found]
      rfl
    · show Values.cons (comp.eval results binders) (embed model.Value spec values) =
        Values.cons (comp.eval results binders) (Comps.eval results comps binders)
      rw [same]

/-- Every returned tuple of the form has the presentation's shape. -/
def Form.finishes {out : List Ty} (spec : Values (fun _ => Carried) out) : {Δ : Scope} → Form laws Δ out → Bool
  | _, .done values => shapeMatches spec values
  | _, .halt _ => true
  | _, .send _ _ _ _ next => next.finishes spec
  | _, .receive _ _ _ next => next.finishes spec
  | _, .query _ _ _ next => next.finishes spec
  | _, .split _ absent present => absent.finishes spec && present.finishes spec
  | _, .guard _ _ _ next => next.finishes spec
  | _, .strict _ _ next => next.finishes spec
  | _, .compute _ _ _ next => next.finishes spec
  | _, .byLaw _ _ next => next.finishes spec

section Finish
variable (model) (tables : Tables model) (results : LawResults model laws) (context : ProtocolContext)

/-- A returned tuple, presented. -/
def finishLeaf {out : List Ty} (spec : Values (fun _ => Carried) out) {Δ : Scope}
    (values : Values (Comp laws Δ) out) (binders : Binders model Δ) :
    PIR.Proc (Interface model) (Tuple model.Value (carried spec)) :=
  match presented results spec values binders with
  | some presentedValues => .done (Tuple.ofValues presentedValues)
  | none => .halt .refused

/-- A form whose returned tuples have the presentation's shape is its presented
process followed by the embedding of the presented tuple. -/
theorem denote_finish {out : List Ty} (spec : Values (fun _ => Carried) out) :
    {Δ : Scope} → (form : Form laws Δ out) → form.finishes spec = true → (binders : Binders model Δ) →
      form.denote model tables results context binders =
        (form.denoteWith model tables results context (finishLeaf model results spec) binders).bind
          fun tuple => .done (embed model.Value spec (Tuple.toValues tuple))
  | _, .done values, finishes, binders => by
    obtain ⟨presentedValues, found, same⟩ := presented_embed results binders spec values finishes
    simp only [Form.denote, Form.denoteWith, finishLeaf, found, PIR.Proc.bind, Tuple.toValues_ofValues, same]
  | _, .halt _, _, _ => rfl
  | _, .send ty site peer value next, finishes, binders => by
    simp only [Form.denote, Form.denoteWith, PIR.Proc.bind]
    exact congrArg (PIR.Proc.call _) (funext fun _ => denote_finish spec next finishes binders)
  | _, .receive ty site peer next, finishes, binders => by
    simp only [Form.denote, Form.denoteWith, PIR.Proc.bind]
    exact congrArg (PIR.Proc.call _) (funext fun reply => denote_finish spec next finishes (.cons reply binders))
  | _, .query site request args next, finishes, binders => by
    simp only [Form.denote, Form.denoteWith, PIR.Proc.bind]
    exact congrArg (PIR.Proc.call _) (funext fun reply => denote_finish spec next finishes (.cons reply binders))
  | _, .split subject absent present, finishes, binders => by
    simp only [Form.finishes, Bool.and_eq_true] at finishes
    simp only [Form.denote, Form.denoteWith]
    cases subject.eval results binders with
    | none => exact denote_finish spec absent finishes.1 binders
    | some value => exact denote_finish spec present finishes.2 (.cons value binders)
  | _, .guard equality left right next, finishes, binders => by
    simp only [Form.denote, Form.denoteWith]
    split
    · exact denote_finish spec next finishes binders
    · rfl
  | _, .strict helper args next, finishes, binders => by
    simp only [Form.denote, Form.denoteWith, PIR.Proc.bind_assoc]
    exact congrArg (PIR.Proc.bind _) (funext fun values => denote_finish spec next finishes (.cons values binders))
  | _, .compute op allowed args next, finishes, binders => by
    simp only [Form.denote, Form.denoteWith, PIR.Proc.bind_assoc]
    exact congrArg (PIR.Proc.bind _) (funext fun values => denote_finish spec next finishes (.cons values binders))
  | _, .byLaw _ _ next, finishes, binders => denote_finish spec next finishes binders

end Finish

/-- A roster of one role: nothing to distinguish. -/
theorem RosterDistinct.only (context : ProtocolContext) : RosterDistinct context 0 1 :=
  fun other bound different => absurd (by omega : other = 0) different

/-! The uniform interpretation. -/

section Uniform
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- `normalize_sound` for the uniform participant meaning. -/
theorem sound_uniform (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (context : ProtocolContext) (distinct : RosterDistinct context role roster)
    (tables : Evaluation.ComponentTables F G (participantInterface F G))
    (protocols : ProtocolTable (assignment F G) (participantInterface F G))
    (results : LawResults (ringModel F G) sig.laws) (binders : Binders (ringModel F G) pattern.scope)
    (inputs : Values (Component (assignment F G)) Γ)
    (environment : pattern.environment (ringModel F G) binders = inputs)
    (lawsHold : LawsHold tables.toOn results inputs) :
    body.denote (participantMeaningWith (.silent _) (participantActions F G) tables (context.roles role)
        protocols context) inputs.get =
      form.denote (ringModel F G) tables.toOn results context binders := by
  subst environment
  rw [denote_participantMeaningWith_eq]
  exact normalize_sound (protocols := protocols) sig body role roster pattern form normalized matched distinct
    results binders lawsHold

/-- A repeat callback's process, factored through the role's presented tuple. -/
theorem callback_sound_uniform (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (spec : Values (fun _ => Carried) out)
    (form : Form sig.laws pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (finishes : form.finishes spec = true)
    (context : ProtocolContext) (distinct : RosterDistinct context role roster)
    (tables : Evaluation.ComponentTables F G (participantInterface F G))
    (protocols : ProtocolTable (assignment F G) (participantInterface F G))
    (results : LawResults (ringModel F G) sig.laws) (binders : Binders (ringModel F G) pattern.scope)
    (inputs : Values (Component (assignment F G)) Γ)
    (environment : pattern.environment (ringModel F G) binders = inputs)
    (lawsHold : LawsHold tables.toOn results inputs) :
    body.denote (participantMeaningWith (.silent _) (participantActions F G) tables (context.roles role)
        protocols context) inputs.get =
      (form.denoteWith (ringModel F G) tables.toOn results context
        (finishLeaf (ringModel F G) results spec) binders).bind
          fun tuple => .done (embed (ringModel F G).Value spec (Tuple.toValues tuple)) :=
  (sound_uniform sig body role roster pattern form normalized matched context distinct tables protocols results
    binders inputs environment lawsHold).trans
      (denote_finish (ringModel F G) tables.toOn results context spec form finishes binders)

/-- An entry's participant at the root context: the normal form of the entry
body, on the masked inputs, followed by the output masks. -/
theorem participant_sound_uniform (program : Program)
    (body : Region protocolDialect program.payload.entry.inputs program.payload.entry.outputs)
    (raw : program.payload.entry.raw = body.erase) (sig : Signature) (role roster : Nat)
    (pattern : InputPattern program.payload.entry.inputs) (form : Form sig.laws pattern.scope program.payload.entry.outputs)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (results : LawResults (ringModel F G) sig.laws) (binders : Binders (ringModel F G) pattern.scope)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs)
    (environment : pattern.environment (ringModel F G) binders =
      maskValues role program.payload.entry.inputScopes inputs)
    (lawsHold : LawsHold (program.payload.definitions.foldl
      (Evaluation.ComponentTables.extend (.silent (participantInterface F G))) ⟨[], []⟩).toOn results
        (maskValues role program.payload.entry.inputScopes inputs)) :
    program.participant F G role inputs =
      (form.denote (ringModel F G) (program.payload.definitions.foldl
        (Evaluation.ComponentTables.extend (.silent (participantInterface F G))) ⟨[], []⟩).toOn results {} binders).bind
          fun out => .done (maskValues role program.payload.entry.outputScopes out) := by
  refine (program.payload.protocolTable_forgetSites (F := F) (G := G) program.payload.entry.signature {} role
    inputs).trans ?_
  refine (protocol_invoke_body_view (.silent _) (participantActions F G)
    (program.payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent (participantInterface F G)))
      ⟨[], []⟩) program.payload.protocols program.payload.protocolsLinked program.payload.entry
    program.payload.entry_mem body raw {} role inputs).trans ?_
  simp only [ProtocolContext.mapScopes_root]
  exact bind_congr_left (sound_uniform sig body role roster pattern form normalized matched {}
    (RosterDistinct.root role roster) _ (program.payload.plainProtocolTable F G) results binders _ environment
    lawsHold) _

end Uniform

end NormalForm
end Zkc.Source.Structured
