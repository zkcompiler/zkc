module

public import Zkc.Source.Structured.NormalForm.Soundness

@[expose] public section

/-! A verified checker of proposed forms: the translation-validation
alternative to computing forms.

An untrusted generator proposes a role's form; `check` walks the body and the
form in lockstep over the same symbolic state the normalizer uses, and accepts
only when every form node is what the body's operation does at the role. The
form chooses where to split on an undecided input: a split on any input is
sound wherever it stands, so the checker validates it locally instead of
recomputing which operation first needs the input. Terms in the form are
compared with the checker's own by a syntactic comparison proved to preserve
evaluation.

This prototype covers the straight-line fragment of root participants:
total calculations, sends, receives, restrictions, draws, marks, statements,
returns and stops, and splits. Guards, helper calls, protocol applications and
repeats are rejected. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace NormalForm

variable {laws : List LawKey}

/-! Syntactic comparison. -/

/-- Equality of total operations, with its proof; other operations are never identified. -/
def Op.sameTotal? : (left right : Op) → Option (PLift (left = right))
  | .indexEqual, .indexEqual => some ⟨rfl⟩
  | .fieldAdd a, .fieldAdd b => if same : a = b then some ⟨same ▸ rfl⟩ else none
  | .fieldSubtract a, .fieldSubtract b => if same : a = b then some ⟨same ▸ rfl⟩ else none
  | .fieldMultiply a, .fieldMultiply b => if same : a = b then some ⟨same ▸ rfl⟩ else none
  | .fieldEqual a, .fieldEqual b => if same : a = b then some ⟨same ▸ rfl⟩ else none
  | .groupAdd a, .groupAdd b => if same : a = b then some ⟨same ▸ rfl⟩ else none
  | .groupEqual a, .groupEqual b => if same : a = b then some ⟨same ▸ rfl⟩ else none
  | .groupScale g f, .groupScale g' f' =>
    if same : g = g' ∧ f = f' then some ⟨by rw [same.1, same.2]⟩ else none
  | .booleanAnd, .booleanAnd => some ⟨rfl⟩
  | .booleanOr, .booleanOr => some ⟨rfl⟩
  | .booleanXor, .booleanXor => some ⟨rfl⟩
  | .booleanEqual, .booleanEqual => some ⟨rfl⟩
  | .booleanNotEqual, .booleanNotEqual => some ⟨rfl⟩
  | _, _ => none

def Term.calc? {Δ : Scope} {ty : Ty} : Term laws Δ ty →
    Option ((op : Op) ×' (op.total = true) ×' Terms laws Δ op.arguments ×' Var op.results ty)
  | .var _ => none
  | .result .. => none
  | .index _ => none
  | .bool _ => none
  | .field .. => none
  | .groupZero _ => none
  | .calc op total args position => some ⟨op, total, args, position⟩
  | .law .. => none

def Term.isGroupZero {Δ : Scope} {ty : Ty} : Term laws Δ ty → Bool
  | .var _ => false
  | .result .. => false
  | .index _ => false
  | .bool _ => false
  | .field .. => false
  | .groupZero _ => true
  | .calc .. => false
  | .law .. => false

mutual
  /-- Syntactic equality of variables, literals and total calculations. -/
  def Term.beq {Δ : Scope} {ty : Ty} : Term laws Δ ty → Term laws Δ ty → Bool
    | .var left, right =>
      match right.var? with
      | some binder => (Var.same? left binder).isSome
      | none => false
    | .result .., _ => false
    | .index value, right => right.literal? == some value
    | .bool value, right => right.literal? == some value.toNat
    | .field _ value, right => right.literal? == some value
    | .groupZero _, right => right.isGroupZero
    | .calc op _ args position, right =>
      match right.calc? with
      | some ⟨op', _, args', position'⟩ =>
        match Op.sameTotal? op' op with
        | some ⟨same⟩ =>
          Terms.beq args (same ▸ args') && (Var.same? position (same ▸ position')).isSome
        | none => false
      | none => false
    | .law .., _ => false

  def Terms.beq {Δ : Scope} : {types : List Ty} → Terms laws Δ types → Terms laws Δ types → Bool
    | [], .nil, .nil => true
    | _ :: _, .cons left lefts, .cons right rights => left.beq right && Terms.beq lefts rights
end

def Comp.beq {Δ : Scope} {ty : Ty} : Comp laws Δ ty → Comp laws Δ ty → Bool
  | .absent, right => right.isAbsent
  | .present term, right =>
    match right.term? with
    | some other => term.beq other
    | none => false
  | .input binder, right =>
    match right.input? with
    | some ⟨_, other⟩ => (Var.same? binder other).isSome
    | none => false
  | .read .., _ => false

def Comps.beq {Δ : Scope} : {types : List Ty} → Values (Comp laws Δ) types → Values (Comp laws Δ) types → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons left lefts, .cons right rights => left.beq right && Comps.beq lefts rights

/-! Form views. -/

section Views
variable {out : List Ty}

def Form.done? {Δ : Scope} : Form laws Δ out → Option (Values (Comp laws Δ) out)
  | .done values => some values
  | .halt _ => none
  | .send .. => none
  | .receive .. => none
  | .query .. => none
  | .split .. => none
  | .guard .. => none
  | .strict .. => none
  | .compute .. => none

def Form.halt? {Δ : Scope} : Form laws Δ out → Option PIR.Stop
  | .done _ => none
  | .halt reason => some reason
  | .send .. => none
  | .receive .. => none
  | .query .. => none
  | .split .. => none
  | .guard .. => none
  | .strict .. => none
  | .compute .. => none

def Form.send? {Δ : Scope} : Form laws Δ out →
    Option ((ty : Ty) × String × Nat × Term laws Δ ty × Form laws Δ out)
  | .done _ => none
  | .halt _ => none
  | .send ty site peer value next => some ⟨ty, site, peer, value, next⟩
  | .receive .. => none
  | .query .. => none
  | .split .. => none
  | .guard .. => none
  | .strict .. => none
  | .compute .. => none

def Form.receive? {Δ : Scope} : Form laws Δ out →
    Option ((ty : Ty) × String × Nat × Form laws (.value ty :: Δ) out)
  | .done _ => none
  | .halt _ => none
  | .send .. => none
  | .receive ty site peer next => some ⟨ty, site, peer, next⟩
  | .query .. => none
  | .split .. => none
  | .guard .. => none
  | .strict .. => none
  | .compute .. => none

def Form.query? {Δ : Scope} : Form laws Δ out →
    Option ((request : services.Op) × String × Terms laws Δ (services.arguments request) ×
      Form laws (.value (services.result request) :: Δ) out)
  | .done _ => none
  | .halt _ => none
  | .send .. => none
  | .receive .. => none
  | .query site request args next => some ⟨request, site, args, next⟩
  | .split .. => none
  | .guard .. => none
  | .strict .. => none
  | .compute .. => none

def Form.split? {Δ : Scope} : Form laws Δ out →
    Option ((ty : Ty) × Var Δ (.component ty) × Form laws Δ out × Form laws (.value ty :: Δ) out)
  | .done _ => none
  | .halt _ => none
  | .send .. => none
  | .receive .. => none
  | .query .. => none
  | .split subject absent present =>
    match subject with
    | .input binder => some ⟨_, binder, absent, present⟩
    | _ => none
  | .guard .. => none
  | .strict .. => none
  | .compute .. => none

end Views

/-! The checker. -/

section Check
variable (sig : Signature) (role roster : Nat) {Γ₀ out : List Ty}

/-- One operation against the proposed form, then the continuation. -/
def checkOperation {Γ : List Ty} : (op : ProtocolOp) → Operands Γ op.arguments → {Δ : Scope} →
    State sig.laws Γ₀ Δ Γ → Form sig.laws Δ out →
    ({Δ' : Scope} → State sig.laws Γ₀ Δ' (op.results ++ Γ) → Form sig.laws Δ' out → Bool) → Bool
  | .calculate op _, args, _, state, form, next =>
    if total : op.total = true then
      let operands := Operands.eval state.env.get args
      if anyAbsent operands then next (state.push (absentComps op.results)) form
      else
        match presentTerms operands with
        | some terms => next (state.push (calculation op total terms)) form
        | none => false
    else false
  | .exchange ty sender receiver site, .cons arg .nil, _, state, form, next =>
    if roster ≤ sender || roster ≤ receiver then false
    else if sender == role then
      match (state.env.get arg).term? with
      | some term =>
        match form.send? with
        | some ⟨ty', site', peer, value, rest⟩ =>
          if same : ty' = ty then
            site' == site && peer == receiver && term.beq (same ▸ value) &&
              next (state.push (.cons (.present term) .nil)) rest
          else false
        | none => false
      | none => (state.env.get arg).isAbsent && form.halt? == some .incomplete
    else if receiver == role then
      match form.receive? with
      | some ⟨ty', site', peer, rest⟩ =>
        if same : ty' = ty then
          site' == site && peer == sender &&
            next ((state.weaken (.value ty)).push (.cons (.present (.var .here)) .nil)) (same ▸ rest)
        else false
      | none => false
    else next (state.push (.cons .absent .nil)) form
  | .restrict _ roles, .cons arg .nil, _, state, form, next =>
    if roles.any (roster ≤ ·) then false
    else if roles.contains role then next (state.push (.cons (state.env.get arg) .nil)) form
    else next (state.push (.cons .absent .nil)) form
  | .draw owner field site, .cons arg .nil, _, state, form, next =>
    if roster ≤ owner then false
    else if owner != role then next (state.push (.cons .absent .nil)) form
    else
      match (state.env.get arg).term? with
      | some handle =>
        match form.query? with
        | some ⟨request, site', args, rest⟩ =>
          match String.decEq request field with
          | isTrue same =>
            site' == site && Terms.beq (same ▸ args) (.cons handle .nil) &&
              next ((state.weaken (.value (services.result field))).push (.cons (.present (.var .here)) .nil))
                (same ▸ rest)
          | isFalse _ => false
        | none => false
      | none => (state.env.get arg).isAbsent && form.halt? == some .incomplete
  | .statement .., _, _, state, form, next => next (state.push .nil) form
  | .mark _, _, _, state, form, next => next (state.push .nil) form
  | .localCall .., _, _, _, _, _ => false
  | .guard .., _, _, _, _, _ => false
  | .protocolApply .., _, _, _, _, _ => false
  | .repeat .., _, _, _, _, _ => false

/-- Splits the form proposes, then the operation in each case. -/
def checkSplits {Γ : List Ty}
    (proceed : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Form sig.laws Δ out → Bool) :
    {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Form sig.laws Δ out → Bool
  | _, state, .split subject absent present =>
    match subject with
    | .input binder =>
      checkSplits proceed (state.map (Comp.absentAt binder)) absent &&
        checkSplits proceed (state.map (Comp.presentAt binder)) present
    | .absent => proceed state (.split .absent absent present)
    | .present term => proceed state (.split (.present term) absent present)
    | .read binder position => proceed state (.split (.read binder position) absent present)
  | _, state, .done values => proceed state (.done values)
  | _, state, .halt reason => proceed state (.halt reason)
  | _, state, .send ty site peer value next => proceed state (.send ty site peer value next)
  | _, state, .receive ty site peer next => proceed state (.receive ty site peer next)
  | _, state, .query site request args next => proceed state (.query site request args next)
  | _, state, .guard equality left right next => proceed state (.guard equality left right next)
  | _, state, .strict helper args next => proceed state (.strict helper args next)
  | _, state, .compute op allowed args next => proceed state (.compute op allowed args next)

def checkRegion : {Γ : List Ty} → Region protocolDialect Γ out → {Δ : Scope} →
    State sig.laws Γ₀ Δ Γ → Form sig.laws Δ out → Bool
  | _, .ret values, _, state, form =>
    match form.done? with
    | some comps => Comps.beq (Operands.eval state.env.get values) comps
    | none => false
  | _, .stop reason, _, _, form => form.halt? == some reason
  | _, .bind .., _, _, _ => false
  | _, .letOp op args _ next, _, state, form =>
    checkSplits sig (fun state form =>
      checkOperation sig role roster op args state form fun state form => checkRegion next state form) state form

/-- Whether a proposed form is the role's form of the body. -/
def check {Γ : List Ty} (body : Region protocolDialect Γ out) (pattern : InputPattern Γ)
    (form : Form sig.laws pattern.scope out) : Bool :=
  checkRegion sig role roster body ⟨pattern.initial, pattern.initial⟩ form

end Check

/-! Soundness of the checker. -/

section Facts
variable {model : DomainModel} (results : LawResults model laws)

theorem term_calc?_eval {Δ : Scope} (binders : Binders model Δ) {ty : Ty} (term : Term laws Δ ty)
    {op : Op} {total : op.total = true} {args : Terms laws Δ op.arguments} {position : Var op.results ty}
    (found : term.calc? = some ⟨op, total, args, position⟩) :
    term.eval results binders = (op.evalTotal model total (Terms.eval results args binders)).get position := by
  cases term <;> simp [Term.calc?] at found
  obtain ⟨rfl, rfl, rfl, rfl⟩ := found
  rfl

mutual
  theorem term_beq_eval {Δ : Scope} (binders : Binders model Δ) :
      {ty : Ty} → (left right : Term laws Δ ty) → left.beq right = true →
        left.eval results binders = right.eval results binders
    | _, .var binder, right, equal => by
      cases found : right.var? with
      | none => simp [Term.beq, found] at equal
      | some other =>
        simp only [Term.beq, found] at equal
        rw [term_var?_eval results binders right other found, var_same?_eq equal]
        rfl
    | _, .result .., _, equal => by simp [Term.beq] at equal
    | _, .index value, right, equal => by
      simp only [Term.beq, beq_iff_eq] at equal
      exact term_literal?_eval results binders _ right value rfl equal
    | _, .bool value, right, equal => by
      simp only [Term.beq, beq_iff_eq] at equal
      exact term_literal?_eval results binders _ right value.toNat rfl equal
    | _, .field _ value, right, equal => by
      simp only [Term.beq, beq_iff_eq] at equal
      exact term_literal?_eval results binders _ right value rfl equal
    | _, .groupZero _, right, equal => by
      simp only [Term.beq] at equal
      cases right <;> simp [Term.isGroupZero] at equal
      rfl
    | _, .calc op total args position, right, equal => by
      cases found : right.calc? with
      | none => simp [Term.beq, found] at equal
      | some view =>
        obtain ⟨op', total', args', position'⟩ := view
        cases same : Op.sameTotal? op' op with
        | none => simp [Term.beq, found, same] at equal
        | some proof =>
          obtain ⟨proof⟩ := proof
          subst op'
          simp only [Term.beq, found, same, Bool.and_eq_true] at equal
          rw [term_calc?_eval results binders right found, var_same?_eq equal.2]
          simp only [Term.eval, terms_beq_eval binders args args' equal.1]
    | _, .law .., _, equal => by simp [Term.beq] at equal

  theorem terms_beq_eval {Δ : Scope} (binders : Binders model Δ) :
      {types : List Ty} → (left right : Terms laws Δ types) → Terms.beq left right = true →
        Terms.eval results left binders = Terms.eval results right binders
    | [], .nil, .nil, _ => rfl
    | _ :: _, .cons left lefts, .cons right rights, equal => by
      simp only [Terms.beq, Bool.and_eq_true] at equal
      simp only [Terms.eval, term_beq_eval binders left right equal.1,
        terms_beq_eval binders lefts rights equal.2]
end

theorem comp_beq_eval {Δ : Scope} (binders : Binders model Δ) {ty : Ty} (left right : Comp laws Δ ty)
    (equal : left.beq right = true) : left.eval results binders = right.eval results binders := by
  cases left with
  | absent => cases right <;> simp [Comp.beq, Comp.isAbsent] at equal; rfl
  | present term =>
    cases right <;> simp [Comp.beq, Comp.term?] at equal
    simp only [Comp.eval, term_beq_eval results binders _ _ equal]
  | input binder =>
    cases right <;> simp [Comp.beq, Comp.input?] at equal
    simp only [Comp.eval, var_same?_eq equal]
  | read _ _ => simp [Comp.beq] at equal

theorem comps_beq_eval {Δ : Scope} (binders : Binders model Δ) :
    {types : List Ty} → (left right : Values (Comp laws Δ) types) → Comps.beq left right = true →
      Comps.eval results left binders = Comps.eval results right binders
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons left lefts, .cons right rights, equal => by
    simp only [Comps.beq, Bool.and_eq_true] at equal
    simp only [Comps.eval, comp_beq_eval results binders left right equal.1,
      comps_beq_eval binders lefts rights equal.2]

end Facts

section Views
variable {out : List Ty} {Δ : Scope}

theorem Form.done?_some {form : Form laws Δ out} {values : Values (Comp laws Δ) out}
    (found : form.done? = some values) : form = .done values := by
  cases form <;> simp [Form.done?] at found
  rw [found]

theorem Form.halt?_some {form : Form laws Δ out} {reason : PIR.Stop}
    (found : form.halt? = some reason) : form = .halt reason := by
  cases form <;> simp [Form.halt?] at found
  rw [found]

theorem Form.send?_some {form : Form laws Δ out} {ty : Ty} {site : String} {peer : Nat}
    {value : Term laws Δ ty} {next : Form laws Δ out}
    (found : form.send? = some ⟨ty, site, peer, value, next⟩) : form = .send ty site peer value next := by
  cases form <;> simp [Form.send?] at found
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := found
  rfl

theorem Form.receive?_some {form : Form laws Δ out} {ty : Ty} {site : String} {peer : Nat}
    {next : Form laws (.value ty :: Δ) out}
    (found : form.receive? = some ⟨ty, site, peer, next⟩) : form = .receive ty site peer next := by
  cases form <;> simp [Form.receive?] at found
  obtain ⟨rfl, rfl, rfl, rfl⟩ := found
  rfl

theorem Form.query?_some {form : Form laws Δ out} {request : services.Op} {site : String}
    {args : Terms laws Δ (services.arguments request)}
    {next : Form laws (.value (services.result request) :: Δ) out}
    (found : form.query? = some ⟨request, site, args, next⟩) : form = .query site request args next := by
  cases form <;> simp [Form.query?] at found
  obtain ⟨rfl, rfl, rfl, rfl⟩ := found
  rfl

end Views

theorem comp_term?_some {Δ : Scope} {ty : Ty} {comp : Comp laws Δ ty} {term : Term laws Δ ty}
    (found : comp.term? = some term) : comp = .present term := by
  cases comp <;> simp [Comp.term?] at found
  rw [found]

theorem comp_isAbsent {Δ : Scope} {ty : Ty} {comp : Comp laws Δ ty} (absent : comp.isAbsent = true) :
    comp = .absent := by
  cases comp <;> simp [Comp.isAbsent] at absent
  rfl

section Main
variable {model : DomainModel} {tables : Tables model}
  {protocols : ProtocolTable model.Value (Interface model)} {context : ProtocolContext}

variable (model tables protocols context) in
/-- Every form a checking step accepts at a state denotes the region's process
at the state's environment, whenever the state's inputs are the body's. -/
def Accepts (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out : List Ty} (inputs : Values (Component model.Value) Γ₀) (region : Region protocolDialect Γ out)
    (accept : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Form sig.laws Δ out → Bool) : Prop :=
  ∀ {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (form : Form sig.laws Δ out), accept state form = true →
    ∀ binders : Binders model Δ, Comps.eval results state.inputs binders = inputs →
      region.denote (meaningAt model tables protocols context role) (Comps.eval results state.env binders).get =
        form.denote model tables results context binders

theorem checkSplits_sound (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out : List Ty} (inputs : Values (Component model.Value) Γ₀) (region : Region protocolDialect Γ out)
    (proceed : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Form sig.laws Δ out → Bool)
    (sound : Accepts model tables protocols context sig results role inputs region proceed) :
    {Δ : Scope} → (state : State sig.laws Γ₀ Δ Γ) → (form : Form sig.laws Δ out) →
      checkSplits sig proceed state form = true → ∀ binders : Binders model Δ,
        Comps.eval results state.inputs binders = inputs →
          region.denote (meaningAt model tables protocols context role) (Comps.eval results state.env binders).get =
            form.denote model tables results context binders
  | _, state, .split (.input subject) absent present, accepted, binders, inputsEq => by
    simp only [checkSplits, Bool.and_eq_true] at accepted
    simp only [Form.denote, Form.denoteWith, Comp.eval]
    cases value : binders.get subject with
    | none =>
      have preserved := state_map_eval results (Comp.absentAt subject) binders binders
        (comp_eval_absentAt results subject binders value) state
      have step := checkSplits_sound sig results role inputs region proceed sound _ absent accepted.1 binders
        (preserved.1.trans inputsEq)
      rw [preserved.2] at step
      exact step
    | some present' =>
      have preserved := state_map_eval results (Comp.presentAt subject) binders (.cons present' binders)
        (comp_eval_presentAt results subject present' binders value) state
      have step := checkSplits_sound sig results role inputs region proceed sound _ present accepted.2
        (.cons present' binders) (preserved.1.trans inputsEq)
      rw [preserved.2] at step
      exact step
  | _, state, .split .absent absent present, accepted, binders, inputsEq =>
    sound state _ accepted binders inputsEq
  | _, state, .split (.present term) absent present, accepted, binders, inputsEq =>
    sound state _ accepted binders inputsEq
  | _, state, .split (.read binder position) absent present, accepted, binders, inputsEq =>
    sound state _ accepted binders inputsEq
  | _, state, .done _, accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .halt _, accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .send .., accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .receive .., accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .query .., accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .guard .., accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .strict .., accepted, binders, inputsEq => sound state _ accepted binders inputsEq
  | _, state, .compute .., accepted, binders, inputsEq => sound state _ accepted binders inputsEq

theorem continue_accept (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out types : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (nextRegion : Region protocolDialect (types ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (types ++ Γ) → Form sig.laws Δ out → Bool)
    (sound : Accepts model tables protocols context sig results role inputs nextRegion next)
    {Δ Δ' : Scope} (state : State sig.laws Γ₀ Δ Γ) (state' : State sig.laws Γ₀ Δ' (types ++ Γ))
    (form : Form sig.laws Δ' out) (accepted : next state' form = true) (binders : Binders model Δ)
    (binders' : Binders model Δ') (inputsEq : Comps.eval results state'.inputs binders' = inputs)
    (values : Values (Component model.Value) types)
    (evaluated : Comps.eval results state'.env binders' = values.append (Comps.eval results state.env binders)) :
    nextRegion.denote (meaningAt model tables protocols context role)
        (values.append (Comps.eval results state.env binders)).get =
      form.denote model tables results context binders' := by
  rw [← evaluated]
  exact sound state' form accepted binders' inputsEq

theorem continue_accept_weaken (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out types : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (nextRegion : Region protocolDialect (types ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (types ++ Γ) → Form sig.laws Δ out → Bool)
    (sound : Accepts model tables protocols context sig results role inputs nextRegion next)
    {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (slot : Slot) (value : Slot.Value model slot)
    (added : Values (Comp sig.laws (slot :: Δ)) types) (form : Form sig.laws (slot :: Δ) out)
    (accepted : next ((state.weaken slot).push added) form = true) (binders : Binders model Δ)
    (inputsEq : Comps.eval results state.inputs binders = inputs) (values : Values (Component model.Value) types)
    (evaluated : Comps.eval results added (.cons value binders) = values) :
    nextRegion.denote (meaningAt model tables protocols context role)
        (values.append (Comps.eval results state.env binders)).get =
      form.denote model tables results context (.cons value binders) := by
  have preserved := state_map_eval results (Comp.rename .there) binders (.cons value binders)
    (comp_eval_weaken results value binders) state
  have step := sound ((state.weaken slot).push added) form accepted (.cons value binders)
    (preserved.1.trans inputsEq)
  simp only [State.push, comps_eval_append, evaluated] at step
  rw [State.weaken, preserved.2] at step
  exact step

theorem checkOperation_sound (sig : Signature) (results : LawResults model sig.laws) (role roster : Nat)
    (distinct : RosterDistinct context role roster) {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀)
    {Γ out : List Ty} (op : ProtocolOp)
    (args : Operands Γ op.arguments) (bodies : Regions protocolDialect op.regions)
    (nextRegion : Region protocolDialect (op.results ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (op.results ++ Γ) → Form sig.laws Δ out → Bool)
    (sound : Accepts model tables protocols context sig results role inputs nextRegion next) :
    Accepts model tables protocols context sig results role inputs (.letOp op args bodies nextRegion)
      (fun state form => checkOperation sig role roster op args state form next) := by
  intro Δ state form accepted binders inputsEq
  rw [Region.denote_letOp_values]
  change (protocolOperationWithOn model (.silent _) (participantActionsOn model.toCarriers) tables
    (context.roles role) op (Operands.eval (Comps.eval results state.env binders).get args)
    (bodies.denote (meaningAt model tables protocols context role)) protocols context).bind _ = _
  rw [← comps_eval_operands]
  cases op with
  | calculate op allowed =>
    simp only [checkOperation] at accepted
    split at accepted
    · rename_i total
      split at accepted
      · rename_i absent
        refine (bind_congr_left (calculate_absent model tables protocols context _ op allowed total _ _
          (anyAbsent_sequence results binders _ absent)) _).trans ?_
        exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
          binders binders inputsEq _ ((comps_eval_append results binders (absentComps op.results) state.env).trans
            (congrArg (fun values => Values.append values (Comps.eval results state.env binders))
              (comps_eval_absent results binders op.results)))
      · split at accepted
        · rename_i terms found
          rw [presentTerms_eval results binders _ terms found]
          refine (bind_congr_left (calculate_present model tables protocols context _ op allowed total _ _) _).trans ?_
          exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
            binders binders inputsEq _ ((comps_eval_append results binders (calculation op total terms) state.env).trans
              (congrArg (fun values => Values.append values (Comps.eval results state.env binders))
                (calculation_eval results binders op total terms)))
        · cases accepted
    · cases accepted
  | exchange ty sender receiver site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [checkOperation] at accepted
    split at accepted
    · cases accepted
    · rename_i bounded
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at bounded
      refine (bind_congr_left (exchange_rule model tables protocols context _ ty sender receiver site _ _) _).trans ?_
      rw [interpret_plain]
      split at accepted
      · rename_i isSender
        have same : sender = role := by simpa using isSender
        subst same
        split at accepted
        · rename_i term stored
          split at accepted
          · rename_i ty' site' peer value rest sent
            split at accepted
            · rename_i sameType
              subst sameType
              simp only [Bool.and_eq_true, beq_iff_eq] at accepted
              obtain ⟨⟨⟨siteEq, peerEq⟩, valueEq⟩, restAccepted⟩ := accepted
              subst siteEq peerEq
              rw [Form.send?_some sent]
              simp only [comp_term?_some stored]
              simp only [Participant.exchange, ite_true, Comp.eval, PIR.Proc.bind, Form.denote,
                Form.denoteWith, term_beq_eval results binders _ _ valueEq]
              refine congrArg (PIR.Proc.call _) (funext fun _ => ?_)
              exact continue_accept sig results _ inputs nextRegion next sound state (state.push _) rest
                restAccepted binders binders inputsEq _
                (congrArg (fun x => Values.append (Values.cons (Value := Component model.Value) (some x) Values.nil)
                  (Comps.eval results state.env binders)) (term_beq_eval results binders _ _ valueEq))
            · cases accepted
          · cases accepted
        · rename_i noTerm
          simp only [Bool.and_eq_true, beq_iff_eq] at accepted
          rw [Form.halt?_some accepted.2]
          simp only [comp_isAbsent accepted.1]
          simp [Participant.exchange, Comp.eval, PIR.Proc.bind, Form.denote, Form.denoteWith]
      · rename_i notSender
        have different : context.roles sender ≠ context.roles role :=
          distinct sender bounded.1 (by simpa using notSender)
        split at accepted
        · rename_i isReceiver
          have same : receiver = role := by simpa using isReceiver
          subst same
          split at accepted
          · rename_i ty' site' peer rest received
            split at accepted
            · rename_i sameType
              subst sameType
              simp only [Bool.and_eq_true, beq_iff_eq] at accepted
              obtain ⟨⟨siteEq, peerEq⟩, restAccepted⟩ := accepted
              subst siteEq peerEq
              rw [Form.receive?_some received]
              simp only [Participant.exchange, different, ite_false, ite_true, PIR.Proc.bind, Form.denote,
                Form.denoteWith]
              refine congrArg (PIR.Proc.call _) (funext fun reply => ?_)
              exact continue_accept_weaken sig results _ inputs nextRegion next sound state _ reply _ rest
                restAccepted binders inputsEq _ rfl
            · cases accepted
          · cases accepted
        · rename_i notReceiver
          have otherReceiver : context.roles receiver ≠ context.roles role :=
            distinct receiver bounded.2 (by simpa using notReceiver)
          simp only [Participant.exchange, different, otherReceiver, ite_false, PIR.Proc.bind]
          exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
            binders binders inputsEq _ (by simp only [State.push]; rfl)
  | restrict ty roles =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [checkOperation] at accepted
    split at accepted
    · cases accepted
    · rename_i bounded
      have contains := restrict_contains distinct roles (by simpa using bounded)
      refine (bind_congr_left (restrict_rule model tables protocols context _ ty roles _ _) _).trans ?_
      simp only [contains, PIR.Proc.bind]
      split at accepted
      · rename_i member
        simp only [member, Participant.restrict, ite_true]
        exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
          binders binders inputsEq _ (by simp only [State.push]; rfl)
      · rename_i notMember
        simp only [Participant.restrict, Bool.not_eq_true] at notMember ⊢
        simp only [notMember, Bool.false_eq_true, ite_false]
        exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
          binders binders inputsEq _ (by simp only [State.push]; rfl)
  | draw owner field site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [checkOperation] at accepted
    split at accepted
    · cases accepted
    · rename_i bounded
      refine (bind_congr_left (draw_rule model tables protocols context _ owner field site _ _) _).trans ?_
      rw [interpret_plain]
      split at accepted
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        simp only [Participant.query, different, ite_false, PIR.Proc.bind]
        exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
          binders binders inputsEq _ (by simp only [State.push]; rfl)
      · rename_i own
        have same : owner = role := by simpa using own
        subst same
        split at accepted
        · rename_i handle stored
          split at accepted
          · rename_i request site' args rest queried
            split at accepted
            · rename_i sameRequest _
              subst sameRequest
              simp only [Bool.and_eq_true, beq_iff_eq] at accepted
              obtain ⟨⟨siteEq, argsEq⟩, restAccepted⟩ := accepted
              subst siteEq
              have argsEval : Terms.eval results args binders = .cons (handle.eval results binders) .nil :=
                terms_beq_eval results binders _ _ argsEq
              have stored' := comp_term?_some stored
              rw [Form.query?_some queried]
              simp only [Form.denote, Form.denoteWith]
              rw [argsEval]
              simp only [Participant.query, ite_true, Operands.eval, stored']
              refine congrArg (PIR.Proc.call _) (funext fun reply => ?_)
              exact continue_accept_weaken sig results _ inputs nextRegion next sound state _ reply _ rest
                restAccepted binders inputsEq _ rfl
            · cases accepted
          · cases accepted
        · rename_i noTerm
          simp only [Bool.and_eq_true, beq_iff_eq] at accepted
          rw [Form.halt?_some accepted.2]
          have absent := comp_isAbsent accepted.1
          simp only [Participant.query, ite_true, Operands.eval, absent]
          rfl
  | statement relation types selectors acceptance =>
    simp only [checkOperation] at accepted
    refine (bind_congr_left (statement_rule model tables protocols context _ relation types selectors acceptance
      _ _) _).trans ?_
    exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
      binders binders inputsEq _ (by simp only [State.push]; rfl)
  | mark site =>
    rcases args with _ | _
    simp only [checkOperation] at accepted
    refine (bind_congr_left (mark_rule model tables protocols context _ site _) _).trans ?_
    exact continue_accept sig results role inputs nextRegion next sound state (state.push _) form accepted
      binders binders inputsEq _ (by simp only [State.push]; rfl)
  | localCall => simp only [checkOperation] at accepted; cases accepted
  | guard => simp only [checkOperation] at accepted; cases accepted
  | protocolApply => simp only [checkOperation] at accepted; cases accepted
  | «repeat» => simp only [checkOperation] at accepted; cases accepted

theorem checkRegion_sound (sig : Signature) (results : LawResults model sig.laws) (role roster : Nat)
    (distinct : RosterDistinct context role roster) {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀)
    {out : List Ty} :
    {Γ : List Ty} → (region : Region protocolDialect Γ out) →
      Accepts model tables protocols context sig results role inputs region
        (fun state form => checkRegion sig role roster region state form)
  | _, .ret values => by
    intro state form accepted binders _
    simp only [checkRegion] at accepted
    split at accepted
    · rename_i comps found
      rw [Form.done?_some found]
      simp only [Region.denote, Form.denote, Form.denoteWith, ← comps_eval_operands,
        comps_beq_eval results binders _ _ accepted]
    · cases accepted
  | _, .stop reason => by
    intro state form accepted binders _
    simp only [checkRegion, beq_iff_eq] at accepted
    rw [Form.halt?_some accepted]
    rfl
  | _, .letOp op args bodies next => by
    intro state form accepted binders inputsEq
    exact checkSplits_sound sig results role inputs (.letOp op args bodies next) _
      (checkOperation_sound sig results role roster distinct inputs op args bodies next _
        (checkRegion_sound sig results role roster distinct inputs next))
      state form accepted binders inputsEq
  | _, .bind body next => by
    intro state form accepted
    simp [checkRegion] at accepted

/-- **Soundness of the checker.** An accepted form is the role's form of the
body: the same conclusion as `normalize_sound`, with the same premises. -/
theorem check_sound (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws pattern.scope out)
    (checked : check sig role roster body pattern form = true)
    (distinct : RosterDistinct context role roster) (results : LawResults model sig.laws)
    (binders : Binders model pattern.scope) :
    body.denote (meaningAt model tables protocols context role) (pattern.environment model binders).get =
      form.denote model tables results context binders := by
  have initial := initial_eval (laws := sig.laws) results pattern binders
  have sound := checkRegion_sound (tables := tables) (protocols := protocols) sig results role roster distinct
    (pattern.environment model binders) body ⟨pattern.initial, pattern.initial⟩ form checked binders initial
  rw [initial] at sound
  exact sound

end Main

end NormalForm
end Zkc.Source.Structured
