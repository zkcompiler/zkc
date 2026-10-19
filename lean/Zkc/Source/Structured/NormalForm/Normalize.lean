module

public import Zkc.Source.Structured.NormalForm.Denote

@[expose] public section

/-! The normalizer: one role's form of a typed protocol body.

It evaluates the body symbolically at the role, following the participant
rules. The symbolic environment holds a component for every variable of the
body's context; the body's inputs are kept beside it, so that a law pinned to
an input can be checked against the call's argument. Every step is structural:
the body by its `next` region, presence splits by a counter bounded by the
operation's arity, and no step unfolds a helper body or a protocol table.

* Presence. Where an operation needs its operands at this role (a calculation
  without an absent operand, an owned call, a send, a draw or a guard of the
  role), the first operand that is an undecided input is split on, and the
  operation is normalized again in both cases. An absent operand decides a
  calculation (absent results), an owned call, a draw or a guard (each stops
  as incomplete) without splitting.
* Roles. Every role index the body names must be below the roster, and the
  normalizer decides `owner = role` on numerals; `RosterDistinct` makes the
  participant rules agree with that decision.
* Refusals. Anything outside the supported fragment is refused with a named
  reason: protocol applications and repeats, Math calls, calculations that can
  stop, undecided guard conditions, laws whose pins do not match, owned calls
  without a law when calls are not kept, and the shared-suffix `bind` form.

* Laws. A law is chosen for an owned call by the called helper's kind,
  inputs and outputs, and by its name only when the signature asks for names.
  The kernel evaluates a string comparison by encoding both strings, which for
  the compiler's long helper names costs more than the rest of a small
  normalization; the form instead records the called helper at the law use
  (`byLaw`), and the instance checks it against the law's helper by
  definitional equality, where two equal literals compare at once.

Normalization never compares names on a hot path. Sorts are compared when a
law is chosen and when a pin is decoded, once per law use. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace NormalForm

variable {laws : List LawKey}

/-! Scope operations. -/

theorem Var.index_heq {α : Type} :
    {Γ : List α} → {a b : α} → (left : Var Γ a) → (right : Var Γ b) → left.index = right.index →
      a = b ∧ HEq left right
  | _, _, _, .here, .here, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .there left, .there right, same => by
    have inner := Var.index_heq left right (by simpa [Var.index] using same)
    obtain ⟨sort, heq⟩ := inner
    subst sort
    cases eq_of_heq heq
    exact ⟨rfl, HEq.rfl⟩
  | _, _, _, .here, .there _, same => by simp [Var.index] at same
  | _, _, _, .there _, .here, same => by simp [Var.index] at same

/-- Compare two variables of one context by position; equal positions have equal sorts. -/
def Var.same? {α : Type} {Γ : List α} {a b : α} (left : Var Γ a) (right : Var Γ b) : Option (PLift (a = b)) :=
  if same : left.index = right.index then some ⟨(Var.index_heq left right same).1⟩ else none

/-- The newest binder, at a sort known to be equal to its own. -/
def Var.hereAs {Δ : Scope} {ty ty₀ : Ty} (same : ty = ty₀) : Var (.value ty₀ :: Δ) (.value ty) := by
  subst same
  exact .here

abbrev Rename (Δ Δ' : Scope) := {slot : Slot} → Var Δ slot → Var Δ' slot

mutual
  def Term.rename {Δ Δ' : Scope} (rename : Rename Δ Δ') {ty : Ty} : Term laws Δ ty → Term laws Δ' ty
    | .var binder => .var (rename binder)
    | .result binder position => .result (rename binder) position
    | .index value => .index value
    | .bool value => .bool value
    | .field domain value => .field domain value
    | .groupZero domain => .groupZero domain
    | .calc op total args position => .calc op total (Terms.rename rename args) position
    | .law entry args position => .law entry (Terms.rename rename args) position

  def Terms.rename {Δ Δ' : Scope} (rename : Rename Δ Δ') {types : List Ty} :
      Terms laws Δ types → Terms laws Δ' types
    | .nil => .nil
    | .cons head tail => .cons (head.rename rename) (Terms.rename rename tail)
end

def Comp.rename {Δ Δ' : Scope} (rename : Rename Δ Δ') {ty : Ty} : Comp laws Δ ty → Comp laws Δ' ty
  | .absent => .absent
  | .present term => .present (term.rename rename)
  | .input binder => .input (rename binder)
  | .read binder position => .read (rename binder) position

/-- Apply a sort-preserving map to every entry. -/
def mapValues {α : Type} {V W : α → Type} (f : {a : α} → V a → W a) :
    {types : List α} → Values V types → Values W types
  | _, .nil => .nil
  | _, .cons head tail => .cons (f head) (mapValues f tail)

/-- Replace the entry at one variable. -/
def setValue {α : Type} {V : α → Type} :
    {types : List α} → {a : α} → Values V types → Var types a → V a → Values V types
  | _, _, values, .here, value => .cons value (laterEntries values)
  | _, _, values, .there position, value => .cons (firstEntry values) (setValue (laterEntries values) position value)

/-- The absent and present cases of an undecided input. -/
def Comp.absentAt {Δ : Scope} {ty₀ : Ty} (subject : Var Δ (.component ty₀)) {ty : Ty} :
    Comp laws Δ ty → Comp laws Δ ty
  | .absent => .absent
  | .present term => .present term
  | .input binder =>
    match Var.same? binder subject with
    | some _ => .absent
    | none => .input binder
  | .read binder position => .read binder position

def Comp.presentAt {Δ : Scope} {ty₀ : Ty} (subject : Var Δ (.component ty₀)) {ty : Ty} :
    Comp laws Δ ty → Comp laws (.value ty₀ :: Δ) ty
  | .absent => .absent
  | .present term => .present (term.rename .there)
  | .input binder =>
    match Var.same? binder subject with
    | some ⟨same⟩ => .present (.var (Var.hereAs (Slot.component.inj same)))
    | none => .input binder.there
  | .read binder position => .read binder.there position

/-! The symbolic state of one body. -/

/-- The body's inputs and the current environment, as components in a scope. -/
structure State (laws : List LawKey) (Γ₀ : List Ty) (Δ : Scope) (Γ : List Ty) where
  inputs : Values (Comp laws Δ) Γ₀
  env : Values (Comp laws Δ) Γ

variable {Γ₀ : List Ty}

def State.map {Δ Δ' : Scope} {Γ : List Ty} (f : {ty : Ty} → Comp laws Δ ty → Comp laws Δ' ty)
    (state : State laws Γ₀ Δ Γ) : State laws Γ₀ Δ' Γ :=
  ⟨mapValues f state.inputs, mapValues f state.env⟩

def State.weaken {Δ : Scope} {Γ : List Ty} (slot : Slot) (state : State laws Γ₀ Δ Γ) :
    State laws Γ₀ (slot :: Δ) Γ :=
  state.map (Comp.rename .there)

def State.push {Δ : Scope} {Γ types : List Ty} (state : State laws Γ₀ Δ Γ)
    (added : Values (Comp laws Δ) types) : State laws Γ₀ Δ (types ++ Γ) :=
  ⟨state.inputs, added.append state.env⟩

def State.set {Δ : Scope} {Γ : List Ty} {ty : Ty} (state : State laws Γ₀ Δ Γ) (position : Var Γ ty)
    (value : Comp laws Δ ty) : State laws Γ₀ Δ Γ :=
  ⟨state.inputs, setValue state.env position value⟩

/-! Operands. -/

def Comp.isAbsent {Δ : Scope} {ty : Ty} : Comp laws Δ ty → Bool
  | .absent => true
  | .present _ => false
  | .input _ => false
  | .read _ _ => false

def Comp.input? {Δ : Scope} {ty : Ty} : Comp laws Δ ty → Option (Σ ty, Var Δ (.component ty))
  | .absent => none
  | .present _ => none
  | .input binder => some ⟨_, binder⟩
  | .read _ _ => none

def Comp.term? {Δ : Scope} {ty : Ty} : Comp laws Δ ty → Option (Term laws Δ ty)
  | .absent => none
  | .present term => some term
  | .input _ => none
  | .read _ _ => none

def anyAbsent {Δ : Scope} : {types : List Ty} → Values (Comp laws Δ) types → Bool
  | _, .nil => false
  | _, .cons head tail => head.isAbsent || anyAbsent tail

def firstInput {Δ : Scope} : {types : List Ty} → Values (Comp laws Δ) types →
    Option (Σ ty, Var Δ (.component ty))
  | _, .nil => none
  | _, .cons head tail =>
    match head.input? with
    | some found => some found
    | none => firstInput tail

def presentTerms {Δ : Scope} : {types : List Ty} → Values (Comp laws Δ) types → Option (Terms laws Δ types)
  | _, .nil => some .nil
  | _, .cons head tail =>
    match head.term?, presentTerms tail with
    | some term, some terms => some (.cons term terms)
    | some _, none => none
    | none, _ => none

def absentComps {Δ : Scope} : (types : List Ty) → Values (Comp laws Δ) types
  | [] => .nil
  | _ :: rest => .cons .absent (absentComps rest)

/-- Whether a request's helper key selects the called helper: by kind, inputs and
outputs, and by name when names are compared. -/
def helperMatches (names : Bool) (key helper : Helper) : Bool :=
  key.kind == helper.kind && key.inputs == helper.inputs && key.outputs == helper.outputs &&
    (!names || key.name == helper.name)

/-- Whether owned calls of the helper are kept as owned invocations. -/
def Signature.keeps (sig : Signature) (helper : Helper) : Bool :=
  sig.kept.any fun key => helperMatches sig.names key helper

/-- Whether the operation needs the presence of its operands at this role. A
calculation that can stop is presented only through a law on components, and a
kept owned call takes its operands as components, so neither demands them. -/
def demanded (sig : Signature) {Δ : Scope} (role : Nat) :
    (op : ProtocolOp) → Values (Comp sig.laws Δ) op.arguments → Bool
  | .calculate op _, operands => op.total && !anyAbsent operands
  | .localCall helper _ owner _, operands => owner == role && !anyAbsent operands && !sig.keeps helper
  | .exchange _ sender _ _, _ => sender == role
  | .draw owner _ _, operands => owner == role && !anyAbsent operands
  | .guard owner _, operands => owner == role && !anyAbsent operands
  | _, _ => false

/-! Calculations, laws and conditions. -/

/-- Constants are literals. -/
def constantResults {Δ : Scope} : (op : Op) → Option (Values (Comp laws Δ) op.results)
  | .fieldConstant domain value => some (.cons (.present (.field domain value)) .nil)
  | .indexConstant value => some (.cons (.present (.index value)) .nil)
  | .booleanConstant value => some (.cons (.present (.bool value)) .nil)
  | .groupIdentity domain => some (.cons (.present (.groupZero domain)) .nil)
  | _ => none

def Term.index? {Δ : Scope} {ty : Ty} : Term laws Δ ty → Option Nat
  | .var _ => none
  | .result .. => none
  | .index value => some value
  | .bool _ => none
  | .field .. => none
  | .groupZero _ => none
  | .calc .. => none
  | .law .. => none

def Term.bool? {Δ : Scope} {ty : Ty} : Term laws Δ ty → Option Bool
  | .var _ => none
  | .result .. => none
  | .index _ => none
  | .bool value => some value
  | .field .. => none
  | .groupZero _ => none
  | .calc .. => none
  | .law .. => none

/-- A Boolean operation on two Boolean literals, folded. -/
def booleanFold {Δ : Scope} (combine : Bool → Bool → Bool) (left right : Term laws Δ .boolean) :
    Option (Values (Comp laws Δ) [.boolean]) :=
  match left.bool? with
  | none => none
  | some first => right.bool?.map fun second => .cons (.present (.bool (combine first second))) .nil

/-- Index equality and Boolean operations on literals are literals. -/
def folded {Δ : Scope} : (op : Op) → Terms laws Δ op.arguments → Option (Values (Comp laws Δ) op.results)
  | .indexEqual => fun
    | .cons left (.cons right .nil) =>
      match left.index? with
      | none => none
      | some first => right.index?.map fun second => .cons (.present (.bool (first == second))) .nil
  | .booleanAnd => fun | .cons left (.cons right .nil) => booleanFold (· && ·) left right
  | .booleanOr => fun | .cons left (.cons right .nil) => booleanFold (· || ·) left right
  | .booleanXor => fun | .cons left (.cons right .nil) => booleanFold xor left right
  | .booleanEqual => fun | .cons left (.cons right .nil) => booleanFold (· == ·) left right
  | .booleanNotEqual => fun | .cons left (.cons right .nil) => booleanFold (· != ·) left right
  | _ => fun _ => none

/-- The results of a total calculation. -/
def calculation {Δ : Scope} (op : Op) (total : op.total = true) (args : Terms laws Δ op.arguments) :
    Values (Comp laws Δ) op.results :=
  (constantResults op).getD ((folded op args).getD
    (mapValues (fun position => .present (.calc op total args position)) (Operands.identity op.results)))

/-- A literal of a sort, as a term. -/
def literalTerm {Δ : Scope} : (ty : Ty) → Nat → Option (Term laws Δ ty)
  | .index, value => some (.index value)
  | .boolean, value => some (.bool (value == 1))
  | .field domain, value => some (.field domain value)
  | .vector _, _ => none
  | .group _, _ => none
  | .service _, _ => none

/-- A returning law's results as components: from its result function, from the
call's arguments, or literals. -/
def lawComps {Δ : Scope} (entry : Fin laws.length) (args : Terms laws Δ laws[entry].helper.inputs) :
    (types : List Ty) → ({ty : Ty} → Var types ty → Var laws[entry].helper.outputs ty) → List LawOutput →
      Option (Values (Comp laws Δ) types)
  | [], _, _ => some .nil
  | ty :: types, position, outputs =>
    let first : Option (Comp laws Δ ty) :=
      match outputs.headD .result with
      | .result => some (.present (.law entry args (position .here)))
      | .argument input => (Var.decode _ ty input).map fun binder => .present (termsAt args binder)
      | .literal value => (literalTerm ty value).map .present
    match first with
    | none => none
    | some comp => (lawComps entry args types (fun binder => position (.there binder)) outputs.tail).map (.cons comp)

/-- The components of a returned tuple bound at the newest binder. -/
def readComps {Δ : Scope} (types : List Ty) : Values (Comp laws (.tuple types :: Δ)) types :=
  mapValues (fun position => .read .here position) (Operands.identity types)

/-- The first law whose helper has the called helper's kind, inputs and
outputs, and its name when `names` is set. The equalities returned are those
the law's terms need; that the law's helper is the called one is checked on the
form (`Form.LawsMatch`). -/
def findLaw (names : Bool) (helper : Helper) :
    (laws : List LawKey) → Option (Σ' entry : Fin laws.length,
      laws[entry].helper.inputs = helper.inputs ∧ laws[entry].helper.outputs = helper.outputs)
  | [] => none
  | key :: rest =>
    if key.helper.kind = helper.kind ∧ (names = false ∨ key.helper.name = helper.name) then
      if same : key.helper.inputs = helper.inputs ∧ key.helper.outputs = helper.outputs then
        some ⟨⟨0, Nat.zero_lt_succ _⟩, same⟩
      else (findLaw names helper rest).map fun found => ⟨found.1.succ, found.2⟩
    else (findLaw names helper rest).map fun found => ⟨found.1.succ, found.2⟩

def Term.var? {Δ : Scope} {ty : Ty} : Term laws Δ ty → Option (Var Δ (.value ty))
  | .var binder => some binder
  | .result .. => none
  | .index _ => none
  | .bool _ => none
  | .field .. => none
  | .groupZero _ => none
  | .calc .. => none
  | .law .. => none

def Term.literal? {Δ : Scope} {ty : Ty} : Term laws Δ ty → Option Nat
  | .var _ => none
  | .result .. => none
  | .index value => some value
  | .bool value => some value.toNat
  | .field _ value => some value
  | .groupZero _ => none
  | .calc .. => none
  | .law .. => none

/-- Syntactic identity of variables and literals; other terms are never identified. -/
def Term.same {Δ : Scope} {ty : Ty} (left right : Term laws Δ ty) : Bool :=
  match left.var?, right.var? with
  | some first, some second => (Var.same? first second).isSome
  | some _, none => false
  | none, some _ => false
  | none, none =>
    match left.literal?, right.literal? with
    | some first, some second => first == second
    | some _, none => false
    | none, _ => false

/-- Whether the call's present arguments are the pinned inputs. -/
def pinsMatch {Δ : Scope} (inputs : Values (Comp laws Δ) Γ₀) :
    {types : List Ty} → List (Option Nat) → Terms laws Δ types → Bool
  | _, _, .nil => true
  | _, [], .cons _ _ => true
  | _, pin :: pins, .cons (ty := ty) term terms =>
    (match pin with
      | none => true
      | some index =>
        match Var.decode Γ₀ ty index with
        | some binder =>
          match entryAt inputs binder with
          | .present pinned => term.same pinned
          | _ => false
        | none => false) && pinsMatch inputs pins terms

/-- The decision of a guard's present condition. -/
inductive Decision (laws : List LawKey) (Δ : Scope) where
  | holds | fails
  | compare {ty : Ty} (equality : Equality ty) (left right : Term laws Δ ty)
  | unknown

def comparison {Δ : Scope} : (op : Op) → Terms laws Δ op.arguments → Decision laws Δ
  | .fieldEqual domain => fun | .cons left (.cons right .nil) => .compare (.field domain) left right
  | .groupEqual domain => fun | .cons left (.cons right .nil) => .compare (.group domain) left right
  | .indexEqual => fun | .cons left (.cons right .nil) => .compare .index left right
  | _ => fun _ => .unknown

def decision {Δ : Scope} : Term laws Δ .boolean → Decision laws Δ
  | .var _ => .unknown
  | .result .. => .unknown
  | .bool value => if value then .holds else .fails
  | .calc op _ args _ => comparison op args
  | .law .. => .unknown

section Normalize
variable {out : List Ty}

/-- A calculation that cannot stop, on resolved operands. -/
def totalCalculation (sig : Signature) {Γ : List Ty} (op : Op) (total : op.total = true)
    (args : Operands Γ op.arguments) {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ)
    (next : {Δ' : Scope} → State sig.laws Γ₀ Δ' (op.results ++ Γ) → Except Refusal (Form sig.laws Δ' out)) :
    Except Refusal (Form sig.laws Δ out) :=
  let operands := lookup state.env args
  if anyAbsent operands then next (state.push (absentComps op.results))
  else
    match presentTerms operands with
    | none => .error "undecided-operand"
    | some terms => next (state.push (calculation op total terms))

/-- A Math call, presented by a passing law on the operands' components. -/
def mathCall (sig : Signature) {Γ : List Ty} (helper : Helper) (args : Operands Γ helper.inputs) {Δ : Scope}
    (state : State sig.laws Γ₀ Δ Γ)
    (next : {Δ' : Scope} → State sig.laws Γ₀ Δ' (helper.outputs ++ Γ) → Except Refusal (Form sig.laws Δ' out)) :
    Except Refusal (Form sig.laws Δ out) :=
  if helper.kind = .math then
    match findLaw sig.names helper sig.laws with
    | some ⟨entry, _, _⟩ =>
      match sig.laws[entry].shape with
      | .passes positions =>
        match passEntries (lookup state.env args) helper.outputs positions with
        | some passed => do
          let rest ← next (state.push passed)
          pure (.byLaw entry helper rest)
        | none => .error "law-positions"
      | .returns _ => .error "calculation-can-stop"
      | .stops _ => .error "calculation-can-stop"
    | none => .error "calculation-can-stop"
  else .error "calculation-can-stop"

/-- A calculation: total ones as terms, Math calls through a passing law. -/
def calculateOperation (sig : Signature) {Γ : List Ty} (op : Op) (args : Operands Γ op.arguments) {Δ : Scope}
    (state : State sig.laws Γ₀ Δ Γ)
    (next : {Δ' : Scope} → State sig.laws Γ₀ Δ' (op.results ++ Γ) → Except Refusal (Form sig.laws Δ' out)) :
    Except Refusal (Form sig.laws Δ out) :=
  if total : op.total = true then totalCalculation sig op total args state next
  else
    match op, args, @next with
    | .invoke helper, args, next => mathCall sig helper args state next
    | _, _, _ => .error "calculation-can-stop"

/-- A call presented by a returning law: its results, then the continuation. -/
def lawReturn (sig : Signature) {Γ : List Ty} (entry : Fin sig.laws.length) (helper : Helper) {Δ : Scope}
    (state : State sig.laws Γ₀ Δ Γ) (lawArgs : Terms sig.laws Δ sig.laws[entry].helper.inputs)
    (outputsSame : sig.laws[entry].helper.outputs = helper.outputs) (outputs : List LawOutput)
    (next : {Δ' : Scope} → State sig.laws Γ₀ Δ' (helper.outputs ++ Γ) → Except Refusal (Form sig.laws Δ' out)) :
    Except Refusal (Form sig.laws Δ out) :=
  match lawComps entry lawArgs _ (fun position => position) outputs with
  | some lawResults => do
    let rest ← next (state.push (outputsSame ▸ lawResults : Values (Comp sig.laws Δ) helper.outputs))
    pure (.byLaw entry helper rest)
  | none => .error "law-outputs"

/-- An owned call at its owner, on present arguments: a law's results or stop,
or the helper's strict invocation. -/
def ownedCall (sig : Signature) {Γ : List Ty} (helper : Helper) {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ)
    (terms : Terms sig.laws Δ helper.inputs)
    (next : {Δ' : Scope} → State sig.laws Γ₀ Δ' (helper.outputs ++ Γ) → Except Refusal (Form sig.laws Δ' out)) :
    Except Refusal (Form sig.laws Δ out) :=
  match findLaw sig.names helper sig.laws with
  | some ⟨entry, inputsSame, outputsSame⟩ =>
    let lawArgs : Terms sig.laws Δ sig.laws[entry].helper.inputs := inputsSame ▸ terms
    if pinsMatch state.inputs sig.laws[entry].pins lawArgs then
      match sig.laws[entry].shape with
      | .returns outputs => lawReturn sig entry helper state lawArgs outputsSame outputs next
      | .stops reason => .ok (.byLaw entry helper (.halt reason))
      | .passes _ => .error "law-shape"
    else .error "law-pins"
  | none =>
    if sig.strict then do
      let rest ← next ((state.weaken (.results helper.outputs)).push
        (mapValues (fun position => .present (.result .here position)) (Operands.identity helper.outputs)))
      pure (.strict helper terms rest)
    else .error "no-law"

/-- One operation on resolved operands, then the continuation on its results. -/
def operation (sig : Signature) (role roster : Nat) {Γ : List Ty} : (op : ProtocolOp) → Operands Γ op.arguments →
    Regions protocolDialect op.regions → {Δ : Scope} → State sig.laws Γ₀ Δ Γ →
    ({Δ' : Scope} → State sig.laws Γ₀ Δ' (op.results ++ Γ) → Except Refusal (Form sig.laws Δ' out)) →
    Except Refusal (Form sig.laws Δ out)
  | .calculate op _, args, _, _, state, next => calculateOperation sig op args state next
  | .localCall helper _ owner _, args, _, _, state, next =>
    if roster ≤ owner then .error "role-outside-roster"
    else if owner != role then next (state.push (absentComps helper.outputs))
    else
      let operands := lookup state.env args
      if anyAbsent operands then .ok (.halt .incomplete)
      else if sig.keeps helper then do
        let rest ← next ((state.weaken (.tuple helper.outputs)).push (readComps helper.outputs))
        pure (.owned owner helper operands rest)
      else
        match presentTerms operands with
        | none => .error "undecided-operand"
        | some terms => ownedCall sig helper state terms next
  | .exchange ty sender receiver site, .cons arg .nil, _, _, state, next =>
    if roster ≤ sender || roster ≤ receiver then .error "role-outside-roster"
    else if sender == role then
      match entryAt state.env arg with
      | .absent => .ok (.halt .incomplete)
      | .present term => do
        let rest ← next (state.push (.cons (.present term) .nil))
        pure (.send ty site receiver term rest)
      | _ => .error "undecided-operand"
    else if receiver == role then do
      let rest ← next ((state.weaken (.value ty)).push (.cons (.present (.var .here)) .nil))
      pure (.receive ty site sender rest)
    else next (state.push (.cons .absent .nil))
  | .restrict _ roles, .cons arg .nil, _, _, state, next =>
    if roles.any (roster ≤ ·) then .error "role-outside-roster"
    else if roles.contains role then next (state.push (.cons (entryAt state.env arg) .nil))
    else next (state.push (.cons .absent .nil))
  | .draw owner field site, .cons arg .nil, _, _, state, next =>
    if roster ≤ owner then .error "role-outside-roster"
    else if owner != role then next (state.push (.cons .absent .nil))
    else
      match entryAt state.env arg with
      | .absent => .ok (.halt .incomplete)
      | .present handle => do
        let rest ← next ((state.weaken (.value (services.result field))).push
          (.cons (.present (.var .here)) .nil))
        pure (.query site field (.cons handle .nil) rest)
      | _ => .error "undecided-operand"
  | .guard owner _, .cons arg .nil, _, _, state, next =>
    if roster ≤ owner then .error "role-outside-roster"
    else if owner != role then next (state.push .nil)
    else
      match entryAt state.env arg with
      | .absent => .ok (.halt .incomplete)
      | .present condition =>
        match decision condition with
        | .holds => next (state.push .nil)
        | .fails => .ok (.halt .reject)
        | .compare equality left right => do
          let rest ← next ((state.set arg (.present (.bool true))).push .nil)
          pure (.guard equality left right rest)
        | .unknown => .error "guard-undecided"
      | _ => .error "undecided-operand"
  | .statement .., _, _, _, state, next => next (state.push .nil)
  | .mark _, _, _, _, state, next => next (state.push .nil)
  | .protocolApply .., _, _, _, _, _ => .error "protocol-application"
  | .repeat spec site, .cons count rest, .cons callback .nil, _, state, next =>
    let parts := Values.split spec.state (lookup state.env rest)
    do
      let after ← next ((state.weaken (.tuple spec.state)).push (readComps spec.state))
      pure (.repeat spec site callback (entryAt state.env count) parts.1 parts.2 after)

/-- Split on the undecided inputs the operation needs, in operand order. -/
def resolve (sig : Signature) (role : Nat) {Γ : List Ty} (op : ProtocolOp) (args : Operands Γ op.arguments) :
    Nat → {Δ : Scope} → State sig.laws Γ₀ Δ Γ →
    ({Δ' : Scope} → State sig.laws Γ₀ Δ' Γ → Except Refusal (Form sig.laws Δ' out)) →
    Except Refusal (Form sig.laws Δ out)
  | 0, _, state, proceed => proceed state
  | fuel + 1, _, state, proceed =>
    if demanded sig role op (lookup state.env args) then
      match firstInput (lookup state.env args) with
      | none => proceed state
      | some ⟨_, subject⟩ => do
        let absent ← resolve sig role op args fuel (state.map (Comp.absentAt subject)) proceed
        let present ← resolve sig role op args fuel (state.map (Comp.presentAt subject)) proceed
        pure (.split (.input subject) absent present)
    else proceed state

def normalizeRegion (sig : Signature) (role roster : Nat) : {Γ : List Ty} → Region protocolDialect Γ out → {Δ : Scope} →
    State sig.laws Γ₀ Δ Γ → Except Refusal (Form sig.laws Δ out)
  | _, .ret values, _, state => .ok (.done (lookup state.env values))
  | _, .stop reason, _, _ => .ok (.halt reason)
  | _, .bind .., _, _ => .error "region-bind"
  | _, .letOp op args bodies next, _, state =>
    resolve sig role op args op.arguments.length state fun state =>
      operation sig role roster op args bodies state fun state => normalizeRegion sig role roster next state

end Normalize

/-! Input patterns. -/

/-- How a role holds one input of the body. -/
inductive Input : Ty → Type where
  | absent {ty : Ty} : Input ty
  | present {ty : Ty} : Input ty
  /-- Present or absent; decided where first needed. -/
  | optional {ty : Ty} : Input ty
  | index (value : Nat) : Input .index
  | field (domain : String) (value : Nat) : Input (.field domain)
  | bool (value : Bool) : Input .boolean

abbrev InputPattern (Γ : List Ty) := Values Input Γ

/-- One binder per present or optional input, in input order. -/
def InputPattern.scope : {Γ : List Ty} → InputPattern Γ → Scope
  | [], .nil => []
  | ty :: _, .cons .present rest => .value ty :: scope rest
  | ty :: _, .cons .optional rest => .component ty :: scope rest
  | _ :: _, .cons .absent rest => scope rest
  | _ :: _, .cons (.index _) rest => scope rest
  | _ :: _, .cons (.field ..) rest => scope rest
  | _ :: _, .cons (.bool _) rest => scope rest

/-- The inputs as components of the pattern's binders, placed in a scope by
`lift`. Each binder is placed once, so the inputs cost one step each rather
than a renaming of every later input. -/
def InputPattern.initialIn {Δ : Scope} : {Γ : List Ty} → (pattern : InputPattern Γ) →
    Rename pattern.scope Δ → Values (Comp laws Δ) Γ
  | [], .nil, _ => .nil
  | ty :: _, .cons .present rest, lift =>
    let lift : Rename (.value ty :: InputPattern.scope rest) Δ := lift
    .cons (.present (.var (lift .here))) (initialIn rest fun binder => lift binder.there)
  | ty :: _, .cons .optional rest, lift =>
    let lift : Rename (.component ty :: InputPattern.scope rest) Δ := lift
    .cons (.input (lift .here)) (initialIn rest fun binder => lift binder.there)
  | _ :: _, .cons .absent rest, lift => .cons .absent (initialIn rest lift)
  | _ :: _, .cons (.index value) rest, lift => .cons (.present (.index value)) (initialIn rest lift)
  | _ :: _, .cons (.field domain value) rest, lift => .cons (.present (.field domain value)) (initialIn rest lift)
  | _ :: _, .cons (.bool value) rest, lift => .cons (.present (.bool value)) (initialIn rest lift)

/-- The inputs as components of the pattern's binders. -/
def InputPattern.initial {Γ : List Ty} (pattern : InputPattern Γ) : Values (Comp laws pattern.scope) Γ :=
  pattern.initialIn fun binder => binder

/-- The inputs the pattern's binders give. -/
def InputPattern.environment (model : DomainModel) : {Γ : List Ty} → (pattern : InputPattern Γ) →
    Binders model pattern.scope → Values (Component model.Value) Γ
  | [], .nil, _ => .nil
  | ty :: _, .cons .present rest, binders =>
    let binders : Values (Slot.Value model) (.value ty :: InputPattern.scope rest) := binders
    match binders with
    | .cons value binders => .cons (some value) (environment model rest binders)
  | ty :: _, .cons .optional rest, binders =>
    let binders : Values (Slot.Value model) (.component ty :: InputPattern.scope rest) := binders
    match binders with
    | .cons value binders => .cons value (environment model rest binders)
  | _ :: _, .cons .absent rest, binders => .cons none (environment model rest binders)
  | _ :: _, .cons (.index value) rest, binders => .cons (some value) (environment model rest binders)
  | _ :: _, .cons (.field domain value) rest, binders =>
    .cons (some (fieldLiteral model.toFieldModel domain value)) (environment model rest binders)
  | _ :: _, .cons (.bool value) rest, binders => .cons (some value) (environment model rest binders)

/-- One role's form of a body, for the inputs the pattern describes. -/
def normalize (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) : Except Refusal (Form sig.laws pattern.scope out) :=
  normalizeRegion sig role roster body ⟨pattern.initial, pattern.initial⟩

end NormalForm
end Zkc.Source.Structured
