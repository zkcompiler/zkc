module

public import Zkc.Source.Structured.DomainParticipant

@[expose] public section

/-! Participant normal forms as data.

A form is the process one role runs for a typed protocol body: its ordered
actions, the values it computes on the way, its decided conditions and the
places where a missing input stops it. Forms are indexed by a scope of typed
binders, newest first, so a form term is well scoped and well typed by
construction. Values computed from binders are terms; inputs whose presence is
decided where an operation first needs them are components.

* A query binds the reply sort its service request declares (`services.result`),
  so a service whose reply sort depends on the request is presented as it is.
* A calculation enters the total term language only with a witness that its
  meaning returns for every argument (`Op.total`). A calculation that can stop
  is a separate node that binds its results after the stop has been decided.
* A helper call is presented through a law of the signature (a returned
  result or a stop) or kept as the helper's own invocation on present
  arguments. Math calls can instead retain their exact invocation on optional
  components, without a helper law. A law names its helper; the soundness theorem asks for one
  premise per law, so every presented call is tied to the admitted helper it
  is about. The form records the called helper wherever a law presents a call
  (`byLaw`), and the soundness theorem asks that it be the law's own helper:
  an instance checks this by definitional equality of the two helper terms,
  never by comparing helper names in the kernel's evaluator.

The normalizer (`Normalize`) computes forms from bodies, the denotation
(`Denote`) gives them their participant meaning, and `Soundness` proves the
two agree. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- Calculations whose meaning returns for every argument: constants, ring and
group arithmetic, comparisons, Boolean connectives and selection. Primitive
executions, bounded reads, helper calls, folds and maps can stop or depend on
helper bodies and are excluded. -/
def Op.total : Op → Bool
  | .makeProduct .. | .getProduct .. => true
  | .indexConstant .. | .indexEqual | .indexLess | .indexPowerOfTwo | .vectorLength .. | .multilinearRestrictPrefix .. |
    .fieldConstant .. | .fieldAdd .. | .fieldSubtract ..
  | .fieldMultiply .. | .fieldEmbed .. | .fieldEqual .. | .groupIdentity .. | .groupAdd .. | .groupScale ..
  | .groupEqual .. | .booleanConstant .. | .booleanAnd | .booleanOr | .booleanXor
  | .booleanEqual | .booleanNotEqual | .select .. => true
  | _ => false

namespace NormalForm

/-! Access for the kernel's evaluator.

The kernel evaluates a match whose patterns fix an index of an indexed family
through casts it checks at every step. The functions the normalizer evaluates
match one discriminant at a time with its indices left as variables, and take
the parts of a tuple of known length by eliminating into a sort computed from
the index, so each step is a plain reduction. -/

/-- The first entry of a nonempty tuple. -/
def firstEntry {α : Type} {V : α → Type} {a : α} {types : List α} (values : Values V (a :: types)) : V a :=
  Values.casesOn (motive := fun index _ => match index with | [] => PUnit | head :: _ => V head) values
    PUnit.unit fun head _ => head

/-- The entries after the first. -/
def laterEntries {α : Type} {V : α → Type} {a : α} {types : List α} (values : Values V (a :: types)) :
    Values V types :=
  Values.casesOn (motive := fun index _ => match index with | [] => PUnit | _ :: tail => Values V tail) values
    PUnit.unit fun _ tail => tail

/-- The entry at a variable. -/
def entryAt {α : Type} {V : α → Type} : {types : List α} → {a : α} → Values V types → Var types a → V a
  | _, _, values, .here => firstEntry values
  | _, _, values, .there position => entryAt (laterEntries values) position

/-- The entries at operand variables. -/
def lookup {α : Type} {V : α → Type} {Γ : List α} (values : Values V Γ) :
    {types : List α} → Values (Var Γ) types → Values V types
  | _, .nil => .nil
  | _, .cons position rest => .cons (entryAt values position) (lookup values rest)

@[simp] theorem firstEntry_cons {α : Type} {V : α → Type} {a : α} {types : List α} (head : V a)
    (tail : Values V types) : firstEntry (.cons head tail) = head := rfl

@[simp] theorem laterEntries_cons {α : Type} {V : α → Type} {a : α} {types : List α} (head : V a)
    (tail : Values V types) : laterEntries (.cons head tail) = tail := rfl

theorem entryAt_eq_get {α : Type} {V : α → Type} :
    {types : List α} → {a : α} → (values : Values V types) → (position : Var types a) →
      entryAt values position = values.get position
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons _ tail, .there position => entryAt_eq_get tail position

theorem lookup_eq_eval {α : Type} {V : α → Type} {Γ : List α} (values : Values V Γ) :
    {types : List α} → (operands : Values (Var Γ) types) → lookup values operands = Operands.eval values.get operands
  | _, .nil => rfl
  | _, .cons position rest => by
    simp only [lookup, Operands.eval, entryAt_eq_get, lookup_eq_eval values rest]

/-- The entries at input positions, one per output sort; `none` if a position
is out of range or holds another sort. -/
def passEntries {V : Ty → Type} {inputs : List Ty} (values : Values V inputs) :
    (outputs : List Ty) → List Nat → Option (Values V outputs)
  | [], _ => some .nil
  | _ :: _, [] => none
  | ty :: outputs, position :: positions =>
    match Var.decode inputs ty position with
    | none => none
    | some binder => (passEntries values outputs positions).map (.cons (entryAt values binder))

/-- A binder of a form's scope. -/
inductive Slot where
  /-- A present value: a present input, a received or drawn value, the present
  case of a split. -/
  | value (ty : Ty)
  /-- An input whose presence the form decides where it is first needed. -/
  | component (ty : Ty)
  /-- The present results of a kept helper call or of a calculation that can stop. -/
  | results (types : List Ty)
  /-- A returned tuple of components. -/
  | tuple (types : List Ty)
  deriving DecidableEq, Repr

abbrev Scope := List Slot

/-! Input patterns. -/

/-- How a role holds one input of the body. -/
inductive Input : Ty → Type where
  | absent {ty : Ty} : Input ty
  | present {ty : Ty} : Input ty
  /-- Present or absent; decided where first needed. -/
  | optional {ty : Ty} : Input ty
  /-- A service handle fixed by the input ABI, not a physical data cell. -/
  | capability (service : String) (handle : Nat) : Input (.service service)
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
  | _ :: _, .cons (.capability ..) rest => scope rest
  | _ :: _, .cons (.index _) rest => scope rest
  | _ :: _, .cons (.field ..) rest => scope rest
  | _ :: _, .cons (.bool _) rest => scope rest

/-- One result of a law that returns. -/
inductive LawOutput where
  /-- The law's result function gives it. -/
  | result
  /-- It is the call's argument at this input position. -/
  | argument (position : Nat)
  /-- It is this literal: an index, a Boolean (`1` is true) or the natural of a
  field element. -/
  | literal (value : Nat)
  deriving DecidableEq, Repr

/-- What a law says about its helper on the arguments it covers. -/
inductive LawShape where
  /-- The helper returns, per output, what the list says; missing entries are
  the law's result function. -/
  | returns (outputs : List LawOutput)
  /-- The helper stops with this reason. -/
  | stops (reason : PIR.Stop)
  /-- A Math helper returns, on components, the arguments' components at these
  input positions, one per output, whether present or not. -/
  | passes (positions : List Nat)
  deriving DecidableEq, Repr

/-- What a law asks of one argument of the calls it covers. -/
inductive LawPin where
  /-- Any argument. -/
  | free
  /-- The body's input at this position, which must be present. -/
  | input (position : Nat)
  /-- This literal of the argument's sort. -/
  | literal (value : Nat)
  deriving DecidableEq, Repr

/-- A helper law, keyed by the helper, never by an occurrence. `pins` follows
the helper's inputs and restricts the law to the calls whose arguments they
describe; a missing entry is free. -/
structure LawKey where
  helper : Helper
  shape : LawShape
  pins : List LawPin := []
  deriving DecidableEq, Repr

/-- A protocol a body may apply, keyed by its signature: the callee role this
participant plays, how it holds the callee's inputs, and the caller inputs some
of the callee's binders are pinned to (`some k`), when the callee's equation
holds only there. -/
structure CalleeKey where
  signature : ProtocolSignature
  role : Nat
  pattern : InputPattern signature.inputs
  pins : List (Option Nat) := []

/-- The callee at an index. -/
def calleeAt (callees : List CalleeKey) (callee : Fin callees.length) : CalleeKey := callees[callee]

/-- The part of a request the normalizer reads. -/
structure Signature where
  laws : List LawKey := []
  /-- Owned calls of the role's own helpers without a law are kept as the
  helper's invocation on present arguments (`true`) or refused (`false`). -/
  strict : Bool := false
  /-- A law is chosen for a call by the called helper's kind, inputs and
  outputs; with `names`, also by its name. Choosing never affects soundness,
  because every law use is checked against the law's helper (`byLaw`); names
  are needed only where two helpers of one signature meet in a body. -/
  names : Bool := false
  /-- Owned calls of these helpers are kept as the helper's owned invocation on
  the arguments' components, without deciding their presence. -/
  kept : List Helper := []
  /-- The protocols the body may apply, with the callee forms that present them. -/
  callees : List CalleeKey := []

/-- The decidable equalities a guard can compare. -/
inductive Equality : Ty → Type where
  | field (domain : String) : Equality (.field domain)
  | group (domain : String) : Equality (.group domain)
  | index : Equality .index
  | boolean : Equality .boolean
  deriving Repr

mutual
  /-- Present values in a scope. -/
  inductive Term (laws : List LawKey) (Δ : Scope) : Ty → Type where
    | var {ty : Ty} (binder : Var Δ (.value ty)) : Term laws Δ ty
    | result {types : List Ty} {ty : Ty} (binder : Var Δ (.results types)) (position : Var types ty) :
        Term laws Δ ty
    /-- The nominal service capability selected by the source input ABI. -/
    | capability (service : String) (handle : Nat) : Term laws Δ (.service service)
    | index (value : Nat) : Term laws Δ .index
    | bool (value : Bool) : Term laws Δ .boolean
    /-- A field literal, presented as `0`, `1` or the cast of the natural. -/
    | field (domain : String) (value : Nat) : Term laws Δ (.field domain)
    | groupZero (domain : String) : Term laws Δ (.group domain)
    | calc {ty : Ty} (op : Op) (total : op.total = true) (args : Terms laws Δ op.arguments)
        (position : Var op.results ty) : Term laws Δ ty
    | law {ty : Ty} (entry : Fin laws.length) (args : Terms laws Δ laws[entry].helper.inputs)
        (position : Var laws[entry].helper.outputs ty) : Term laws Δ ty

  inductive Terms (laws : List LawKey) (Δ : Scope) : List Ty → Type where
    | nil : Terms laws Δ []
    | cons {ty : Ty} {types : List Ty} (head : Term laws Δ ty) (tail : Terms laws Δ types) :
        Terms laws Δ (ty :: types)
end

/-- The term at a position of a tuple of terms. -/
def termsAt {laws : List LawKey} {Δ : Scope} : {types : List Ty} → {ty : Ty} → Terms laws Δ types → Var types ty →
    Term laws Δ ty
  | _, _, .cons head _, .here => head
  | _, _, .cons _ tail, .there position => termsAt tail position

/-- Optional components in a scope. -/
inductive Comp (laws : List LawKey) (Δ : Scope) (ty : Ty) where
  | absent
  | present (term : Term laws Δ ty)
  | input (binder : Var Δ (.component ty))
  | read {types : List Ty} (binder : Var Δ (.tuple types)) (position : Var types ty)

/-- A callee's argument for one of its binders: a present value or a component. -/
abbrev Argument (laws : List LawKey) (Δ : Scope) : Slot → Type
  | .value ty => Term laws Δ ty
  | .component ty => Comp laws Δ ty
  | .results types => Terms laws Δ types
  | .tuple types => Values (Comp laws Δ) types

/-- One role's process for a body. -/
inductive Form (laws : List LawKey) (callees : List CalleeKey) : Scope → List Ty → Type where
  | done {Δ : Scope} {out : List Ty} (values : Values (Comp laws Δ) out) : Form laws callees Δ out
  | halt {Δ : Scope} {out : List Ty} (reason : PIR.Stop) : Form laws callees Δ out
  | send {Δ : Scope} {out : List Ty} (ty : Ty) (site : String) (peer : Nat)
      (value : Term laws Δ ty) (next : Form laws callees Δ out) : Form laws callees Δ out
  | receive {Δ : Scope} {out : List Ty} (ty : Ty) (site : String) (peer : Nat)
      (next : Form laws callees (.value ty :: Δ) out) : Form laws callees Δ out
  /-- A service request; the reply has the sort the request declares. -/
  | query {Δ : Scope} {out : List Ty} (site : String) (request : services.Op)
      (args : Terms laws Δ (services.arguments request))
      (next : Form laws callees (.value (services.result request) :: Δ) out) : Form laws callees Δ out
  /-- The absent and present cases of a component. -/
  | split {Δ : Scope} {out : List Ty} {ty : Ty} (subject : Comp laws Δ ty)
      (absent : Form laws callees Δ out) (present : Form laws callees (.value ty :: Δ) out) : Form laws callees Δ out
  /-- Continue when the two values are equal; otherwise reject. -/
  | guard {Δ : Scope} {out : List Ty} {ty : Ty} (equality : Equality ty)
      (left right : Term laws Δ ty) (next : Form laws callees Δ out) : Form laws callees Δ out
  /-- A kept helper call on present arguments: its effects and stops, then its
  present results. -/
  | strict {Δ : Scope} {out : List Ty} (helper : Helper) (args : Terms laws Δ helper.inputs)
      (next : Form laws callees (.results helper.outputs :: Δ) out) : Form laws callees Δ out
  /-- A calculation that can stop, on present arguments: its stop, or its
  present results. -/
  | compute {Δ : Scope} {out : List Ty} (op : Op) (allowed : op.isCalculation = true)
      (args : Terms laws Δ op.arguments)
      (next : Form laws callees (.results op.results :: Δ) out) : Form laws callees Δ out
  /-- An exact Math helper invocation on optional inputs. The returned tuple
  retains optional results; the invocation retains every effect and stop. -/
  | math {Δ : Scope} {out : List Ty} (helper : Helper) (args : Values (Comp laws Δ) helper.inputs)
      (next : Form laws callees (.tuple helper.outputs :: Δ) out) : Form laws callees Δ out
  /-- A call of `helper` presented by the law `entry`: its results, if any,
  are the law's terms in `next`, and a stopping law's stop is `next`. -/
  | byLaw {Δ : Scope} {out : List Ty} (entry : Fin laws.length) (helper : Helper)
      (next : Form laws callees Δ out) : Form laws callees Δ out
  /-- A kept call of a helper at its owner on the arguments' components: it
  stops as incomplete when one is absent, else runs the helper; the returned
  components are bound as a tuple. -/
  | owned {Δ : Scope} {out : List Ty} (owner : Nat) (helper : Helper) (args : Values (Comp laws Δ) helper.inputs)
      (next : Form laws callees (.tuple helper.outputs :: Δ) out) : Form laws callees Δ out
  /-- A repeat of a callback region on a count, a carried state and captures;
  the final state is bound as a tuple. -/
  | «repeat» {Δ : Scope} {out : List Ty} (spec : RepeatSpec) (site : String)
      (callback : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
      (count : Comp laws Δ .index) (state : Values (Comp laws Δ) spec.state)
      (captures : Values (Comp laws Δ) spec.captures)
      (next : Form laws callees (.tuple spec.state :: Δ) out) : Form laws callees Δ out
  /-- An application of a callee at the child context of `site` and `roles`, on
  the callee binders' arguments; the callee's returned tuple is bound. The
  applied signature is recorded so an instance checks it is the callee's. -/
  | apply {Δ : Scope} {out : List Ty} (callee : Fin callees.length) (signature : ProtocolSignature)
      (roles : List Nat) (site : String) (args : Values (Argument laws Δ) (calleeAt callees callee).pattern.scope)
      (next : Form laws callees (.tuple (calleeAt callees callee).signature.outputs :: Δ) out) : Form laws callees Δ out

/-- A named reason for not normalizing a body. -/
abbrev Refusal := String

/-! Presentation of a repeat callback's returned state: each position of the
state is absent at this role, presented as its present value, or presented as
its component. -/

inductive Carried where
  | absent | present | optional
  deriving DecidableEq, Repr

/-- The presented positions, in order, with their presentation. -/
def carried : {out : List Ty} → Values (fun _ => Carried) out → List (Ty × Bool)
  | [], .nil => []
  | _ :: _, .cons .absent rest => carried rest
  | ty :: _, .cons .present rest => (ty, false) :: carried rest
  | ty :: _, .cons .optional rest => (ty, true) :: carried rest

-- Materialize these equations in their owning module. Lazy copies in consumers
-- can refer to different private splitters. No global simp rule is installed.
attribute [local simp] entryAt.eq_def

end NormalForm
end Zkc.Source.Structured
