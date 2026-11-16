module

public import Zkc.Core.Program.Context

@[expose] public section

/-!
Terms: one type, generic in a dialect.

A term is typed in a context of names and returns values; a nested region sees the context
around it. A variable is a name that the context has at its type, and a binding carries the
names that it binds: so a term keeps the names of the program by names that it was elaborated
from, and erasing its proofs gives that program back. A dialect gives its types, its operations,
who performs a form of control and what they may guard, choose, repeat and give. An operation,
a guard, a choice, a loop, a block and an attempt each have one key, which the producer gives;
with the blocks around it, it is the instruction's address.

The form holds what the meaning consumes and nothing else. What elaboration decides about a
body is said here as predicates: distinct addresses, case analyses without an arm that give
nothing, and that every name is bound at one place; linear use is in `Linear.lean`.
-/

namespace Zkc.Core

/-! ## Terms -/

structure Dialect where
  Ty : Type
  /-- An operation, with the types of its operands and of its results. -/
  Op : List Ty → List Ty → Type
  /-- Who performs a guard, a choice or a loop. -/
  Who : Type
  /-- The type is a condition that they may guard or choose on. -/
  Condition : Who → Ty → Prop
  /-- The type is a variant that they may choose on; inside the region of each alternative
  its payload has the type given. -/
  Alternatives : Who → Ty → List Ty → Prop
  /-- The type is a count that they may repeat by. -/
  Count : Who → Ty → Prop
  /-- The type of the iteration number inside their loop, and of the number of their
  attempt. -/
  index : Who → Ty
  /-- They may own an attempt. -/
  Attempt : Who → Prop
  /-- A region of their choice or loop may give a value of the type. -/
  Gives : Who → Ty → Prop
  /-- The type of the sequence of the values of a type that the iterations collect: of the
  size given, for a loop of a written number of iterations. -/
  collected : Option Nat → Ty → Ty

/-- How often a loop runs: a written number of times, or as often as a count that its
performers hold says. -/
inductive Times (D : Dialect) (w : D.Who) (Γ : Ctx D.Ty) where
  | fixed (n : Nat)
  | value {t : D.Ty} (count : Var Γ t) (ok : D.Count w t)

/-- The number of iterations, when it is written. -/
def Times.size {D : Dialect} {w : D.Who} {Γ : Ctx D.Ty} : Times D w Γ → Option Nat
  | .fixed n => some n
  | .value .. => none

mutual
  inductive Term (D : Dialect) : Ctx D.Ty → List D.Ty → Type where
    | ret {Γ outs} (exit : HList (Var Γ) outs) : Term D Γ outs
    | op {Γ outs ins res} (key : Key) (o : D.Op ins res) (operands : HList (Var Γ) ins)
        (results : Names res) (rest : Term D (Γ.extend results) outs) : Term D Γ outs
    /-- They check a condition, and stop when it is false. -/
    | guard {Γ outs t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (why : Reason) (rest : Term D Γ outs) : Term D Γ outs
    | choose {Γ outs mid t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid)
        (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs
    | cases {Γ outs mid t payloads} (key : Key) (w : D.Who) (x : Var Γ t)
        (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ mid → D.Gives w a)
        (arms : Arms D Γ mid payloads)
        (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs
    /-- They repeat a region as often as `times` says. The region has the iteration number
    and the carried values; it returns the carried values and one value of each collected
    type. The loop gives the last carried values and a sequence per collected type. -/
    | loop {Γ outs carried each} (key : Key) (w : D.Who) (times : Times D w Γ)
        (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
        (inputs : Names (D.index w :: carried))
        (body : Term D (Γ.extend inputs) (carried ++ each))
        (results : Names (carried ++ each.map (D.collected times.size)))
        (rest : Term D (Γ.extend results) outs) : Term D Γ outs
    /-- One iteration of a loop whose iterations differ in type, written out. -/
    | block {Γ outs mid} (key : Key) (number : Nat) (body : Term D Γ mid)
        (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs
    /-- An attempt that `w` own: the body runs with the number of the attempt. -/
    | attempt {Γ outs mid} (key : Key) (w : D.Who) (owns : D.Attempt w)
        (inputs : Names [D.index w]) (body : Term D (Γ.extend inputs) mid)
        (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs
  /-- A region per alternative, each with the name of its payload. -/
  inductive Arms (D : Dialect) : Ctx D.Ty → List D.Ty → List D.Ty → Type where
    | nil {Γ mid} : Arms D Γ mid []
    | cons {Γ mid payload payloads} (inputs : Names [payload])
        (arm : Term D (Γ.extend inputs) mid) (rest : Arms D Γ mid payloads) :
        Arms D Γ mid (payload :: payloads)
end

/-! ## Addresses -/

mutual
  /-- The addresses of the instructions of a body: the blocks around each and its key. -/
  def Term.addresses {D : Dialect} (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List (List (Key × Nat) × Key)
    | _, _, .ret _ => []
    | _, _, .op key _ _ _ rest => (blocks, key) :: Term.addresses blocks rest
    | _, _, .guard key _ _ _ _ rest => (blocks, key) :: Term.addresses blocks rest
    | _, _, .choose key _ _ _ _ onTrue onFalse _ rest =>
        (blocks, key) :: (Term.addresses blocks onTrue ++ Term.addresses blocks onFalse ++
          Term.addresses blocks rest)
    | _, _, .cases key _ _ _ _ arms _ rest =>
        (blocks, key) :: (Arms.addresses blocks arms ++ Term.addresses blocks rest)
    | _, _, .loop key _ _ _ _ _ body _ rest =>
        (blocks, key) :: (Term.addresses blocks body ++ Term.addresses blocks rest)
    | _, _, .block key number body _ rest =>
        Term.addresses (blocks ++ [(key, number)]) body ++ Term.addresses blocks rest
    | _, _, .attempt key _ _ _ body _ rest =>
        (blocks, key) :: (Term.addresses blocks body ++ Term.addresses blocks rest)
  def Arms.addresses {D : Dialect} (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
        List (List (Key × Nat) × Key)
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest => Term.addresses blocks arm ++ Arms.addresses blocks rest
end

mutual
  /-- The keys of the blocks of a body. -/
  def Term.blockKeys {D : Dialect} :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Key
    | _, _, .ret _ => []
    | _, _, .op _ _ _ _ rest => Term.blockKeys rest
    | _, _, .guard _ _ _ _ _ rest => Term.blockKeys rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        Term.blockKeys onTrue ++ Term.blockKeys onFalse ++ Term.blockKeys rest
    | _, _, .cases _ _ _ _ _ arms _ rest => Arms.blockKeys arms ++ Term.blockKeys rest
    | _, _, .loop _ _ _ _ _ _ body _ rest => Term.blockKeys body ++ Term.blockKeys rest
    | _, _, .block key _ body _ rest => key :: (Term.blockKeys body ++ Term.blockKeys rest)
    | _, _, .attempt _ _ _ _ body _ rest => Term.blockKeys body ++ Term.blockKeys rest
  def Arms.blockKeys {D : Dialect} :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List Key
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest => Term.blockKeys arm ++ Arms.blockKeys rest
end

/-- Every instruction of a body has its own address, and no block has the key of an
instruction: a site and a place name one instruction. The blocks of one stepped loop repeat
keys, each under its number. -/
def Term.Distinct {D : Dialect} {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) : Prop :=
  (decide (t.addresses []).Nodup &&
    t.blockKeys.all fun k => (t.addresses []).all fun address => address.2 != k) = true

/-! ## What a case analysis without an arm gives -/

/-- Whether a case analysis has an arm. -/
def Arms.hasArm {D : Dialect} {Γ : Ctx D.Ty} {mid payloads : List D.Ty} :
    Arms D Γ mid payloads → Bool
  | .nil => false
  | .cons .. => true

mutual
  /-- Whether every case analysis of a term that has no arm gives nothing. -/
  def Term.armed {D : Dialect} : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Bool
    | _, _, .ret _ => true
    | _, _, .op _ _ _ _ rest => Term.armed rest
    | _, _, .guard _ _ _ _ _ rest => Term.armed rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        Term.armed onTrue && Term.armed onFalse && Term.armed rest
    | _, _, .cases (mid := mid) _ _ _ _ _ arms _ rest =>
        (arms.hasArm || mid.isEmpty) && Arms.armed arms && Term.armed rest
    | _, _, .loop _ _ _ _ _ _ body _ rest => Term.armed body && Term.armed rest
    | _, _, .block _ _ body _ rest => Term.armed body && Term.armed rest
    | _, _, .attempt _ _ _ _ body _ rest => Term.armed body && Term.armed rest
  def Arms.armed {D : Dialect} : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Arms D Γ mid payloads → Bool
    | _, _, _, .nil => true
    | _, _, _, .cons _ arm rest => Term.armed arm && Arms.armed rest
end

/-! ## Whether a body can stop -/

mutual
  /-- Whether a term can stop with a reason: it has a guard, or an operation that can. -/
  def Term.canStop {D : Dialect} (opStops : ∀ {ins res : List D.Ty}, D.Op ins res → Bool) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Bool
    | _, _, .ret _ => false
    | _, _, .op _ o _ _ rest => opStops o || Term.canStop opStops rest
    | _, _, .guard .. => true
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        Term.canStop opStops onTrue || Term.canStop opStops onFalse || Term.canStop opStops rest
    | _, _, .cases _ _ _ _ _ arms _ rest => Arms.canStop opStops arms || Term.canStop opStops rest
    | _, _, .loop _ _ _ _ _ _ body _ rest => Term.canStop opStops body || Term.canStop opStops rest
    | _, _, .block _ _ body _ rest => Term.canStop opStops body || Term.canStop opStops rest
    | _, _, .attempt _ _ _ _ body _ rest => Term.canStop opStops body || Term.canStop opStops rest
  def Arms.canStop {D : Dialect} (opStops : ∀ {ins res : List D.Ty}, D.Op ins res → Bool) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → Bool
    | _, _, _, .nil => false
    | _, _, _, .cons _ arm rest => Term.canStop opStops arm || Arms.canStop opStops rest
end

mutual
  /-- The keys of the definitions that a term calls or applies, by its operations. -/
  def Term.calls {D : Dialect} (opCalls : ∀ {ins res : List D.Ty}, D.Op ins res → List Key) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Key
    | _, _, .ret _ => []
    | _, _, .op _ o _ _ rest => opCalls o ++ Term.calls opCalls rest
    | _, _, .guard _ _ _ _ _ rest => Term.calls opCalls rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        Term.calls opCalls onTrue ++ Term.calls opCalls onFalse ++ Term.calls opCalls rest
    | _, _, .cases _ _ _ _ _ arms _ rest => Arms.calls opCalls arms ++ Term.calls opCalls rest
    | _, _, .loop _ _ _ _ _ _ body _ rest => Term.calls opCalls body ++ Term.calls opCalls rest
    | _, _, .block _ _ body _ rest => Term.calls opCalls body ++ Term.calls opCalls rest
    | _, _, .attempt _ _ _ _ body _ rest => Term.calls opCalls body ++ Term.calls opCalls rest
  def Arms.calls {D : Dialect} (opCalls : ∀ {ins res : List D.Ty}, D.Op ins res → List Key) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List Key
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest => Term.calls opCalls arm ++ Arms.calls opCalls rest
end

/-! ## Single assignment -/

mutual
  /-- The names that a term binds, in order: the results of its instructions and the inputs of
  their regions. -/
  def Term.bindings {D : Dialect} : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs →
      List Name
    | _, _, .ret _ => []
    | _, _, .op _ _ _ results rest => results.toList ++ Term.bindings rest
    | _, _, .guard _ _ _ _ _ rest => Term.bindings rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse results rest =>
        Term.bindings onTrue ++ Term.bindings onFalse ++ results.toList ++ Term.bindings rest
    | _, _, .cases _ _ _ _ _ arms results rest =>
        Arms.bindings arms ++ results.toList ++ Term.bindings rest
    | _, _, .loop _ _ _ _ _ inputs body results rest =>
        inputs.toList ++ Term.bindings body ++ results.toList ++ Term.bindings rest
    | _, _, .block _ _ body results rest =>
        Term.bindings body ++ results.toList ++ Term.bindings rest
    | _, _, .attempt _ _ _ inputs body results rest =>
        inputs.toList ++ Term.bindings body ++ results.toList ++ Term.bindings rest
  def Arms.bindings {D : Dialect} : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Arms D Γ mid payloads → List Name
    | _, _, _, .nil => []
    | _, _, _, .cons inputs arm rest =>
        inputs.toList ++ Term.bindings arm ++ Arms.bindings rest
end

/-- Every name of a definition is bound at one place: its inputs and what its body binds are
different names. -/
def Term.BoundOnce {D : Dialect} {Γ : Ctx D.Ty} {outs : List D.Ty} (inputs : List Name)
    (t : Term D Γ outs) : Prop :=
  (inputs ++ t.bindings).Nodup

end Zkc.Core
