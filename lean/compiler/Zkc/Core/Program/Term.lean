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
  /-- A term in steps: an exit, or one instruction, the names of what it returns, and the
  rest. -/
  inductive Term (D : Dialect) : Ctx D.Ty → List D.Ty → Type where
    | ret {Γ outs} (exit : HList (Var Γ) outs) : Term D Γ outs
    | step {Γ outs mid} (key : Key) (i : Instr D Γ mid) (results : Names mid)
        (rest : Term D (Γ.extend results) outs) : Term D Γ outs
  /-- One instruction, without what follows it: what it runs, returning values of `mid`. -/
  inductive Instr (D : Dialect) : Ctx D.Ty → List D.Ty → Type where
    | op {Γ ins res} (o : D.Op ins res) (operands : HList (Var Γ) ins) : Instr D Γ res
    /-- They check a condition, and stop when it is false; it returns nothing. -/
    | guard {Γ t} (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (why : Reason) :
        Instr D Γ []
    | choose {Γ mid t} (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid) : Instr D Γ mid
    | cases {Γ mid t payloads} (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
        (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads) : Instr D Γ mid
    /-- They repeat a region as often as `times` says. The region has the iteration number
    and the carried values; it returns the carried values and one value of each collected
    type. The loop gives the last carried values and a sequence per collected type. -/
    | loop {Γ carried each} (w : D.Who) (times : Times D w Γ)
        (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
        (inputs : Names (D.index w :: carried))
        (body : Term D (Γ.extend inputs) (carried ++ each)) :
        Instr D Γ (carried ++ each.map (D.collected times.size))
    /-- One iteration of a loop whose iterations differ in type, written out. -/
    | block {Γ mid} (number : Nat) (body : Term D Γ mid) : Instr D Γ mid
    /-- An attempt that `w` own: the body runs with the number of the attempt. -/
    | attempt {Γ mid} (w : D.Who) (owns : D.Attempt w) (inputs : Names [D.index w])
        (body : Term D (Γ.extend inputs) mid) : Instr D Γ mid
  /-- A region per alternative, each with the name of its payload. -/
  inductive Arms (D : Dialect) : Ctx D.Ty → List D.Ty → List D.Ty → Type where
    | nil {Γ mid} : Arms D Γ mid []
    | cons {Γ mid payload payloads} (inputs : Names [payload])
        (arm : Term D (Γ.extend inputs) mid) (rest : Arms D Γ mid payloads) :
        Arms D Γ mid (payload :: payloads)
end

/-! ## Instruction builders -/

section
variable {D : Dialect}

@[match_pattern] abbrev Term.op {Γ outs ins res} (key : Key) (o : D.Op ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term D (Γ.extend results) outs) : Term D Γ outs :=
  .step key (.op o operands) results rest

@[match_pattern] abbrev Term.guard {Γ outs t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (why : Reason) (rest : Term D Γ outs) : Term D Γ outs :=
  .step key (.guard w c ok why) .nil rest

@[match_pattern] abbrev Term.choose {Γ outs mid t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid)
    (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs :=
  .step key (.choose w c ok gives onTrue onFalse) results rest

@[match_pattern] abbrev Term.cases {Γ outs mid t payloads} (key : Key) (w : D.Who) (x : Var Γ t)
    (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (arms : Arms D Γ mid payloads)
    (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs :=
  .step key (.cases w x ok gives arms) results rest

@[match_pattern] abbrev Term.loop {Γ outs carried each} (key : Key) (w : D.Who) (times : Times D w Γ)
    (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
    (inputs : Names (D.index w :: carried))
    (body : Term D (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (D.collected times.size)))
    (rest : Term D (Γ.extend results) outs) : Term D Γ outs :=
  .step key (.loop w times gives initial inputs body) results rest

@[match_pattern] abbrev Term.block {Γ outs mid} (key : Key) (number : Nat) (body : Term D Γ mid)
    (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs :=
  .step key (.block number body) results rest

@[match_pattern] abbrev Term.attempt {Γ outs mid} (key : Key) (w : D.Who) (owns : D.Attempt w)
    (inputs : Names [D.index w]) (body : Term D (Γ.extend inputs) mid)
    (results : Names mid) (rest : Term D (Γ.extend results) outs) : Term D Γ outs :=
  .step key (.attempt w owns inputs body) results rest

end

/-! ## Addresses -/

section
variable {D : Dialect}

mutual
  /-- The addresses of the instructions of a term: the blocks around each and its key; a block has
  none of its own and adds itself to the blocks of its body. -/
  def Term.addresses (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List (List (Key × Nat) × Key)
    | _, _, .ret _ => []
    | _, _, .step key i _ rest =>
        Instr.addresses blocks key i ++ Term.addresses blocks rest
  /-- The addresses of an instruction at a key and of the instructions of its regions. -/
  def Instr.addresses (blocks : List (Key × Nat)) (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List (List (Key × Nat) × Key)
    | _, _, .op _ _ => [(blocks, key)]
    | _, _, .guard _ _ _ _ => [(blocks, key)]
    | _, _, .choose _ _ _ _ onTrue onFalse =>
        (blocks, key) ::
          (Term.addresses blocks onTrue ++ Term.addresses blocks onFalse)
    | _, _, .cases _ _ _ _ arms => (blocks, key) :: Arms.addresses blocks arms
    | _, _, .loop _ _ _ _ _ body => (blocks, key) :: Term.addresses blocks body
    | _, _, .block number body => Term.addresses (blocks ++ [(key, number)]) body
    | _, _, .attempt _ _ _ body => (blocks, key) :: Term.addresses blocks body
  /-- The addresses of the instructions of arms. -/
  def Arms.addresses (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
        List (List (Key × Nat) × Key)
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest => Term.addresses blocks arm ++ Arms.addresses blocks rest
end

end

mutual
  /-- The keys of the blocks of a body. -/
  def Term.blockKeys {D : Dialect} :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Key
    | _, _, .ret _ => []
    | _, _, .step key i _ rest =>
        Instr.blockKeys key i ++ Term.blockKeys rest
  def Instr.blockKeys {D : Dialect} (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List Key
    | _, _, .op .. => []
    | _, _, .guard .. => []
    | _, _, .choose _ _ _ _ onTrue onFalse => Term.blockKeys onTrue ++ Term.blockKeys onFalse
    | _, _, .cases _ _ _ _ arms => Arms.blockKeys arms
    | _, _, .loop _ _ _ _ _ body => Term.blockKeys body
    | _, _, .block _ body => key :: Term.blockKeys body
    | _, _, .attempt _ _ _ body => Term.blockKeys body
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
    | _, _, .step _ i _ rest =>
        Instr.armed i && Term.armed rest
  def Instr.armed {D : Dialect} : {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → Bool
    | _, _, .op .. => true
    | _, _, .guard .. => true
    | _, _, .choose _ _ _ _ onTrue onFalse => Term.armed onTrue && Term.armed onFalse
    | _, _, .cases (mid := mid) _ _ _ _ arms => (arms.hasArm || mid.isEmpty) && Arms.armed arms
    | _, _, .loop _ _ _ _ _ body => Term.armed body
    | _, _, .block _ body => Term.armed body
    | _, _, .attempt _ _ _ body => Term.armed body
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
    | _, _, .step _ i _ rest =>
        Instr.canStop opStops i || Term.canStop opStops rest
  def Instr.canStop {D : Dialect} (opStops : ∀ {ins res : List D.Ty}, D.Op ins res → Bool) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → Bool
    | _, _, .op o _ => opStops o
    | _, _, .guard .. => true
    | _, _, .choose _ _ _ _ onTrue onFalse => Term.canStop opStops onTrue || Term.canStop opStops onFalse
    | _, _, .cases _ _ _ _ arms => Arms.canStop opStops arms
    | _, _, .loop _ _ _ _ _ body => Term.canStop opStops body
    | _, _, .block _ body => Term.canStop opStops body
    | _, _, .attempt _ _ _ body => Term.canStop opStops body
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
    | _, _, .step _ i _ rest =>
        Instr.calls opCalls i ++ Term.calls opCalls rest
  def Instr.calls {D : Dialect} (opCalls : ∀ {ins res : List D.Ty}, D.Op ins res → List Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List Key
    | _, _, .op o _ => opCalls o
    | _, _, .guard .. => []
    | _, _, .choose _ _ _ _ onTrue onFalse => Term.calls opCalls onTrue ++ Term.calls opCalls onFalse
    | _, _, .cases _ _ _ _ arms => Arms.calls opCalls arms
    | _, _, .loop _ _ _ _ _ body => Term.calls opCalls body
    | _, _, .block _ body => Term.calls opCalls body
    | _, _, .attempt _ _ _ body => Term.calls opCalls body
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
    | _, _, .step _ i results rest =>
        Instr.bindings i ++ results.toList ++ Term.bindings rest
  def Instr.bindings {D : Dialect} : {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid →
      List Name
    | _, _, .op .. => []
    | _, _, .guard .. => []
    | _, _, .choose _ _ _ _ onTrue onFalse => Term.bindings onTrue ++ Term.bindings onFalse
    | _, _, .cases _ _ _ _ arms => Arms.bindings arms
    | _, _, .loop _ _ _ _ inputs body => inputs.toList ++ Term.bindings body
    | _, _, .block _ body => Term.bindings body
    | _, _, .attempt _ _ inputs body => inputs.toList ++ Term.bindings body
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
