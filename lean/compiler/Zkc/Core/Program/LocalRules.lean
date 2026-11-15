module

public import Zkc.Core.Program.Print

@[expose] public section

/-!
The rules of the local dialect: the written form of each of its operations and the operation
that a written form names, with the laws that make the printed form of an operation name it.

An operation is written as a row of the vocabulary with its static arguments (the operands
have its signature's types), as an operation that the core owns with its name, its types and
its static naturals, as a literal with its data (which reads as its type), or as a call of the
function with a key (one of the headers before the caller has it). Nobody performs a form of
control, and nobody owns an attempt.

This is the one place where the local dialect's operations meet their written forms: adding an
operation that the core owns is a constructor of `OwnedOp`, an entry of `OwnedOp.name` and one
of `OwnedOp.resolve` here, its meaning and its facts.
-/

namespace Zkc.Core

section
variable {T : Type}

/-- The position of a variable, from the innermost binding. -/
def Var.index {Γ : List T} {a : T} : Var Γ a → Nat
  | .head => 0
  | .tail x => x.index + 1

/-- The variable at a position, with its type. -/
def Var.atIndex : (Γ : List T) → Nat → Option ((t : T) × Var Γ t)
  | [], _ => none
  | t :: _, 0 => some ⟨t, .head⟩
  | _ :: Γ, n + 1 => (Var.atIndex Γ n).map fun found => ⟨found.1, .tail found.2⟩

theorem Var.atIndex_index : ∀ {Γ : List T} {a : T} (x : Var Γ a),
    Var.atIndex Γ x.index = some ⟨a, x⟩
  | _ :: _, _, .head => rfl
  | _ :: _, _, .tail x => by simp only [Var.index, Var.atIndex, Var.atIndex_index x, Option.map_some]

theorem Var.key_mem (keyOf : T → Key) : ∀ {items : List T} {a : T}, Var items a →
    keyOf a ∈ items.map keyOf
  | _ :: _, _, .head => List.mem_cons_self
  | _ :: _, _, .tail x => List.mem_cons_of_mem _ (Var.key_mem keyOf x)

theorem Var.withKey_absent (keyOf : T → Key) (key : Key) : ∀ {items : List T},
    key ∉ items.map keyOf → Var.withKey keyOf key items = []
  | [], _ => rfl
  | a :: rest, absent => by
      have other : keyOf a ≠ key := fun same => absent (same ▸ List.mem_cons_self)
      have later : key ∉ rest.map keyOf := fun found => absent (List.mem_cons_of_mem _ found)
      simp only [Var.withKey, other, ↓reduceIte, Var.withKey_absent keyOf key later, List.map_nil]

/-- With distinct keys, the variable with the key of an item is that item's. -/
theorem Var.withKey_key (keyOf : T → Key) : ∀ {items : List T} {a : T} (x : Var items a),
    (items.map keyOf).Nodup → Var.withKey keyOf (keyOf a) items = [⟨a, x⟩]
  | _ :: _, _, .head, distinct => by
      have absent := (List.nodup_cons.mp distinct).1
      simp only [Var.withKey, ↓reduceIte, Var.withKey_absent keyOf _ absent, List.map_nil]
  | b :: _, a, .tail x, distinct => by
      have ⟨absent, others⟩ := List.nodup_cons.mp distinct
      have other : keyOf b ≠ keyOf a := fun same => absent (same ▸ Var.key_mem keyOf x)
      simp only [Var.withKey, other, ↓reduceIte, Var.withKey_key keyOf x others, List.map_cons,
        List.map_nil]

end

section
variable {V : Vocabulary}

/-! ## The operations that the core owns -/

/-- What is written for an operation that the core owns: its name, its types and its static
naturals. -/
def OwnedOp.name {ins outs : List V.Ty} : OwnedOp V ins outs → OwnedName × List V.Ty × List Nat
  | .natAdd => (.natAdd, [], [])
  | .natSub => (.natSub, [], [])
  | .natLe => (.natLe, [], [])
  | .boolNot => (.boolNot, [], [])
  | .seqLength item size => (.seqLength, [.seq item size], [])
  | .seqAt item size => (.seqAt, [.seq item size], [])
  | .make key linear fields => (.make, [.record key linear fields], [])
  | .take key linear fields => (.take, [.record key linear fields], [])
  | .inject key alternatives position => (.inject, [.variant key alternatives], [position.index])

/-- The operation that the core owns that a name, types and static naturals write, with its
operand types and its result types. -/
def OwnedOp.resolve : OwnedName → List V.Ty → List Nat →
    Option ((ins outs : List V.Ty) × OwnedOp V ins outs)
  | .natAdd, [], [] => some ⟨_, _, .natAdd⟩
  | .natSub, [], [] => some ⟨_, _, .natSub⟩
  | .natLe, [], [] => some ⟨_, _, .natLe⟩
  | .boolNot, [], [] => some ⟨_, _, .boolNot⟩
  | .seqLength, [.seq item size], [] => some ⟨_, _, .seqLength item size⟩
  | .seqAt, [.seq item size], [] => some ⟨_, _, .seqAt item size⟩
  | .make, [.record key linear fields], [] => some ⟨_, _, .make key linear fields⟩
  | .take, [.record key linear fields], [] => some ⟨_, _, .take key linear fields⟩
  | .inject, [.variant key alternatives], [position] =>
      (Var.atIndex alternatives.toList position).map fun found =>
        ⟨_, _, .inject key alternatives found.2⟩
  | _, _, _ => none

/-- Resolving what is written for an operation that the core owns gives the operation. -/
theorem OwnedOp.resolve_name : ∀ {ins outs : List V.Ty} (o : OwnedOp V ins outs),
    OwnedOp.resolve o.name.1 o.name.2.1 o.name.2.2 = some ⟨ins, outs, o⟩
  | _, _, .natAdd => rfl
  | _, _, .natSub => rfl
  | _, _, .natLe => rfl
  | _, _, .boolNot => rfl
  | _, _, .seqLength .. => rfl
  | _, _, .seqAt .. => rfl
  | _, _, .make .. => rfl
  | _, _, .take .. => rfl
  | _, _, .inject _ _ position => by
      simp only [OwnedOp.name, OwnedOp.resolve, Var.atIndex_index position, Option.map_some]

/-! ## The operations of a function -/

/-- What is written for a local operation. -/
def LocalOp.print {fns : List (FnHeader V)} {ins res : List V.Ty} : LocalOp V fns ins res → LocalRaw V
  | .row key statics _ _ => .row key statics
  | .owned o => let written := o.name; .owned written.1 written.2.1 written.2.2
  | .literal τ data _ => .literal τ data
  | .call (hdr := hdr) _ => .call hdr.key

/-- Whether the data of a literal reads as its type. -/
instance Vocabulary.decideReads (τ : V.Ty) (data : List Nat) : Decidable (V.Reads τ data) :=
  inferInstanceAs (Decidable (Ty.scan V τ data = some []))

/-- A local operation of the operand types given, when they are those that it takes. -/
def LocalOp.ofOperands {fns : List (FnHeader V)} (operands ins res : List V.Ty)
    (o : LocalOp V fns ins res) :
    Except (Problem V.Ty (LocalRaw V)) ((res : List V.Ty) × LocalOp V fns operands res) :=
  if same : operands = ins then .ok ⟨res, cast (congrArg (fun ins => LocalOp V fns ins res) same.symm) o⟩
  else .error (problemOf .operands (.types ins operands))

/-- The local operation that is written, on operands of the types given. -/
def LocalOp.read (fns : List (FnHeader V)) : (written : LocalRaw V) → (operands : List V.Ty) →
    Except (Problem V.Ty (LocalRaw V)) ((res : List V.Ty) × LocalOp V fns operands res)
  | .row key statics, operands =>
      match known : V.row key statics with
      | none => .error (problemOf .row (.operation (.row key statics)))
      | some signature =>
          LocalOp.ofOperands operands signature.ins signature.outs (.row key statics signature known)
  | .owned name types statics, operands =>
      match OwnedOp.resolve name types statics with
      | none => .error (problemOf .owned (.operation (.owned name types statics)))
      | some ⟨ins, outs, o⟩ => LocalOp.ofOperands operands ins outs (.owned o)
  | .literal τ data, operands =>
      if reads : V.Reads τ data then LocalOp.ofOperands operands [] [τ] (.literal τ data reads)
      else .error (problemOf .literal (.operation (.literal τ data)))
  | .call key, operands =>
      match Var.withKey (·.key) key fns with
      | [⟨hdr, callee⟩] => LocalOp.ofOperands operands hdr.ins hdr.outs (.call callee)
      | found => .error (problemOf .callee (.callee key found.length))

theorem LocalOp.ofOperands_self {fns : List (FnHeader V)} {ins res : List V.Ty}
    (o : LocalOp V fns ins res) : LocalOp.ofOperands ins ins res o = .ok ⟨res, o⟩ := by
  simp only [LocalOp.ofOperands, ↓reduceDIte, cast_eq]

/-- What is written for an operation reads back as it, on its operands, when the functions
before have distinct keys. -/
theorem LocalOp.read_print {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup) :
    ∀ {ins res : List V.Ty} (o : LocalOp V fns ins res), LocalOp.read fns o.print ins = .ok ⟨res, o⟩
  | _, _, .row key statics signature known => by
      simp only [LocalOp.print, LocalOp.read]
      split
      · rename_i missing
        rw [known] at missing
        cases missing
      · rename_i found same
        rw [known] at same
        cases same
        exact LocalOp.ofOperands_self _
  | _, _, .owned o => by
      simp only [LocalOp.print, LocalOp.read, OwnedOp.resolve_name, LocalOp.ofOperands_self]
  | _, _, .literal τ data reads => by
      simp only [LocalOp.print, LocalOp.read, reads, ↓reduceDIte, LocalOp.ofOperands_self]
  | _, _, .call callee => by
      simp only [LocalOp.print, LocalOp.read, Var.withKey_key (·.key) callee distinct,
        LocalOp.ofOperands_self]

/-- What is written for an operation names it: with distinct keys before, two operations on
the same operands that are written alike are one. -/
theorem LocalOp.print_injective {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup)
    {ins res res' : List V.Ty} (o : LocalOp V fns ins res) (o' : LocalOp V fns ins res')
    (same : o.print = o'.print) :
    (⟨res, o⟩ : (res : List V.Ty) × LocalOp V fns ins res) = ⟨res', o'⟩ := by
  have both := LocalOp.read_print distinct o
  rw [same, LocalOp.read_print distinct o'] at both
  exact (Except.ok.inj both).symm

/-! ## The rules -/

/-- The rules of the local dialect, over the headers of the functions that a body may call. -/
def localRules (fns : List (FnHeader V)) : Rules (localDialect V fns) (LocalRaw V) Unit where
  sameTy := inferInstanceAs (DecidableEq V.Ty)
  op := LocalOp.read fns
  who := fun _ => .ok ()
  condition := fun _ t => inferInstanceAs (Decidable (t = .bool))
  alternatives := fun _ t =>
    match t with
    | .variant key alternatives => some ⟨alternatives.toList, key, alternatives, rfl, rfl⟩
    | _ => none
  count := fun _ t => inferInstanceAs (Decidable (t = .nat))
  gives := fun _ _ => isTrue trivial
  attempt := fun _ => isFalse id
  printOp := fun o => LocalOp.print o
  printWho := fun _ => ()

/-- The local rules are lawful over headers with distinct keys. -/
theorem localRules_lawful {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup) :
    (localRules fns).Lawful where
  op o := LocalOp.read_print distinct o
  who _ := rfl
  alternatives _ _ _ := fun ⟨_, _, same, payloads⟩ => by
    subst same
    subst payloads
    exact ⟨_, rfl⟩

end

end Zkc.Core
