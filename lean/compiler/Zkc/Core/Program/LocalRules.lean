module

public import Zkc.Core.Program.Erase
public import Zkc.Core.Program.Typed

@[expose] public section

/-!
The rules of the local dialect: the written form of each of its operations and the operation
that a written form names, with both halves of the law of written forms: the written form of an
operation reads back as it, over headers with distinct keys (`localRules_lawful`), and an
operation that a written form reads as is written as that form, so that each operation has one
spelling (`localRules_canonical`).

An operation is written as a row of the vocabulary by its key (the operands have its
signature's types), as an operation that the core owns with its name, its types and its
numbers, as a literal with its data (which reads as its type), or as a call of the
function with a key (one of the headers before the caller has it). Nobody performs a form of
control, and nobody owns an attempt.

This is where the local dialect's operations meet their written forms. An operation that the
core owns is described by case analyses in several modules, and adding one adds an arm to each:
its name (`OwnedName`, `Program/Syntax.lean`) and its constructor (`OwnedOp`,
`Program/Dialects.lean`); its written form and its resolution here (`OwnedOp.name`,
`OwnedOp.resolve`, `OwnedOp.resolve_name`, `OwnedOp.name_resolve`); its meaning (`ownedOp`,
`Meaning/Local.lean`), with
the proofs that it keeps validity (`ownedOp_valid`, `Meaning/Validity.lean`) and stops only
`undefined` (`ownedOp_halts`, `Meaning/Stops.lean`); what the check of facts is told of it, one
entry of the table of the contracts of the operations that the core owns (`ownedContract`,
`Facts/Local.lean`), with its laws (`Facts/LocalLaws.lean`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-! ## The operations that the core owns -/

/-- What is written for an operation that the core owns: its name, the types that its
arguments are read from (the sequence, tuple, record, variant or `fin` types involved), and
a position (of a component, a field or an alternative) as its one number. -/
def OwnedOp.name {ins outs : List V.Ty} : OwnedOp V ins outs → OwnedName × List V.Ty × List Nat
  | .natAdd => (.natAdd, [], [])
  | .natSub => (.natSub, [], [])
  | .natMul => (.natMul, [], [])
  | .natDiv => (.natDiv, [], [])
  | .natRem => (.natRem, [], [])
  | .natPow => (.natPow, [], [])
  | .natEqual => (.natEqual, [], [])
  | .natLess => (.natLess, [], [])
  | .boolAnd => (.boolAnd, [], [])
  | .boolOr => (.boolOr, [], [])
  | .boolNot => (.boolNot, [], [])
  | .boolEqual => (.boolEqual, [], [])
  | .seqLength item size _ => (.seqLength, [.seq item size], [])
  | .seqAt item size _ => (.seqAt, [.seq item size], [])
  | .seqSlice item size result _ => (.seqSlice, [.seq item size, .seq item result], [])
  | .seqConcat item first second => (.seqConcat, [.seq item first, .seq item second], [])
  | .seqFill item count _ => (.seqFill, [.seq item (some count)], [])
  | .seqSized item size _ => (.seqSized, [.seq item (some size)], [])
  | .natBelow bound => (.natBelow, [.fin bound], [])
  | .seqUnsized item size => (.seqUnsized, [.seq item (some size)], [])
  | .finToNat bound => (.finToNat, [.fin bound], [])
  | .finWiden bound wider _ => (.finWiden, [.fin bound, .fin wider], [])
  | .makeSeq item count => (.make, [.seq item (some count)], [])
  | .makeTuple items => (.make, [.tuple items], [])
  | .makeRecord key linear fields => (.make, [.record key linear fields], [])
  | .getTuple items position _ => (.get, [.tuple items], [position.index])
  | .getRecord key fields position _ => (.get, [.record key false fields], [position.index])
  | .takeTuple items => (.take, [.tuple items], [])
  | .takeRecord key linear fields => (.take, [.record key linear fields], [])
  | .variant key alternatives position =>
      (.variant, [.variant key alternatives], [position.index])

/-- The operation that the core owns that a name, types and numbers write, with its
operand types and its result types. `make`, `get` and `take` are told apart by the type. -/
def OwnedOp.resolve : OwnedName → List V.Ty → List Nat →
    Option ((ins outs : List V.Ty) × OwnedOp V ins outs)
  | .natAdd, [], [] => some ⟨_, _, .natAdd⟩
  | .natSub, [], [] => some ⟨_, _, .natSub⟩
  | .natMul, [], [] => some ⟨_, _, .natMul⟩
  | .natDiv, [], [] => some ⟨_, _, .natDiv⟩
  | .natRem, [], [] => some ⟨_, _, .natRem⟩
  | .natPow, [], [] => some ⟨_, _, .natPow⟩
  | .natEqual, [], [] => some ⟨_, _, .natEqual⟩
  | .natLess, [], [] => some ⟨_, _, .natLess⟩
  | .boolAnd, [], [] => some ⟨_, _, .boolAnd⟩
  | .boolOr, [], [] => some ⟨_, _, .boolOr⟩
  | .boolNot, [], [] => some ⟨_, _, .boolNot⟩
  | .boolEqual, [], [] => some ⟨_, _, .boolEqual⟩
  | .seqLength, [.seq item size], [] =>
      if free : Ty.isLinear V item = false then some ⟨_, _, .seqLength item size free⟩ else none
  | .seqAt, [.seq item size], [] =>
      if free : Ty.isLinear V item = false then some ⟨_, _, .seqAt item size free⟩ else none
  | .seqSlice, [.seq item size, .seq other result], [] =>
      if other = item then
        if free : Ty.isLinear V item = false then
          some ⟨_, _, .seqSlice item size result free⟩
        else none
      else none
  | .seqConcat, [.seq item first, .seq other second], [] =>
      if other = item then some ⟨_, _, .seqConcat item first second⟩ else none
  | .seqFill, [.seq item (some count)], [] =>
      if free : Ty.isLinear V item = false then some ⟨_, _, .seqFill item count free⟩ else none
  | .seqSized, [.seq item (some size)], [] =>
      if free : Ty.isLinear V item = false then some ⟨_, _, .seqSized item size free⟩ else none
  | .natBelow, [.fin bound], [] => some ⟨_, _, .natBelow bound⟩
  | .seqUnsized, [.seq item (some size)], [] => some ⟨_, _, .seqUnsized item size⟩
  | .finToNat, [.fin bound], [] => some ⟨_, _, .finToNat bound⟩
  | .finWiden, [.fin bound, .fin wider], [] =>
      if le : bound ≤ wider then some ⟨_, _, .finWiden bound wider le⟩ else none
  | .make, [.seq item (some count)], [] => some ⟨_, _, .makeSeq item count⟩
  | .make, [.tuple items], [] => some ⟨_, _, .makeTuple items⟩
  | .make, [.record key linear fields], [] => some ⟨_, _, .makeRecord key linear fields⟩
  | .get, [.tuple items], [position] =>
      if free : Tys.anyLinear V items = false then
        (Member.atIndex items.toList position).map fun found =>
          ⟨_, _, .getTuple items found.2 free⟩
      else none
  | .get, [.record key false fields], [position] =>
      if free : Tys.anyLinear V fields = false then
        (Member.atIndex fields.toList position).map fun found =>
          ⟨_, _, .getRecord key fields found.2 free⟩
      else none
  | .take, [.tuple items], [] => some ⟨_, _, .takeTuple items⟩
  | .take, [.record key linear fields], [] => some ⟨_, _, .takeRecord key linear fields⟩
  | .variant, [.variant key alternatives], [position] =>
      (Member.atIndex alternatives.toList position).map fun found =>
        ⟨_, _, .variant key alternatives found.2⟩
  | _, _, _ => none

/-- Resolving what is written for an operation that the core owns gives the operation. -/
theorem OwnedOp.resolve_name : ∀ {ins outs : List V.Ty} (o : OwnedOp V ins outs),
    OwnedOp.resolve o.name.1 o.name.2.1 o.name.2.2 = some ⟨ins, outs, o⟩
  | _, _, .natAdd => rfl
  | _, _, .natSub => rfl
  | _, _, .natMul => rfl
  | _, _, .natDiv => rfl
  | _, _, .natRem => rfl
  | _, _, .natPow => rfl
  | _, _, .natEqual => rfl
  | _, _, .natLess => rfl
  | _, _, .boolAnd => rfl
  | _, _, .boolOr => rfl
  | _, _, .boolNot => rfl
  | _, _, .boolEqual => rfl
  | _, _, .seqLength _ _ free => by simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte]
  | _, _, .seqAt _ _ free => by simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte]
  | _, _, .seqSlice _ _ _ free => by
      simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte, ↓reduceIte]
  | _, _, .seqConcat .. => by simp only [OwnedOp.name, OwnedOp.resolve, ↓reduceIte]
  | _, _, .seqFill _ _ free => by simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte]
  | _, _, .seqSized _ _ free => by simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte]
  | _, _, .natBelow _ => rfl
  | _, _, .seqUnsized .. => rfl
  | _, _, .finToNat _ => rfl
  | _, _, .finWiden _ _ le => by simp only [OwnedOp.name, OwnedOp.resolve, le, ↓reduceDIte]
  | _, _, .makeSeq .. => rfl
  | _, _, .makeTuple _ => rfl
  | _, _, .makeRecord .. => rfl
  | _, _, .getTuple _ position free => by
      simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte, Member.atIndex_index position,
        Option.map_some]
  | _, _, .getRecord _ _ position free => by
      simp only [OwnedOp.name, OwnedOp.resolve, free, ↓reduceDIte, Member.atIndex_index position,
        Option.map_some]
  | _, _, .takeTuple _ => rfl
  | _, _, .takeRecord .. => rfl
  | _, _, .variant _ _ position => by
      simp only [OwnedOp.name, OwnedOp.resolve, Member.atIndex_index position, Option.map_some]

/-- What the core owns that a name, types and numbers resolve to is written with them: an
operation that the core owns has one written form. -/
theorem OwnedOp.name_resolve : ∀ {name : OwnedName} {types : List V.Ty} {numbers : List Nat}
    {ins outs : List V.Ty} {o : OwnedOp V ins outs},
    OwnedOp.resolve name types numbers = some ⟨ins, outs, o⟩ → o.name = (name, types, numbers) := by
  intro name types numbers ins outs o found
  unfold OwnedOp.resolve at found
  repeat' split at found
  all_goals first
    | (cases found; done)
    | (cases found; rfl)
    | (subst_vars; cases found; rfl)
    | (simp only [Option.map_eq_some_iff] at found
       obtain ⟨⟨_, _⟩, located, same⟩ := found
       cases same
       simp only [OwnedOp.name, Member.index_of_atIndex located])

/-! ## The operations of a function -/

/-- What is written for a local operation. -/
def LocalOp.print {fns : List (FnHeader V)} {ins res : List V.Ty} :
    LocalOp V fns ins res → LocalRaw V
  | .row key _ _ => .row key
  | .owned o => let written := o.name; .owned written.1 written.2.1 written.2.2
  | .literal τ data _ => .literal τ data
  | .call (hdr := hdr) _ => .call hdr.key

/-- Whether the data of a literal reads as its type. -/
instance Vocabulary.decideReads (τ : V.Ty) (data : List Nat) : Decidable (V.Reads τ data) :=
  inferInstanceAs (Decidable (Ty.scan V τ data = some []))

/-- A local operation of the operand types given, when they are those that it takes. -/
def LocalOp.ofOperands {fns : List (FnHeader V)} (operands ins res : List V.Ty)
    (o : LocalOp V fns ins res) :
    Except (Finding V.Ty (LocalRaw V)) ((res : List V.Ty) × LocalOp V fns operands res) :=
  if same : operands = ins then
    .ok ⟨res, cast (congrArg (fun ins => LocalOp V fns ins res) same.symm) o⟩
  else .error ⟨.operands, .types ins operands⟩

/-- The local operation that is written, on operands of the types given. -/
def LocalOp.read (fns : List (FnHeader V)) : (written : LocalRaw V) → (operands : List V.Ty) →
    Except (Finding V.Ty (LocalRaw V)) ((res : List V.Ty) × LocalOp V fns operands res)
  | .row key, operands =>
      match known : V.row key with
      | none => .error ⟨.row, .operation (.row key)⟩
      | some signature =>
          LocalOp.ofOperands operands signature.ins signature.outs
            (.row key signature known)
  | .owned name types numbers, operands =>
      match OwnedOp.resolve name types numbers with
      | none => .error ⟨.owned, .operation (.owned name types numbers)⟩
      | some ⟨ins, outs, o⟩ => LocalOp.ofOperands operands ins outs (.owned o)
  | .literal τ data, operands =>
      if reads : V.Reads τ data then LocalOp.ofOperands operands [] [τ] (.literal τ data reads)
      else .error ⟨.literal, .operation (.literal τ data)⟩
  | .call key, operands =>
      match Member.withKey (·.key) key fns with
      | [⟨hdr, callee⟩] => LocalOp.ofOperands operands hdr.ins hdr.outs (.call callee)
      | found => .error ⟨.callee, .callee key found.length⟩

theorem LocalOp.ofOperands_self {fns : List (FnHeader V)} {ins res : List V.Ty}
    (o : LocalOp V fns ins res) : LocalOp.ofOperands ins ins res o = .ok ⟨res, o⟩ := by
  simp only [LocalOp.ofOperands, ↓reduceDIte, cast_eq]

/-- What is written for an operation reads back as it, on its operands, when the functions
before have distinct keys. -/
theorem LocalOp.read_print {fns : List (FnHeader V)} (distinct : (fns.map (·.key)).Nodup) :
    ∀ {ins res : List V.Ty} (o : LocalOp V fns ins res), LocalOp.read fns o.print ins = .ok ⟨res, o⟩
  | _, _, .row key signature known => by
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
      simp only [LocalOp.print, LocalOp.read, Member.withKey_key (·.key) callee distinct,
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

/-- An operation of the operand types given is written as the operation that it is read
from. -/
theorem LocalOp.print_ofOperands {fns : List (FnHeader V)} {operands ins res res' : List V.Ty}
    (o : LocalOp V fns ins res) (o' : LocalOp V fns operands res')
    (found : LocalOp.ofOperands operands ins res o = .ok ⟨res', o'⟩) : o'.print = o.print := by
  unfold LocalOp.ofOperands at found
  split at found
  · rename_i same
    subst same
    cases found
    simp only [cast_eq]
  · cases found

/-- An operation that a written form reads as is written as that form: each local operation has
one spelling. -/
theorem LocalOp.print_read {fns : List (FnHeader V)} :
    ∀ {ins res : List V.Ty} (written : LocalRaw V) (o : LocalOp V fns ins res),
      LocalOp.read fns written ins = .ok ⟨res, o⟩ → o.print = written
  | _, _, .row key, o, found => by
      simp only [LocalOp.read] at found
      split at found
      · cases found
      · rw [LocalOp.print_ofOperands _ o found]
        rfl
  | _, _, .owned name types numbers, o, found => by
      simp only [LocalOp.read] at found
      split at found
      · cases found
      · rename_i ins outs owned resolved
        rw [LocalOp.print_ofOperands _ o found]
        simp only [LocalOp.print, OwnedOp.name_resolve resolved]
  | _, _, .literal τ data, o, found => by
      simp only [LocalOp.read] at found
      split at found
      · rw [LocalOp.print_ofOperands _ o found]
        rfl
      · cases found
  | _, _, .call key, o, found => by
      simp only [LocalOp.read] at found
      split at found
      · rename_i hdr callee located
        have named : hdr.key = key :=
          Member.key_of_withKey (·.key) key (found := ⟨hdr, callee⟩)
            (located ▸ List.mem_singleton_self _)
        rw [LocalOp.print_ofOperands _ o found]
        simp only [LocalOp.print, named]
      · cases found

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

/-- The written forms of the local rules are canonical: an operation that a written form reads
as is written as that form. No hypothesis on the headers is needed. -/
theorem localRules_canonical {fns : List (FnHeader V)} : (localRules fns).Canonical where
  op raw o found := LocalOp.print_read raw o found
  who _ _ _ := rfl

end

end Zkc.Core
