module

public import Zkc.Core.Meaning.Local
public import Zkc.Core.Meaning.Assertions
public import Zkc.Core.Meaning.ValidValues
public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
Validity of the values of a function, and every local operation keeps validity. The validity of
values for any dialect, and its one conversion to the form `HList.All` of the statements about
functions (`Semantics.dyns_valid_iff`), are in `Meaning/ValidValues.lean`.

On valid operands, every local operation gives valid results. A row keeps validity by the model's
law; a literal reads as a valid value; an operation that the core owns keeps it by its meaning (a
refining operation because it gives its operand only inside its domain); a call keeps it when its
callee does (`FnTable.KeepsValidity`). The check of facts uses the statement for a local operation
as a whole (`localOp_valid`).

A function reads its values for a requirement as naturals and truth values (`localReading`), and
the relation of its written operations is that of the local operations that they print
(`LocalReturns`). Header expressions use this relation with the fixed empty callee table.
`FnHeader.Required` reads the requirements on the inputs. `FnTable.SatisfiesSummaries`
uses `HeaderSummary.Holds` for each member, and `HeaderSummary.holds_tables` transports
the judgment across callee tables. A statement about a function is made against callees (`Callees`):
with distinct keys, each satisfying its summary, keeping validity, and stopping only `undefined`
where their headers say that they cannot stop. Keeping validity is unconditional, apart from the
summary. That the functions of a table never stop `undefined` on any valid input (`FnTable.Safe`)
follows when no summary has a requirement (`FnTable.safe_of_unconditional`). The values of a
function are valid as the model says (`ValidDyn`); the payload of the alternative of a valid
variant is valid (`localPick_valid`), and so is what a loop of a function collects, of the size
given (`localCollect_valid`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary} {M : Model V}

/-! ## Types without a value -/

mutual
  /-- A type of which a value is valid passes the test of having no value. -/
  theorem Ty.noValue_of_valid {C : Carriers V} : ∀ (τ : V.Ty) (v : τ.Val C), Ty.Valid C τ v →
      τ.noValue = false
    | .bool, _, _ => rfl
    | .nat, _, _ => rfl
    | .fin 0, _, valid => absurd valid (Nat.not_lt_zero _)
    | .fin (_ + 1), _, _ => rfl
    | .seq _ none, _, _ => rfl
    | .seq _ (some 0), _, _ => rfl
    | .seq item (some (n + 1)), vs, valid => by
        match vs, valid with
        | v :: _, valid => exact Ty.noValue_of_valid item v (valid.1 v List.mem_cons_self)
        | [], valid => exact absurd (valid.2 (n + 1) rfl) (fun h => Nat.succ_ne_zero n h.symm)
    | .tuple items, vs, valid => Tys.someNoValue_of_valid items vs valid
    | .record _ _ fields, vs, valid => Tys.someNoValue_of_valid fields vs valid
    | .variant _ alternatives, v, valid => Tys.allNoValue_of_valid alternatives v valid
    | .nominal _, _, _ => rfl
  /-- Types of which values are valid have none without a value. -/
  theorem Tys.someNoValue_of_valid {C : Carriers V} : ∀ (τs : Tys V.TypeKey) (vs : τs.Val C),
      Tys.Valid C τs vs → Tys.someNoValue τs = false
    | .nil, _, _ => rfl
    | .cons head rest, (v, vs), ⟨valid, others⟩ => by
        simp only [Tys.someNoValue, Ty.noValue_of_valid head v valid,
          Tys.someNoValue_of_valid rest vs others, Bool.or_self]
  /-- Types of which one has a valid value are not all without a value. -/
  theorem Tys.allNoValue_of_valid {C : Carriers V} : ∀ (τs : Tys V.TypeKey) (c : τs.Choice C),
      Tys.ValidChoice C τs c → Tys.allNoValue τs = false
    | .nil, c, _ => nomatch c
    | .cons head _, .inl v, valid => by
        simp only [Tys.allNoValue, Ty.noValue_of_valid head v valid, Bool.false_and]
    | .cons _ rest, .inr c, valid => by
        simp only [Tys.allNoValue, Tys.allNoValue_of_valid rest c valid, Bool.and_false]
end

/-! ## Literals -/

theorem readMany_valid {α : Type} {read : List Nat → Option (α × List Nat)} {P : α → Prop}
    (each : ∀ data v rest, read data = some (v, rest) → P v) :
    ∀ n data vs rest, readMany read n data = some (vs, rest) →
      (∀ v, v ∈ vs → P v) ∧ vs.length = n
  | 0, data, vs, rest, e => by
      simp only [readMany, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      simp
  | n + 1, data, vs, rest, e => by
      simp only [readMany] at e
      rw [Option.bind_eq_some_iff] at e
      obtain ⟨⟨v, mid⟩, first, e⟩ := e
      rw [Option.map_eq_some_iff] at e
      obtain ⟨⟨more, rest'⟩, others, e⟩ := e
      cases e
      obtain ⟨valid, length⟩ := readMany_valid each n mid more rest' others
      refine ⟨fun w found => ?_, by simp [length]⟩
      rcases List.mem_cons.mp found with rfl | found
      · exact each data _ mid first
      · exact valid w found

mutual
  /-- What a type reads is valid. -/
  theorem Ty.read_valid : ∀ (τ : V.Ty) (data : List Nat) (v : M.Val τ) (rest : List Nat),
      Ty.read M τ data = some (v, rest) → M.Valid τ v
    | .bool, _, _, _, _ => trivial
    | .nat, _, _, _, _ => trivial
    | .fin _, [], _, _, e => by simp [Ty.read] at e
    | .fin bound, n :: data, v, rest, e => by
        simp only [Ty.read] at e
        split at e
        · cases e
          assumption
        · cases e
    | .seq item (some size), data, vs, rest, e => by
        obtain ⟨valid, length⟩ :=
          readMany_valid (fun d w r h => Ty.read_valid item d w r h) size data vs rest e
        exact ⟨valid, fun n same => by cases same; exact length⟩
    | .seq _ none, [], _, _, e => by simp [Ty.read] at e
    | .seq item none, size :: data, vs, rest, e => by
        obtain ⟨valid, _⟩ :=
          readMany_valid (fun d w r h => Ty.read_valid item d w r h) size data vs rest e
        exact ⟨valid, fun n same => by cases same⟩
    | .tuple items, data, v, rest, e => Tys.read_valid items data v rest e
    | .record _ _ fields, data, v, rest, e => Tys.read_valid fields data v rest e
    | .variant _ _, [], _, _, e => by simp [Ty.read] at e
    | .variant _ alternatives, position :: data, v, rest, e =>
        Tys.readAt_valid alternatives position data v rest e
    | .nominal _, [], _, _, e => by simp [Ty.read] at e
    | .nominal key, n :: data, v, rest, e => by
        simp only [Ty.read] at e
        split at e
        · rename_i literal
          obtain ⟨w, value, valid⟩ := M.literals key n literal
          rw [value] at e
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, -⟩ := e
          exact valid
        · cases e
  /-- What types read in order is valid. -/
  theorem Tys.read_valid : ∀ (τs : Tys V.TypeKey) (data : List Nat) (v : τs.Val M.toCarriers)
      (rest : List Nat), Tys.read M τs data = some (v, rest) → Tys.Valid M.toCarriers τs v
    | .nil, _, _, _, _ => trivial
    | .cons head tail, data, v, rest, e => by
        simp only [Tys.read] at e
        rw [Option.bind_eq_some_iff] at e
        obtain ⟨⟨w, mid⟩, first, e⟩ := e
        rw [Option.map_eq_some_iff] at e
        obtain ⟨⟨ws, rest'⟩, others, e⟩ := e
        cases e
        exact ⟨Ty.read_valid head data w mid first, Tys.read_valid tail mid ws rest' others⟩
  /-- What the type at a position reads is valid. -/
  theorem Tys.readAt_valid : ∀ (τs : Tys V.TypeKey) (position : Nat) (data : List Nat)
      (v : τs.Choice M.toCarriers) (rest : List Nat),
      Tys.readAt M τs position data = some (v, rest) → Tys.ValidChoice M.toCarriers τs v
    | .nil, _, _, _, _, e => by simp [Tys.readAt] at e
    | .cons head _, 0, data, v, rest, e => by
        simp only [Tys.readAt] at e
        rw [Option.map_eq_some_iff] at e
        obtain ⟨⟨w, r⟩, first, e⟩ := e
        cases e
        exact Ty.read_valid head data w r first
    | .cons _ tail, position + 1, data, v, rest, e => by
        simp only [Tys.readAt] at e
        rw [Option.map_eq_some_iff] at e
        obtain ⟨⟨w, r⟩, found, e⟩ := e
        cases e
        exact Tys.readAt_valid tail position data w r found
end

/-- The value of a literal is valid. -/
theorem Ty.readLiteral_valid (τ : V.Ty) (data : List Nat) (reads : V.Reads τ data) :
    M.Valid τ (Ty.readLiteral M τ data reads) :=
  Ty.read_valid τ data _ [] (Ty.read_readLiteral M τ data reads)

/-! ## Parts of data -/

theorem Tys.ofHList_valid : ∀ (fields : Tys V.TypeKey) (vs : HList M.Val fields.toList),
    vs.All M.Valid → Tys.Valid M.toCarriers fields (Tys.ofHList M fields vs)
  | .nil, _, _ => trivial
  | .cons _ rest, .cons _ vs, valid =>
      ⟨(HList.all_cons.mp valid).1, Tys.ofHList_valid rest vs (HList.all_cons.mp valid).2⟩

theorem Tys.toHList_valid : ∀ (fields : Tys V.TypeKey) (v : fields.Val M.toCarriers),
    Tys.Valid M.toCarriers fields v → (Tys.toHList M fields v).All M.Valid
  | .nil, _, _ => trivial
  | .cons _ rest, (_, vs), ⟨first, others⟩ =>
      HList.all_cons.mpr ⟨first, Tys.toHList_valid rest vs others⟩

theorem Tys.getAt_valid : ∀ (fields : Tys V.TypeKey) {τ : V.Ty} (position : Member fields.toList τ)
    (v : fields.Val M.toCarriers), Tys.Valid M.toCarriers fields v →
    M.Valid τ (Tys.getAt M fields position v)
  | .nil, _, position, _, _ => nomatch position
  | .cons _ _, _, .head, (_, _), ⟨first, _⟩ => first
  | .cons _ rest, _, .tail position, (_, vs), ⟨_, others⟩ =>
      Tys.getAt_valid rest position vs others

theorem Tys.injectAt_valid : ∀ (alternatives : Tys V.TypeKey) {τ : V.Ty}
    (position : Member alternatives.toList τ) (v : M.Val τ), M.Valid τ v →
    Tys.ValidChoice M.toCarriers alternatives (Tys.injectAt M alternatives position v)
  | .nil, _, position, _, _ => nomatch position
  | .cons _ _, _, .head, _, valid => valid
  | .cons _ rest, _, .tail position, v, valid => Tys.injectAt_valid rest position v valid

theorem HList.ofItems_valid {item : V.Ty} : ∀ (xs : List (M.Val item)),
    (∀ x ∈ xs, M.Valid item x) → (HList.ofItems M xs).All M.Valid
  | [], _ => trivial
  | x :: xs, valid => HList.all_cons.mpr ⟨valid x List.mem_cons_self,
      HList.ofItems_valid xs (fun v mem => valid v (List.mem_cons_of_mem _ mem))⟩

theorem HList.sizedItems_valid {item : V.Ty} (xs : List (M.Val item)) (n : Nat) (size : xs.length = n)
    (valid : ∀ x ∈ xs, M.Valid item x) :
    (size ▸ HList.ofItems M xs : HList M.Val (List.replicate n item)).All M.Valid := by
  subst n
  exact HList.ofItems_valid xs valid

theorem HList.toItems_valid {item : V.Ty} : ∀ (count : Nat)
    (vs : HList M.Val (List.replicate count item)), vs.All M.Valid →
    (∀ v, v ∈ HList.toItems M count vs → M.Valid item v) ∧
      (HList.toItems M count vs).length = count
  | 0, _, _ => ⟨fun _ none => (nomatch none), rfl⟩
  | count + 1, .cons v vs, valid => by
      have rest := HList.toItems_valid count vs (HList.all_cons.mp valid).2
      refine ⟨fun w found => ?_, by simp [HList.toItems, rest.2]⟩
      rcases List.mem_cons.mp found with rfl | found
      · exact (HList.all_cons.mp valid).1
      · exact rest.1 w found

/-! ## The operations that the core owns -/

/-- A valid value, alone, is a valid list of values. -/
theorem valid_single {τ : V.Ty} (v : M.Val τ) (valid : M.Valid τ v) :
    (HList.cons v HList.nil : HList M.Val [τ]).All M.Valid :=
  HList.all_cons.mpr ⟨valid, trivial⟩

/-- An operation that the core owns keeps validity. -/
theorem ownedOp_valid : ∀ {ins outs : List V.Ty} (o : OwnedOp V ins outs) (args : HList M.Val ins)
    (results : HList M.Val outs), args.All M.Valid → ownedOp M o args = .done results →
    results.All M.Valid
  | _, _, .natAdd, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .natSub, .cons _ (.cons _ .nil), _, _, e => by
      simp only [ownedOp] at e
      split at e
      · cases e
        exact valid_single _ trivial
      · cases e
  | _, _, .natMul, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .natDiv, .cons _ (.cons _ .nil), _, _, e => by
      simp only [ownedOp] at e
      split at e
      · cases e
        exact valid_single _ trivial
      · cases e
  | _, _, .natRem, .cons _ (.cons _ .nil), _, _, e => by
      simp only [ownedOp] at e
      split at e
      · cases e
        exact valid_single _ trivial
      · cases e
  | _, _, .natPow, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .natEqual, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .natLess, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .boolAnd, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .boolOr, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .boolNot, .cons _ .nil, _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .boolEqual, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .seqLength .., .cons _ .nil, _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .seqAt .., .cons xs (.cons i .nil), _, valid, e => by
      have items := (HList.all_cons.mp valid).1
      simp only [ownedOp] at e
      split at e
      · rename_i v found
        cases e
        exact valid_single _ (items.1 v (List.mem_of_getElem? found))
      · cases e
  | _, _, .seqSlice _ _ result _, .cons xs (.cons first (.cons second .nil)), _, valid, e => by
      have items := (HList.all_cons.mp valid).1
      simp only [ownedOp] at e
      split at e
      · rename_i inside
        cases e
        obtain ⟨ordered, within, fits⟩ := inside
        refine valid_single _ ⟨fun v found => items.1 v
          (List.mem_of_mem_drop (List.mem_of_mem_take found)), fun n same => ?_⟩
        subst same
        have equal := Nat.eq_of_beq_eq_true fits
        simp only [List.length_take, List.length_drop]
        omega
      · cases e
  | _, _, .seqConcat _ first second, .cons xs (.cons ys .nil), _, valid, e => by
      have before := (HList.all_cons.mp valid).1
      have after := (HList.all_cons.mp (HList.all_cons.mp valid).2).1
      cases e
      refine valid_single _ ⟨fun v found => ?_, fun n same => ?_⟩
      · rcases List.mem_append.mp found with found | found
        · exact before.1 v found
        · exact after.1 v found
      · cases first with
        | none => cases same
        | some a =>
            cases second with
            | none => cases same
            | some b =>
                cases same
                simp only [List.length_append, before.2 a rfl, after.2 b rfl]
  | _, _, .seqFill .., .cons v .nil, _, valid, e => by
      cases e
      refine valid_single _ ⟨fun w found => ?_, fun n same => ?_⟩
      · rw [List.eq_of_mem_replicate found]
        exact (HList.all_cons.mp valid).1
      · cases same
        exact List.length_replicate
  | _, _, .seqSized _ size _, .cons xs .nil, _, valid, e => by
      have items := (HList.all_cons.mp valid).1
      simp only [ownedOp] at e
      split at e
      · rename_i length
        cases e
        exact valid_single _ ⟨items.1, fun n same => by cases same; exact length⟩
      · cases e
  | _, _, .natBelow _, .cons _ .nil, _, _, e => by
      simp only [ownedOp] at e
      split at e
      · rename_i below
        cases e
        exact valid_single _ below
      · cases e
  | _, _, .seqUnsized .., .cons xs .nil, _, valid, e => by
      cases e
      exact valid_single _ ⟨(HList.all_cons.mp valid).1.1, fun _ same => by cases same⟩
  | _, _, .finToNat _, .cons _ .nil, _, _, e => by
      cases e
      exact valid_single _ trivial
  | _, _, .finWiden _ _ fits, .cons _ .nil, _, valid, e => by
      cases e
      exact valid_single _ (Nat.lt_of_lt_of_le (HList.all_cons.mp valid).1 fits)
  | _, _, .makeSeq _ count, vs, _, valid, e => by
      cases e
      have items := HList.toItems_valid count vs valid
      exact valid_single _ ⟨items.1, fun n same => by cases same; exact items.2⟩
  | _, _, .makeTuple items, vs, _, valid, e => by
      cases e
      exact valid_single _ (Tys.ofHList_valid items vs valid)
  | _, _, .makeRecord _ _ fields, vs, _, valid, e => by
      cases e
      exact valid_single _ (Tys.ofHList_valid fields vs valid)
  | _, _, .getTuple items position _, .cons v .nil, _, valid, e => by
      cases e
      exact valid_single _ (Tys.getAt_valid items position v (HList.all_cons.mp valid).1)
  | _, _, .getRecord _ fields position _, .cons v .nil, _, valid, e => by
      cases e
      exact valid_single _
        (Tys.getAt_valid fields position v (HList.all_cons.mp valid).1)
  | _, _, .takeSeq item count, .cons xs .nil, _, valid, e => by
      obtain ⟨all, sized⟩ := (HList.all_cons.mp valid).1
      have size := sized count rfl
      simp [ownedOp, size] at e
      cases e
      exact HList.sizedItems_valid xs count size all
  | _, _, .takeTuple items, .cons v .nil, _, valid, e => by
      cases e
      exact Tys.toHList_valid items v (HList.all_cons.mp valid).1
  | _, _, .takeRecord _ _ fields, .cons v .nil, _, valid, e => by
      cases e
      exact Tys.toHList_valid fields v (HList.all_cons.mp valid).1
  | _, _, .variant _ alternatives position, .cons v .nil, _, valid, e => by
      cases e
      exact valid_single _
        (Tys.injectAt_valid alternatives position v (HList.all_cons.mp valid).1)

/-! ## Local operations -/

/-- The functions of a table keep validity: on valid inputs, the results that each gives are
valid. -/
def FnTable.KeepsValidity {fns : List (FnHeader V)} (table : FnTable M fns) : Prop :=
  ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins) (results : HList M.Val hdr.outs),
    args.All M.Valid → table hdr callee args = .done results → results.All M.Valid

/-- The functions of a table never stop `undefined` on valid inputs. -/
def FnTable.Safe {fns : List (FnHeader V)} (table : FnTable M fns) : Prop :=
  ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
    (table hdr callee args).Stops (· ≠ .undefined)

section
variable {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A row keeps validity, by the model's law. -/
theorem localOp_row_valid (key : V.RowKey)
    (signature : RowSignature V.TypeKey V.RowKey) (known : V.row key = some signature)
    (args : HList M.Val signature.ins) (results : HList M.Val signature.outs) :
    args.All M.Valid → localOp M table (.row key signature known) args = .done results →
    results.All M.Valid := by
  intro valid e
  cases applied : M.apply key signature known args with
  | none =>
      simp only [localOp, applied] at e
      cases e
  | some outs =>
      simp only [localOp, applied] at e
      cases e
      exact M.keeps key signature known args _ valid applied

/-- An operation that the core owns keeps validity. -/
theorem localOp_owned_valid {ins outs : List V.Ty} (o : OwnedOp V ins outs)
    (args : HList M.Val ins) (results : HList M.Val outs) :
    args.All M.Valid → localOp M table (.owned o) args = .done results →
    results.All M.Valid :=
  ownedOp_valid o args results

/-- A literal gives a valid value. -/
theorem localOp_literal_valid (τ : V.Ty) (data : List Nat) (reads : V.Reads τ data)
    (args : HList M.Val []) (results : HList M.Val [τ]) :
    localOp M table (.literal τ data reads) args = .done results → results.All M.Valid := by
  intro e
  cases e
  exact valid_single _ (Ty.readLiteral_valid τ data reads)

/-- A call keeps validity when its callee does. -/
theorem localOp_call_valid (keeps : FnTable.KeepsValidity table) {hdr : FnHeader V}
    (callee : Member fns hdr) (args : HList M.Val hdr.ins) (results : HList M.Val hdr.outs) :
    args.All M.Valid → localOp M table (.call callee) args = .done results →
    results.All M.Valid :=
  keeps hdr callee args results

/-- Every local operation keeps validity, when the functions that it may call do. -/
theorem localOp_valid (keeps : FnTable.KeepsValidity table) :
    ∀ {ins outs : List V.Ty} (o : LocalOp V fns ins outs) (args : HList M.Val ins)
      (results : HList M.Val outs), args.All M.Valid → localOp M table o args = .done results →
      results.All M.Valid
  | _, _, .row key signature known, args, results, valid =>
      localOp_row_valid table key signature known args results valid
  | _, _, .owned o, args, results, valid => localOp_owned_valid table o args results valid
  | _, _, .literal τ data reads, args, results, _ =>
      localOp_literal_valid table τ data reads args results
  | _, _, .call callee, args, results, valid =>
      localOp_call_valid table keeps callee args results valid

end

/-! ## The callees of a function -/

/-- A value of a function with its type is valid in the model: the validity of the values of
the semantics of a function (`localSem`), with which the statements about any dialect are made for
functions. -/
def ValidDyn (M : Model V) (value : (τ : V.Ty) × M.Val τ) : Prop := M.Valid value.1 value.2

/-- How a requirement reads a value of a function: a natural or an index as a natural, a truth
value as itself. -/
def localReading (M : Model V) : Reading ((τ : V.Ty) × M.Val τ) where
  nat
    | ⟨.nat, n⟩ => some n
    | ⟨.fin _, n⟩ => some n
    | _ => none
  bool
    | ⟨.bool, b⟩ => some b
    | _ => none

section
variable (M) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A written form gives results on operands when it is the printed form of a local operation
that returns those results on those operands: the relation of written operations of a function.
The values need not be valid. -/
def LocalReturns (written : LocalRaw V) (operands results : List (localSem M fns table).Dyn) :
    Prop :=
  ∃ (ins res : List V.Ty) (o : LocalOp V fns ins res) (args : HList M.Val ins)
    (returned : HList M.Val res), o.print = written ∧ (localSem M fns table).dyns args = operands ∧
    (localSem M fns table).dyns returned = results ∧ localOp M table o args = .done returned

/-- Header expressions refer to the vocabulary of the model. An empty function table
makes their meaning independent of insertion or replacement of function definitions. -/
def headerTable (M : Model V) : FnTable M [] := fun _ member => nomatch member

def HeaderClause.Holds (M : Model V) (args : List ((t : V.Ty) × M.Val t)) : HeaderClause V → Prop
  | .positional q => q.Holds Empty.elim (localReading M) args
  | .assertion c =>
    c.assertion.Holds (ValidRun (localSem M [] (headerTable M)) (LocalReturns M (headerTable M))
      (ValidDyn M)) (localReading M) args

/-- Stable preconditions and postconditions of a run with the supplied function table. -/
def HeaderSummary.Holds {ins outs : List V.Ty} (summary : HeaderSummary V)
    (run : HList M.Val ins → Local (HList M.Val outs)) : Prop :=
  ∀ args : HList M.Val ins, (∀ v ∈ (localSem M fns table).dyns args, ValidDyn M v) →
    (∀ q ∈ summary.requires, q.Holds M ((localSem M fns table).dyns args)) →
    (run args).Every (fun _ _ => True) (fun ys =>
      (∀ v ∈ (localSem M fns table).dyns ys, ValidDyn M v) ∧
      ∀ q ∈ summary.ensures, q.Holds M ((localSem M fns table).dyns args ++ (localSem M fns table).dyns ys))
      (· ≠ .undefined)

/-- Positional headers retain exactly the earlier summary judgment, for any implementation. -/
theorem HeaderSummary.positional_iff {ins outs : List V.Ty} (old : Summary Empty)
    (run : HList M.Val ins → Local (HList M.Val outs)) :
    (ofPositional old).Holds M table run ↔
      old.Holds (localSem M fns table) (fun _ _ => True) (localReading M)
        Empty.elim (ValidDyn M) (· = .undefined) run := by
  simp only [HeaderSummary.Holds, ofPositional, List.forall_mem_map, HeaderClause.Holds, Summary.Holds]

/-- The requirements of the summary of a function's header hold of its inputs, read as a function
reads its values, with header expressions interpreted on the empty callee table. -/
def FnHeader.Required (hdr : FnHeader V) (ins : HList M.Val hdr.ins) : Prop :=
  ∀ requirement, requirement ∈ hdr.summary.requires →
    requirement.Holds M ((localSem M fns table).dyns ins)

end

/-- Every function of a table satisfies the summary of its header (`HeaderSummary.Holds`).
On valid inputs that satisfy its
requirements, it never stops `undefined` and returns valid values that, with the inputs, satisfy
its guarantees. -/
def FnTable.SatisfiesSummaries {fns : List (FnHeader V)} (table : FnTable M fns) : Prop :=
  ∀ hdr (callee : Member fns hdr),
    HeaderSummary.Holds M table hdr.summary (table hdr callee)

/-- The values of a function with their types do not depend on its callees. -/
theorem localSem_dyns {fns fns' : List (FnHeader V)} (table : FnTable M fns)
    (table' : FnTable M fns') :
    ∀ {items : List V.Ty} (values : HList M.Val items),
      (localSem M fns table).dyns values = (localSem M fns' table').dyns values
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (List.cons _) (localSem_dyns table table' rest)

/-- **A summary of a function holds against any callees as against others.** A run of a function
that satisfies the summary of a function against one table of callees satisfies it against
another: the values with their types do not depend on the callees, and the summary applies no
written operation. -/
theorem Summary.holds_tables {fns fns' : List (FnHeader V)} {table : FnTable M fns}
    {table' : FnTable M fns'} {summary : Summary Empty} {ins outs : List V.Ty}
    {run : HList M.Val ins → Local (HList M.Val outs)}
    (holds : Summary.Holds (localSem M fns table) (fun _ _ => True) (localReading M) Empty.elim
      (ValidDyn M) (· = .undefined) summary run) :
    Summary.Holds (localSem M fns' table') (fun _ _ => True) (localReading M) Empty.elim
      (ValidDyn M) (· = .undefined) summary run := by
  intro values valid required
  have valid' : ∀ v, v ∈ (localSem M fns table).dyns values → ValidDyn M v := by
    rw [localSem_dyns table table']
    exact valid
  have required' : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds Empty.elim (localReading M) ((localSem M fns table).dyns values) := by
    rw [localSem_dyns table table']
    exact required
  exact Process.every_mono _ _
    (fun returned post => ⟨by rw [← localSem_dyns table table']; exact post.1, by
        rw [← localSem_dyns table table' values, ← localSem_dyns table table' returned]
        exact post.2⟩)
    (fun _ stop => stop) (holds values valid' required')

/-- A header describes the same input and output values against any table of callees. -/
theorem HeaderSummary.holds_tables {hs hs' : List (FnHeader V)} {table : FnTable M hs}
    {table' : FnTable M hs'} {s : HeaderSummary V} {ins outs : List V.Ty}
    {run : HList M.Val ins → Local (HList M.Val outs)} (holds : s.Holds M table run) :
    s.Holds M table' run := by
  intro values valid required
  rw [← localSem_dyns table table' values] at valid required
  exact Process.every_mono _ _
    (fun returned post => by
      rw [← localSem_dyns table table' values, ← localSem_dyns table table' returned]
      exact post) (fun _ stop => stop) (holds values valid required)

/-- The callees that a statement about a function is made against: distinct keys, each function
satisfying the summary of its header, valid results, and only `undefined` as a stop where the
header says that the function cannot stop. -/
structure Callees (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns) : Prop where
  distinct : (fns.map (·.key)).Nodup
  satisfies : FnTable.SatisfiesSummaries table
  keeps : FnTable.KeepsValidity table
  quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
    (table hdr callee args).Stops (· = .undefined)

/-- Functions that satisfy their summaries, of which none has a requirement, never stop
`undefined` on valid inputs. -/
theorem FnTable.safe_of_unconditional {fns : List (FnHeader V)} {table : FnTable M fns}
    (unconditional : ∀ hdr, hdr ∈ fns → hdr.summary.requires = [])
    (satisfies : FnTable.SatisfiesSummaries table) : FnTable.Safe table := by
  intro hdr callee args valid
  have none : ∀ requirement, requirement ∈ hdr.summary.requires →
      requirement.Holds M ((localSem M fns table).dyns args) := by
    intro requirement listed
    rw [unconditional hdr (Member.mem callee)] at listed
    cases listed
  exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ stop => stop)
    (satisfies hdr callee args (((localSem M fns table).dyns_valid_iff args).mpr valid) none)

/-- The payload of the alternative of a valid value of a variant is valid. -/
theorem Tys.pick_valid : ∀ (alts : Tys V.TypeKey) (c : alts.Choice M.toCarriers),
    Tys.ValidChoice M.toCarriers alts c → (Tys.pick M alts c).All M.Valid
  | .nil, c, _ => nomatch c
  | .cons _ _, .inl _, h => h
  | .cons _ rest, .inr c, h => Tys.pick_valid rest c h

theorem pickValid_cast {ps qs : List V.Ty} (h : ps = qs) (p : Pick M.Val ps) :
    (cast (congrArg (Pick M.Val) h) p).All M.Valid ↔ p.All M.Valid := by
  subst h
  rfl

theorem valid_cast {τ τ' : V.Ty} (h : τ = τ') (v : M.Val τ) :
    M.Valid τ' (cast (congrArg M.Val h) v) ↔ M.Valid τ v := by
  subst h
  rfl

/-- The payload of the alternative that a function picks of a valid variant is valid. -/
theorem localPick_valid {t : V.Ty} {payloads : List V.Ty}
    (h : ∃ key alternatives, t = .variant key alternatives ∧ payloads = alternatives.toList)
    (v : M.Val t) (valid : M.Valid t v) : (localPick M h v).All M.Valid := by
  simp only [localPick]
  rw [pickValid_cast (by obtain ⟨_, _, e, q⟩ := h; rw [Ty.alternatives_of e, q])]
  apply Tys.pick_valid
  have := (valid_cast (Ty.eq_variant h) v).mpr valid
  exact this

/-- What a loop of a function collects of valid values is valid, when they are as many as the
size given, if one is given: the law of `collected_valid` for functions. -/
theorem localCollect_valid {fns : List (FnHeader V)} {table : FnTable M fns} :
    ∀ (size : Option Nat) (a : V.Ty) (vs : List (M.Val a)), (∀ n, size = some n → vs.length = n) →
      (∀ v, v ∈ vs → ValidDyn M ⟨a, v⟩) →
      ValidDyn M
        ⟨(localDialect V fns).collected size a, (localSem M fns table).collect size a vs⟩ :=
  fun _ _ _ length valid => ⟨valid, length⟩

end

end Zkc.Core
