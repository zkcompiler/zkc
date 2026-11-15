module

public import Zkc.Core.Meaning.Local

@[expose] public section

/-!
Every local operation keeps validity: on valid operands, the results that it gives are valid.

A row keeps validity by the model's law; a literal reads as a valid value; an operation that the
core owns keeps it by its meaning (a refining operation because it gives its operand only inside
its domain); a call keeps it when its callee does. The check of facts uses the statement for a
local operation as a whole (`localOp_valid`).
-/

namespace Zkc.Core

theorem HList.all_cons {α : Type} {F : α → Type} {P : ∀ a, F a → Prop} {a : α} {rest : List α}
    {v : F a} {vs : HList F rest} : (HList.cons v vs).All P ↔ P a v ∧ vs.All P := Iff.rfl

section
variable {V : Vocabulary} {M : Model V}

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
    | .nominal _ _, [], _, _, e => by simp [Ty.read] at e
    | .nominal key statics, n :: data, v, rest, e => by
        simp only [Ty.read] at e
        split at e
        · rename_i literal
          obtain ⟨w, value, valid⟩ := M.literals key statics n literal
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

theorem Tys.getAt_valid : ∀ (fields : Tys V.TypeKey) {τ : V.Ty} (position : Var fields.toList τ)
    (v : fields.Val M.toCarriers), Tys.Valid M.toCarriers fields v →
    M.Valid τ (Tys.getAt M fields position v)
  | .nil, _, position, _, _ => nomatch position
  | .cons _ _, _, .head, (_, _), ⟨first, _⟩ => first
  | .cons _ rest, _, .tail position, (_, vs), ⟨_, others⟩ =>
      Tys.getAt_valid rest position vs others

theorem Tys.injectAt_valid : ∀ (alternatives : Tys V.TypeKey) {τ : V.Ty}
    (position : Var alternatives.toList τ) (v : M.Val τ), M.Valid τ v →
    Tys.ValidChoice M.toCarriers alternatives (Tys.injectAt M alternatives position v)
  | .nil, _, position, _, _ => nomatch position
  | .cons _ _, _, .head, _, valid => valid
  | .cons _ rest, _, .tail position, v, valid => Tys.injectAt_valid rest position v valid

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

/-- A value of a natural or a truth value, alone, is valid. -/
theorem valid_single_trivial {τ : V.Ty} (v : M.Val τ) (valid : M.Valid τ v) :
    (HList.cons v HList.nil : HList M.Val [τ]).All M.Valid :=
  HList.all_cons.mpr ⟨valid, trivial⟩

/-- An operation that the core owns keeps validity. -/
theorem ownedOp_valid : ∀ {ins outs : List V.Ty} (o : OwnedOp V ins outs) (args : HList M.Val ins)
    (results : HList M.Val outs), args.All M.Valid → ownedOp M o args = .done results →
    results.All M.Valid
  | _, _, .natAdd, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .natSub, .cons _ (.cons _ .nil), _, _, e => by
      simp only [ownedOp] at e
      split at e
      · cases e
        exact valid_single_trivial _ trivial
      · cases e
  | _, _, .natMul, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .natDiv, .cons _ (.cons _ .nil), _, _, e => by
      simp only [ownedOp] at e
      split at e
      · cases e
        exact valid_single_trivial _ trivial
      · cases e
  | _, _, .natRem, .cons _ (.cons _ .nil), _, _, e => by
      simp only [ownedOp] at e
      split at e
      · cases e
        exact valid_single_trivial _ trivial
      · cases e
  | _, _, .natPow, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .natEqual, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .natLess, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .boolAnd, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .boolOr, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .boolNot, .cons _ .nil, _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .boolEqual, .cons _ (.cons _ .nil), _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .seqLength .., .cons _ .nil, _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .seqAt .., .cons xs (.cons i .nil), _, valid, e => by
      have items := (HList.all_cons.mp valid).1
      simp only [ownedOp] at e
      split at e
      · rename_i v found
        cases e
        exact valid_single_trivial _ (items.1 v (List.mem_of_getElem? found))
      · cases e
  | _, _, .seqSlice _ _ result _, .cons xs (.cons first (.cons second .nil)), _, valid, e => by
      have items := (HList.all_cons.mp valid).1
      simp only [ownedOp] at e
      split at e
      · rename_i inside
        cases e
        obtain ⟨ordered, within, fits⟩ := inside
        refine valid_single_trivial _ ⟨fun v found => items.1 v
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
      refine valid_single_trivial _ ⟨fun v found => ?_, fun n same => ?_⟩
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
      refine valid_single_trivial _ ⟨fun w found => ?_, fun n same => ?_⟩
      · rw [List.eq_of_mem_replicate found]
        exact (HList.all_cons.mp valid).1
      · cases same
        exact List.length_replicate
  | _, _, .seqSized _ size, .cons xs .nil, _, valid, e => by
      have items := (HList.all_cons.mp valid).1
      simp only [ownedOp] at e
      split at e
      · rename_i length
        cases e
        exact valid_single_trivial _ ⟨items.1, fun n same => by cases same; exact length⟩
      · cases e
  | _, _, .natBelow _, .cons _ .nil, _, _, e => by
      simp only [ownedOp] at e
      split at e
      · rename_i below
        cases e
        exact valid_single_trivial _ below
      · cases e
  | _, _, .seqUnsized .., .cons xs .nil, _, valid, e => by
      cases e
      exact valid_single_trivial _ ⟨(HList.all_cons.mp valid).1.1, fun _ same => by cases same⟩
  | _, _, .finToNat _, .cons _ .nil, _, _, e => by
      cases e
      exact valid_single_trivial _ trivial
  | _, _, .finWiden _ _ fits, .cons _ .nil, _, valid, e => by
      cases e
      exact valid_single_trivial _ (Nat.lt_of_lt_of_le (HList.all_cons.mp valid).1 fits)
  | _, _, .makeSeq _ count, vs, _, valid, e => by
      cases e
      have items := HList.toItems_valid count vs valid
      exact valid_single_trivial _ ⟨items.1, fun n same => by cases same; exact items.2⟩
  | _, _, .makeTuple items, vs, _, valid, e => by
      cases e
      exact valid_single_trivial _ (Tys.ofHList_valid items vs valid)
  | _, _, .makeRecord _ _ fields, vs, _, valid, e => by
      cases e
      exact valid_single_trivial _ (Tys.ofHList_valid fields vs valid)
  | _, _, .getTuple items position _, .cons v .nil, _, valid, e => by
      cases e
      exact valid_single_trivial _ (Tys.getAt_valid items position v (HList.all_cons.mp valid).1)
  | _, _, .getRecord _ fields position _, .cons v .nil, _, valid, e => by
      cases e
      exact valid_single_trivial _
        (Tys.getAt_valid fields position v (HList.all_cons.mp valid).1)
  | _, _, .takeTuple items, .cons v .nil, _, valid, e => by
      cases e
      exact Tys.toHList_valid items v (HList.all_cons.mp valid).1
  | _, _, .takeRecord _ _ fields, .cons v .nil, _, valid, e => by
      cases e
      exact Tys.toHList_valid fields v (HList.all_cons.mp valid).1
  | _, _, .variant _ alternatives position, .cons v .nil, _, valid, e => by
      cases e
      exact valid_single_trivial _
        (Tys.injectAt_valid alternatives position v (HList.all_cons.mp valid).1)

/-! ## Local operations -/

/-- The functions of a table keep validity: on valid inputs, the results that each gives are
valid. -/
def FnTable.KeepsValidity {fns : List (FnHeader V)} (table : FnTable M fns) : Prop :=
  ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins) (results : HList M.Val hdr.outs),
    args.All M.Valid → table hdr callee args = .done results → results.All M.Valid

/-- The functions of a table never stop `undefined` on valid inputs. -/
def FnTable.Safe {fns : List (FnHeader V)} (table : FnTable M fns) : Prop :=
  ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
    (table hdr callee args).Stops (· ≠ .undefined)

section
variable {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A row keeps validity, by the model's law. -/
theorem localOp_row_valid (key : V.RowKey) (statics : List Static)
    (signature : RowSignature V.TypeKey V.RowKey) (known : V.row key statics = some signature)
    (args : HList M.Val signature.ins) (results : HList M.Val signature.outs) :
    args.All M.Valid → localOp M table (.row key statics signature known) args = .done results →
    results.All M.Valid := by
  intro valid e
  cases applied : M.apply key statics signature known args with
  | none =>
      simp only [localOp, applied] at e
      cases e
  | some outs =>
      simp only [localOp, applied] at e
      cases e
      exact M.keeps key statics signature known args _ valid applied

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
  exact valid_single_trivial _ (Ty.readLiteral_valid τ data reads)

/-- A call keeps validity when its callee does. -/
theorem localOp_call_valid (keeps : FnTable.KeepsValidity table) {hdr : FnHeader V}
    (callee : Var fns hdr) (args : HList M.Val hdr.ins) (results : HList M.Val hdr.outs) :
    args.All M.Valid → localOp M table (.call callee) args = .done results →
    results.All M.Valid :=
  keeps hdr callee args results

/-- Every local operation keeps validity, when the functions that it may call do. -/
theorem localOp_valid (keeps : FnTable.KeepsValidity table) :
    ∀ {ins outs : List V.Ty} (o : LocalOp V fns ins outs) (args : HList M.Val ins)
      (results : HList M.Val outs), args.All M.Valid → localOp M table o args = .done results →
      results.All M.Valid
  | _, _, .row key statics signature known, args, results, valid =>
      localOp_row_valid table key statics signature known args results valid
  | _, _, .owned o, args, results, valid => localOp_owned_valid table o args results valid
  | _, _, .literal τ data reads, args, results, _ =>
      localOp_literal_valid table τ data reads args results
  | _, _, .call callee, args, results, valid =>
      localOp_call_valid table keeps callee args results valid

end

end

end Zkc.Core
