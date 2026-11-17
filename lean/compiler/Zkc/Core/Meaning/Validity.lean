module

public import Zkc.Core.Meaning.Local
public import Zkc.Core.Meaning.Requirement
public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
Validity of the values of a meaning, and every local operation keeps validity.

For any dialect, validity is a predicate of a value with its type (`Semantics.Dyn`), and values
of a list are valid when each of them with its type is (membership in `Semantics.dyns`), which is
`HList.All` of the predicate at each type (`Semantics.dyns_valid_iff`, the one conversion between
the form of the statements about any dialect and the form of those about functions). The values
of variables in scope are valid when every value in scope is (`env_all_valid`), and what a loop
collects is valid when its iterations' values are and the law of the collected values holds
(`CollectedOK`, `collected_valid`).

On valid operands, every local operation gives valid results. A row keeps validity by the model's
law; a literal reads as a valid value; an operation that the core owns keeps it by its meaning (a
refining operation because it gives its operand only inside its domain); a call keeps it when its
callee does (`FnTable.KeepsValidity`). The check of facts uses the statement for a local operation
as a whole (`localOp_valid`).

A function reads its values for a requirement as naturals and truth values (`localReading`), and
the relation of its written operations is that of the local operations that they print
(`LocalReturns`), with which the analysis reads requirements. The summary of a function applies no
written operation, so it is read with none (`Empty.elim`): so the requirements of a function's
summary hold of its inputs (`FnHeader.Required`), and a table of functions satisfies the summaries
of their headers (`FnTable.SatisfiesSummaries`, by `Summary.Holds`), against any callees as against
others (`Summary.holds_tables`). A statement about a function is made against callees (`Callees`):
with distinct keys, each satisfying its summary, keeping validity, and stopping only `undefined`
where their headers say that they cannot stop. Keeping validity is unconditional, apart from the
summary. That the functions of a table never stop `undefined` on any valid input (`FnTable.Safe`)
follows when no summary has a requirement (`FnTable.safe_of_unconditional`). The values of a
function are valid as the model says (`ValidDyn`); the payload of the alternative of a valid
variant is valid (`localPick_valid`), and so is what a loop of a function collects, of the size
given (`localCollect_valid`).
-/

namespace Zkc.Core

/-! ## Valid values of any dialect -/

section
variable {D : Dialect} {sem : Semantics D} {Valid : sem.Dyn → Prop}

/-- **The one conversion between the two forms of validity.** Values with their types are valid
exactly when each value is valid at its type: the form of the statements about any dialect
(membership in `sem.dyns`) and the form `HList.All` of the statements about functions. -/
theorem Semantics.dyns_valid_iff (sem : Semantics D) {Valid : sem.Dyn → Prop} :
    ∀ {items : List D.Ty} (vs : HList sem.Val items),
      (∀ v, v ∈ sem.dyns vs → Valid v) ↔ vs.All fun τ v => Valid ⟨τ, v⟩
  | [], .nil => ⟨fun _ => trivial, fun _ _ found => nomatch found⟩
  | _ :: _, .cons v rest => by
      rw [HList.all_cons, ← sem.dyns_valid_iff (Valid := Valid) rest]
      constructor
      · intro all
        exact ⟨all _ List.mem_cons_self, fun w found => all w (List.mem_cons_of_mem _ found)⟩
      · intro both w found
        rcases List.mem_cons.mp found with same | found
        · subst same
          exact both.1
        · exact both.2 w found

/-- The values of variables are valid when every value in scope is. -/
theorem env_all_valid {Γ : Ctx D.Ty} {env : Env sem.Val Γ}
    (valid : ∀ τ (x : Var Γ τ), Valid ⟨τ, env.get x⟩) :
    ∀ {items : List D.Ty} (xs : HList (Var Γ) items), ∀ v, v ∈ sem.dyns (env.all xs) → Valid v
  | [], .nil => fun _ found => nomatch found
  | _ :: _, .cons x rest => (sem.dyns_valid_iff _).mpr (HList.all_cons.mpr
      ⟨valid _ x, (sem.dyns_valid_iff _).mp (env_all_valid valid rest)⟩)

variable (sem Valid) in
/-- Values collected so far by a loop: as many of each type as iterations, each valid. -/
def CollectedOK : {each : List D.Ty} → HList (fun a => List (sem.Val a)) each → Nat → Prop
  | [], .nil, _ => True
  | a :: _, .cons vs rest, i =>
      vs.length = i ∧ (∀ v, v ∈ vs → Valid ⟨a, v⟩) ∧ CollectedOK rest i

/-- Nothing collected is as many as no iteration. -/
theorem collectedOK_empties : ∀ (each : List D.Ty),
    CollectedOK sem Valid (HList.empties (V := sem.Val) each) 0
  | [] => trivial
  | _ :: rest => ⟨rfl, fun _ found => (nomatch found), collectedOK_empties rest⟩

/-- One more iteration's valid values keep what is collected valid. -/
theorem collectedOK_push : ∀ {each : List D.Ty} {acc : HList (fun a => List (sem.Val a)) each}
    {i : Nat} {vs : HList sem.Val each}, CollectedOK sem Valid acc i →
    (∀ v, v ∈ sem.dyns vs → Valid v) → CollectedOK sem Valid (acc.push vs) (i + 1)
  | [], .nil, _, .nil, _, _ => trivial
  | _ :: _, .cons xs rest, _, .cons v more, collected, all => by
      obtain ⟨length, valid, others⟩ := collected
      have parts := HList.all_cons.mp ((sem.dyns_valid_iff (.cons v more)).mp all)
      refine ⟨by simp [length], fun w found => ?_,
        collectedOK_push others ((sem.dyns_valid_iff more).mpr parts.2)⟩
      rcases List.mem_cons.mp found with same | found
      · subst same
        exact parts.1
      · exact valid w found

/-- What a loop collects, as one value of each type, is valid, given the law that the values
collected of valid values are valid when they are as many as the size given. -/
theorem collected_valid
    (collect : ∀ (size : Option Nat) (a : D.Ty) (vs : List (sem.Val a)),
      (∀ n, size = some n → vs.length = n) → (∀ v, v ∈ vs → Valid ⟨a, v⟩) →
      Valid ⟨D.collected size a, sem.collect size a vs⟩)
    (size : Option Nat) {n : Nat} (fits : ∀ m, size = some m → n = m) :
    ∀ {each : List D.Ty} {acc : HList (fun a => List (sem.Val a)) each},
      CollectedOK sem Valid acc n → ∀ v, v ∈ sem.dyns (sem.collected size acc) → Valid v
  | [], .nil, _ => fun _ found => nomatch found
  | a :: _, .cons vs rest, collected => by
      obtain ⟨length, valid, others⟩ := collected
      refine (sem.dyns_valid_iff _).mpr (HList.all_cons.mpr ⟨collect size a vs.reverse
          (fun m e => by rw [List.length_reverse, length]; exact fits m e)
          (fun v found => valid v (List.mem_reverse.mp found)), ?_⟩)
      exact (sem.dyns_valid_iff _).mp (collected_valid collect size fits others)

end

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

/-- The requirements of the summary of a function's header hold of its inputs, read as a function
reads its values; they apply no written operation. -/
def FnHeader.Required (hdr : FnHeader V) (ins : HList M.Val hdr.ins) : Prop :=
  ∀ requirement, requirement ∈ hdr.summary.requires →
    requirement.Holds Empty.elim (localReading M) ((localSem M fns table).dyns ins)

end

/-- Every function of a table satisfies the summary of its header (`Summary.Holds`), read as a
function reads its values, with no written operation: on valid inputs that satisfy its
requirements, it never stops `undefined` and returns valid values that, with the inputs, satisfy
its guarantees. -/
def FnTable.SatisfiesSummaries {fns : List (FnHeader V)} (table : FnTable M fns) : Prop :=
  ∀ hdr (callee : Member fns hdr),
    Summary.Holds (localSem M fns table) (fun _ _ => True) (localReading M) Empty.elim
      (ValidDyn M) (· = .undefined) hdr.summary (table hdr callee)

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
      requirement.Holds Empty.elim (localReading M) ((localSem M fns table).dyns args) := by
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
