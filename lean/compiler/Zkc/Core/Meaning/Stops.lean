module

public import Zkc.Core.Meaning.Program

@[expose] public section

/-!
What a function whose header says that it cannot stop may stop with: `undefined` only.

A body that `Term.canStop` says cannot stop has no guard, and calls only functions whose headers
say the same. Every other stop of a local process is `undefined`: a row outside its domain, an
operation that the core owns outside its domain. So, against callees that stop only `undefined`,
such a body stops only `undefined`; in a program, every function whose header says that it
cannot stop does (`Defs.fnTable_stops_undefined`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-- Every stop of a local process satisfies `P` when each of its stops does. -/
theorem Local.stops_of_halts {A : Type} {P : Stop → Prop} :
    ∀ (p : Local A), (∀ h, p = .halt h → P h) → p.Stops P
  | .done _, _ => trivial
  | .halt h, halts => halts h rfl
  | .call op _, _ => nomatch op

/-- Every stop of an operation that the core owns is `undefined`. -/
theorem ownedOp_halts {ins outs : List V.Ty} (o : OwnedOp V ins outs) (args : HList M.Val ins)
    (h : Stop) : ownedOp M o args = .halt h → h = .undefined := by
  fun_cases ownedOp M o args <;> intro e <;> simp only [ownedOp] at e <;>
    first | (split at e <;> cases e <;> rfl) | cases e

/-- A local operation that cannot stop with a reason stops only `undefined`, against callees
whose headers say that they cannot stop and that stop only `undefined`. -/
theorem localOp_stops_undefined {fns : List (FnHeader V)} (table : FnTable M fns)
    (callees : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
      (table hdr callee args).Stops (· = .undefined)) :
    ∀ {ins res : List V.Ty} (o : LocalOp V fns ins res) (args : HList M.Val ins),
      LocalOp.canStop o = false → (localOp M table o args).Stops (· = .undefined)
  | _, _, .row key signature known, args, _ => by
      apply Local.stops_of_halts
      intro h e
      simp only [localOp] at e
      split at e <;> cases e
      rfl
  | _, _, .owned o, args, _ => Local.stops_of_halts _ (ownedOp_halts M o args)
  | _, _, .literal .., _, _ => trivial
  | _, _, .call callee, args, quiet => callees _ callee args quiet

/-- A choice between two processes keeps what holds on every path of both. -/
theorem cond_every {S : Sig} {H A : Type} {permitted : ∀ op, S.Reply op → Prop} {P : A → Prop}
    {R : H → Prop} (b : Bool) {x y : Process S H A} (onTrue : x.Every permitted P R)
    (onFalse : y.Every permitted P R) : (cond b x y).Every permitted P R := by
  cases b
  · exact onFalse
  · exact onTrue

variable {fns : List (FnHeader V)} (table : FnTable M fns)

mutual
  /-- A term that cannot stop with a reason stops only `undefined`, against callees whose
  headers say that they cannot stop and that stop only `undefined`. -/
  theorem Term.stops_undefined
      (callees : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins),
        hdr.canStop = false → (table hdr callee args).Stops (· = .undefined)) :
      ∀ {Γ : Ctx V.Ty} {outs : List V.Ty} (t : Term (localDialect V fns) Γ outs)
        (path : List Frame) (env : Env M.Val Γ),
        Term.canStop (fun o => LocalOp.canStop o) t = false →
        (t.denote (localSem M fns table) path env).Stops (· = .undefined)
    | _, _, .ret _, _, _, _ => trivial
    | _, _, .op _ o _ _ rest, path, _, quiet => by
        simp only [Term.canStop, Instr.canStop, Bool.or_eq_false_iff] at quiet
        simp only [Term.denote_op]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun _ _ => Term.stops_undefined callees rest path _ quiet.2)
          (fun _ e => e) (localOp_stops_undefined M table callees o _ quiet.1)
    | _, _, .guard .., _, _, quiet => by cases quiet
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, path, env, quiet => by
        simp only [Term.canStop, Instr.canStop, Bool.or_eq_false_iff] at quiet
        simp only [Term.denote_choose]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun _ _ => Term.stops_undefined callees rest path _ quiet.2)
          (fun _ e => e) (cond_every _ (Term.stops_undefined callees onTrue path env quiet.1.1)
            (Term.stops_undefined callees onFalse path env quiet.1.2))
    | _, _, .cases _ _ _ _ _ arms _ rest, path, env, quiet => by
        simp only [Term.canStop, Instr.canStop, Bool.or_eq_false_iff] at quiet
        simp only [Term.denote_cases]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun _ _ => Term.stops_undefined callees rest path _ quiet.2)
          (fun _ e => e) (Arms.stops_undefined callees arms path env _ quiet.1)
    | _, _, .loop _ _ _ _ _ _ body _ rest, path, _, quiet => by
        simp only [Term.canStop, Instr.canStop, Bool.or_eq_false_iff] at quiet
        simp only [Term.denote_loop]
        apply (Process.every_bind _ _ _ _ _).mpr
        refine Process.every_mono _ _ (P := fun _ => True)
          (fun _ _ => Term.stops_undefined callees rest path _ quiet.2) (fun _ e => e) ?_
        refine Process.every_iterate (fun _ _ => True) (· = Stop.undefined) _ (fun _ _ => True)
          (fun _ _ _ => ?_) _ 0 _ trivial
        simp only [Semantics.loopStep]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ e => e)
          (Term.stops_undefined callees body _ _ quiet.1)
    | _, _, .block _ _ body _ rest, path, env, quiet => by
        simp only [Term.canStop, Instr.canStop, Bool.or_eq_false_iff] at quiet
        simp only [Term.denote_block]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun _ _ => Term.stops_undefined callees rest path _ quiet.2)
          (fun _ e => e) (Term.stops_undefined callees body _ env quiet.1)
    | _, _, .attempt _ _ owns _ _ _ _, _, _, _ => nomatch owns
  /-- The arms of a case analysis that cannot stop with a reason stop only `undefined`. -/
  theorem Arms.stops_undefined
      (callees : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins),
        hdr.canStop = false → (table hdr callee args).Stops (· = .undefined)) :
      ∀ {Γ : Ctx V.Ty} {mid payloads : List V.Ty} (arms : Arms (localDialect V fns) Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ) (pick : Pick M.Val payloads),
        Arms.canStop (fun o => LocalOp.canStop o) arms = false →
        (arms.denote (localSem M fns table) path env pick).Stops (· = .undefined)
    | _, _, _, .nil, _, _, pick, _ => nomatch pick
    | _, _, _, .cons _ arm _, path, _, .here _, quiet => by
        simp only [Arms.canStop, Bool.or_eq_false_iff] at quiet
        exact Term.stops_undefined callees arm path _ quiet.1
    | _, _, _, .cons _ _ rest, path, env, .there pick, quiet => by
        simp only [Arms.canStop, Bool.or_eq_false_iff] at quiet
        exact Arms.stops_undefined callees rest path env pick quiet.2
end

end

section
variable {V : Vocabulary} (M : Model V)

/-- In a program, a function whose header says that it cannot stop stops only `undefined`: its
body cannot stop with a reason (`FnConditions.stops`), and calls only such functions. -/
theorem Defs.fnTable_stops_undefined : ∀ {hs : Headers V} (defs : Defs V hs) (hdr : FnHeader V)
    (f : Member hs.fns hdr) (ins : HList M.Val hdr.ins), hdr.canStop = false →
    (Defs.fnTable M defs hdr f ins).Stops (· = .undefined)
  | _, .nil, _, f, _, _ => nomatch f
  | _, .fn _ _ body ok rest _, _, .head, _, quiet =>
      Term.stops_undefined M (Defs.fnTable M rest)
        (fun hdr' f' ins' quiet' => Defs.fnTable_stops_undefined rest hdr' f' ins' quiet') body
        [] _ (ok.stops.symm.trans quiet)
  | _, .fn _ _ _ _ rest _, _, .tail f, ins, quiet => Defs.fnTable_stops_undefined rest _ f ins quiet
  | _, .protocol _ _ _ _ rest, _, f, ins, quiet => Defs.fnTable_stops_undefined rest _ f ins quiet

end

end Zkc.Core
