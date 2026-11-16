module

public import Zkc.Core.Transform.Step
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Evidence.Claim

@[expose] public section

/-!
What the judgments about a function rest on, and the meaning of a function against two tables of
callees.

The check of facts is a producer of assurance: a function that it accepts is assured with the
bounds that it gives (`TypedFn.check_assured`, from `checkFacts_sound`). Following is another,
from a source that is safe by any route: when a second function follows the analysis of a first
that is safe with no refusal and no place that differs, the second is assured with the bounds
recorded while it follows, and the two mean the same (`TypedFn.follows_assured`, from
`Analysis.follow_assured` and the laws of the function dialect). The second is not analysed by
itself, and the refusals of the first's own analysis are not read. "The same meaning" of
functions is symmetric and transitive (`TypedFn.SameAs.symm`, `TypedFn.SameAs.trans`), and that
a function is safe is that its body is assured, in the sense of `Evidence/Claim.lean`, in the
scope of the empty path and its inputs bound to valid values (`TypedFn.safe_iff_assured`). What
a stored function is typed as is its elaboration (`typeFn_ok`).

A function that calls a replaced function is the same term run against another table of
callees. On valid values in scope, a term of a function returns valid values against callees
that keep validity (`Term.denote_valid`), and it means the same against two tables that agree on
valid inputs when one of them keeps validity (`Term.denote_tables`): every call is on valid
values, where the two tables agree. Neither needs the check of facts. With it, a program whose
functions follow those of an accepted program gives every function the meaning of the function of
the other with its header (`Defs.functionsFollow_sound`, `Admission/Programs.lean`); the second
program is taken apart at each definition by `Defs.followsFn_true` and
`Defs.followsProtocol_true`.
-/
namespace Zkc.Core

open FactCheck (env_all_valid localPick_valid CollectedOK collectedOK_empties
  collectedOK_push collected_valid)

/-! ## A function against two tables of callees -/

section
variable {V : Vocabulary} {M : Model V}

/-- One more name bound to a valid value keeps every value in scope valid. -/
theorem Env.insert_valid {Γ : Ctx V.Ty} {env : Env M.Val Γ}
    (valid : ∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) (bound : Name) {τ : V.Ty} (v : M.Val τ)
    (valid' : M.Valid τ v) :
    ∀ σ (x : Var (Γ.insert bound τ) σ), M.Valid σ ((env.insert bound v).get x) := by
  intro σ x
  obtain ⟨name, found⟩ := x
  show M.Valid σ (env.insert bound v name σ found)
  by_cases same : name = bound
  · have typed : σ = τ := by
      have look := found
      rw [Ctx.find?_insert, ite_eq_left same] at look
      exact (Option.some.inj look).symm
    subst typed
    rw [eq_of_heq (Env.insert_at_bound env bound v same found)]
    exact valid'
  · rw [Env.insert_at_other env bound v same]
    exact valid σ ⟨name, (ite_eq_right same).symm.trans
      ((Ctx.find?_insert Γ bound τ name).symm.trans found)⟩

/-- The names of a binding bound to valid values keep every value in scope valid. -/
theorem Env.extend_valid : ∀ {Γ : Ctx V.Ty} {env : Env M.Val Γ},
    (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
    ∀ {types : List V.Ty} (bound : Names types) (vs : HList M.Val types), vs.All M.Valid →
      ∀ τ (x : Var (Γ.extend bound) τ), M.Valid τ ((env.extend bound vs).get x)
  | _, _, valid, [], .nil, .nil, _ => valid
  | _, _, valid, _ :: _, .cons name rest, .cons v vs, all =>
      Env.extend_valid (Env.insert_valid valid name v (HList.all_cons.mp all).1) rest vs
        (HList.all_cons.mp all).2

/-- What a local process returns has a property when every value that it returns as `.done`
has it. -/
theorem Local.every_of_done {A : Type} {P : A → Prop} :
    ∀ {p : Local A}, (∀ a, p = .done a → P a) → p.Every (fun _ _ => True) P (fun _ => True)
  | .done a, returns => returns a rfl
  | .halt _, _ => trivial
  | .call op _, _ => nomatch op

/-- A local process followed by two continuations that are the same on every value that it
returns is one process. -/
theorem Local.bind_congr {A B : Type} {P : A → Prop} :
    ∀ {p : Local A} {f g : A → Local B}, p.Every (fun _ _ => True) P (fun _ => True) →
      (∀ a, P a → f a = g a) → p.bind f = p.bind g
  | .done a, _, _, holds, same => same a holds
  | .halt _, _, _, _, _ => rfl
  | .call op _, _, _, _, _ => nomatch op

/-- Bounded iteration of local steps that are the same on every state that satisfies an
invariant which every step keeps is one process. -/
theorem Local.iterate_congr {A : Type} (invariant : Nat → A → Prop)
    {step step' : Nat → A → Local A}
    (same : ∀ i a, invariant i a → step' i a = step i a)
    (kept : ∀ i a, invariant i a →
      (step i a).Every (fun _ _ => True) (invariant (i + 1)) (fun _ => True)) :
    ∀ (n i : Nat) (a : A), invariant i a →
      Process.iterate n step' i a = Process.iterate n step i a
  | 0, _, _, _ => rfl
  | n + 1, i, a, holds => by
      simp only [Process.iterate]
      rw [same i a holds]
      exact Local.bind_congr (kept i a holds) fun a' holds' =>
        Local.iterate_congr invariant same kept n (i + 1) a' holds'

variable {fns : List (FnHeader V)}

/-- A local operation on valid operands means the same against two tables that agree on valid
inputs: only a call reads the table. -/
theorem localOp_tables {table table' : FnTable M fns}
    (agree : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
      table' hdr callee args = table hdr callee args) :
    ∀ {ins res : List V.Ty} (o : LocalOp V fns ins res) (args : HList M.Val ins),
      args.All M.Valid → localOp M table' o args = localOp M table o args
  | _, _, .row .., _, _ => rfl
  | _, _, .owned _, _, _ => rfl
  | _, _, .literal .., _, _ => rfl
  | _, _, .call callee, args, valid => agree _ callee args valid

variable (table : FnTable M fns)

/-- How often a loop of a function runs does not depend on the callees. -/
theorem localSem_times (table' : FnTable M fns) {Γ : Ctx V.Ty} {w : (localDialect V fns).Who}
    (times : Times (localDialect V fns) w Γ) (env : Env M.Val Γ) :
    (localSem M fns table').times times env = (localSem M fns table).times times env := by
  cases times <;> rfl

/-- What a loop of a function collects, as one value, does not depend on the callees. -/
theorem localSem_collected (table' : FnTable M fns) (size : Option Nat) :
    ∀ {each : List V.Ty} (collected : HList (fun a => List (M.Val a)) each),
      (localSem M fns table').collected size collected =
        (localSem M fns table).collected size collected
  | [], .nil => rfl
  | a :: _, .cons values rest =>
      congrArg (HList.cons ((localSem M fns table).collect size a values.reverse))
        (localSem_collected table' size rest)

/-- The state of a loop of a function is valid: its carried values, and what it collected,
as many of each type as iterations. -/
def LoopValid {carried each : List V.Ty} (i : Nat)
    (state : (localSem M fns table).LoopState carried each) : Prop :=
  state.1.All M.Valid ∧ CollectedOK state.2 i

mutual
  /-- **A term of a function returns valid values** on valid values in scope, against callees
  that keep validity. Every value that it binds is valid: no operation, choice, case analysis or
  loop of a function gives an invalid value from valid ones. -/
  theorem Term.denote_valid (keeps : FnTable.KeepsValidity table) :
      ∀ {Γ : Ctx V.Ty} {outs : List V.Ty} (t : Term (localDialect V fns) Γ outs)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        (t.denote (localSem M fns table) path env).Every (fun _ _ => True)
          (fun outs => outs.All M.Valid) (fun _ => True)
    | _, _, .ret exit, _, _, valid => env_all_valid valid exit
    | _, _, .op _ o operands results rest, path, env, valid => by
        simp only [Term.denote]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _
          (fun values valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results values valid')) (fun _ h => h)
          (Local.every_of_done fun values ran =>
            localOp_valid table keeps o _ values (env_all_valid valid operands) ran)
    | _, _, .guard .., path, env, valid => by
        simp only [Term.denote]
        exact cond_every _ (Term.denote_valid keeps _ path env valid) trivial
    | _, _, .choose _ _ _ _ _ onTrue onFalse results rest, path, env, valid => by
        simp only [Term.denote]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact cond_every _
          (Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
            (Term.denote_valid keeps onTrue path env valid))
          (Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
            (Term.denote_valid keeps onFalse path env valid))
    | _, _, .cases _ _ x ok _ arms results rest, path, env, valid => by
        simp only [Term.denote]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
          (Arms.denote_valid keeps arms path env valid _ (localPick_valid ok _ (valid _ x)))
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, path, env, valid => by
        simp only [Term.denote]
        apply (Process.every_bind _ _ _ _ _).mpr
        have fits : ∀ m, times.size = some m → 0 + (localSem M fns table).times times env = m := by
          intro m sized
          cases times with
          | fixed n =>
              simp only [Times.size, Option.some.injEq] at sized
              subst sized
              exact Nat.zero_add _
          | value => cases sized
        refine Process.every_mono _ _ (fun state (loopValid : LoopValid table _ state) =>
            Term.denote_valid keeps rest path _ (Env.extend_valid valid results _
              ((all_append _ _).mpr ⟨loopValid.1, collected_valid (table := table) times.size
                fits loopValid.2⟩))) (fun _ h => h)
          (Process.every_iterate _ _ _ (LoopValid table) (fun i state stateValid => ?_) _ 0 _
            ⟨env_all_valid valid initial, collectedOK_empties each⟩)
        simp only [Semantics.loopStep]
        apply (Process.every_bind _ _ _ _ _).mpr
        refine Process.every_mono _ _ (fun out outValid => ?_) (fun _ h => h)
          (Term.denote_valid keeps body _ _ (Env.extend_valid valid inputs _
            (HList.all_cons.mpr ⟨trivial, stateValid.1⟩)))
        have parts := (all_append _ _).mp
          (by rw [split_append]; exact outValid :
            ((HList.split carried out).1.append (HList.split carried out).2).All M.Valid)
        exact ⟨parts.1, collectedOK_push stateValid.2 parts.2⟩
    | _, _, .block _ _ body results rest, path, env, valid => by
        simp only [Term.denote]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
          (Term.denote_valid keeps body _ env valid)
    | _, _, .attempt _ _ owns _ _ _ _, _, _, _ => nomatch owns
  /-- The arms of a case analysis of a function return valid values on valid values in scope and
  a valid payload, against callees that keep validity. -/
  theorem Arms.denote_valid (keeps : FnTable.KeepsValidity table) :
      ∀ {Γ : Ctx V.Ty} {mid payloads : List V.Ty} (arms : Arms (localDialect V fns) Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        ∀ pick : Pick M.Val payloads, FactCheck.PickValid pick →
        (arms.denote (localSem M fns table) path env pick).Every (fun _ _ => True)
          (fun outs => outs.All M.Valid) (fun _ => True)
    | _, _, _, .nil, _, _, _, pick, _ => nomatch pick
    | _, _, _, .cons inputs arm _, path, _, valid, .here v, pickValid =>
        Term.denote_valid keeps arm path _ (Env.extend_valid valid inputs (.cons v .nil)
          (HList.all_cons.mpr ⟨pickValid, trivial⟩))
    | _, _, _, .cons _ _ rest, path, env, valid, .there pick, pickValid =>
        Arms.denote_valid keeps rest path env valid pick pickValid
end

variable {table} (table' : FnTable M fns)

mutual
  /-- **A term of a function means the same against two tables of callees that agree on valid
  inputs**, on valid values in scope, when the first table keeps validity: every value that the
  term binds is valid, so every call is on valid values, where the tables agree. -/
  theorem Term.denote_tables (keeps : FnTable.KeepsValidity table)
      (agree : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
        table' hdr callee args = table hdr callee args) :
      ∀ {Γ : Ctx V.Ty} {outs : List V.Ty} (t : Term (localDialect V fns) Γ outs)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        t.denote (localSem M fns table') path env = t.denote (localSem M fns table) path env
    | _, _, .ret _, _, _, _ => rfl
    | _, _, .op _ o operands results rest, path, env, valid => by
        have operandsValid := env_all_valid valid operands
        simp only [Term.denote]
        show (localOp M table' o (env.all operands)).bind _ =
          (localOp M table o (env.all operands)).bind _
        rw [localOp_tables agree o _ operandsValid]
        exact Local.bind_congr
          (Local.every_of_done fun values ran =>
            localOp_valid table keeps o _ values operandsValid ran)
          fun values valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results values valid')
    | _, _, .guard _ _ c ok _ rest, path, env, valid => by
        simp only [Term.denote]
        rw [Term.denote_tables keeps agree rest path env valid]
    | _, _, .choose _ _ c ok _ onTrue onFalse results rest, path, env, valid => by
        simp only [Term.denote]
        rw [Term.denote_tables keeps agree onTrue path env valid,
          Term.denote_tables keeps agree onFalse path env valid]
        exact Local.bind_congr
          (cond_every _ (Term.denote_valid table keeps onTrue path env valid)
            (Term.denote_valid table keeps onFalse path env valid))
          fun mids valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results mids valid')
    | _, _, .cases _ _ x ok _ arms results rest, path, env, valid => by
        simp only [Term.denote]
        show (arms.denote (localSem M fns table') path env (localPick M ok (env.get x))).bind _ =
          (arms.denote (localSem M fns table) path env (localPick M ok (env.get x))).bind _
        rw [Arms.denote_tables keeps agree arms path env valid _ (localPick_valid ok _ (valid _ x))]
        exact Local.bind_congr
          (Arms.denote_valid table keeps arms path env valid _ (localPick_valid ok _ (valid _ x)))
          fun mids valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results mids valid')
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, path, env, valid => by
        simp only [Term.denote]
        have fits : ∀ m, times.size = some m → 0 + (localSem M fns table).times times env = m := by
          intro m sized
          cases times with
          | fixed n =>
              simp only [Times.size, Option.some.injEq] at sized
              subst sized
              exact Nat.zero_add _
          | value => cases sized
        have kept : ∀ i (state : (localSem M fns table).LoopState carried each),
            LoopValid table i state →
            ((localSem M fns table).loopStep w inputs (fun path' env' => body.denote
              (localSem M fns table) path' env') key path env i state).Every (fun _ _ => True)
              (LoopValid table (i + 1)) (fun _ => True) := by
          intro i state stateValid
          simp only [Semantics.loopStep]
          apply (Process.every_bind _ _ _ _ _).mpr
          refine Process.every_mono _ _ (fun out outValid => ?_) (fun _ h => h)
            (Term.denote_valid table keeps body _ _ (Env.extend_valid valid inputs _
              (HList.all_cons.mpr ⟨trivial, stateValid.1⟩)))
          have parts := (all_append _ _).mp
            (by rw [split_append]; exact outValid :
              ((HList.split carried out).1.append (HList.split carried out).2).All M.Valid)
          exact ⟨parts.1, collectedOK_push stateValid.2 parts.2⟩
        have initialValid : LoopValid table 0 (env.all initial, HList.empties each) :=
          ⟨env_all_valid valid initial, collectedOK_empties each⟩
        have iterated := Local.iterate_congr (LoopValid table)
          (step' := (localSem M fns table').loopStep w inputs (fun path' env' => body.denote
            (localSem M fns table') path' env') key path env)
          (fun i state stateValid => by
            simp only [Semantics.loopStep]
            rw [Term.denote_tables keeps agree body _ _ (Env.extend_valid valid inputs _
              (HList.all_cons.mpr ⟨trivial, stateValid.1⟩))])
          kept ((localSem M fns table).times times env) 0 _ initialValid
        rw [localSem_times table table' times env, iterated]
        refine Local.bind_congr
          (Process.every_iterate _ _ _ (LoopValid table) kept _ 0 _ initialValid)
          fun state loopValid => ?_
        rw [localSem_collected table table' times.size state.2]
        exact Term.denote_tables keeps agree rest path _
          (Env.extend_valid valid results _ ((all_append _ _).mpr ⟨loopValid.1,
            collected_valid (table := table) times.size fits loopValid.2⟩))
    | _, _, .block _ _ body results rest, path, env, valid => by
        simp only [Term.denote]
        rw [Term.denote_tables keeps agree body _ env valid]
        exact Local.bind_congr (Term.denote_valid table keeps body _ env valid)
          fun mids valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results mids valid')
    | _, _, .attempt _ _ owns _ _ _ _, _, _, _ => nomatch owns
  /-- The arms of a case analysis of a function mean the same against two tables of callees that
  agree on valid inputs, on valid values in scope and a valid payload, when the first table keeps
  validity. -/
  theorem Arms.denote_tables (keeps : FnTable.KeepsValidity table)
      (agree : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
        table' hdr callee args = table hdr callee args) :
      ∀ {Γ : Ctx V.Ty} {mid payloads : List V.Ty} (arms : Arms (localDialect V fns) Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        ∀ pick : Pick M.Val payloads, FactCheck.PickValid pick →
        arms.denote (localSem M fns table') path env pick =
          arms.denote (localSem M fns table) path env pick
    | _, _, _, .nil, _, _, _, pick, _ => nomatch pick
    | _, _, _, .cons inputs arm _, path, _, valid, .here v, pickValid =>
        Term.denote_tables keeps agree arm path _ (Env.extend_valid valid inputs (.cons v .nil)
          (HList.all_cons.mpr ⟨pickValid, trivial⟩))
    | _, _, _, .cons _ _ rest, path, env, valid, .there pick, pickValid =>
        Arms.denote_tables keeps agree rest path env valid pick pickValid
end

end

/-! ## Two bodies of functions of which the second follows the first -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)}

end

/-! ## The judgments about a function -/

section
variable {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- The relation "same meaning" of functions is symmetric. -/
theorem TypedFn.SameAs.symm {f g : TypedFn V fns hdr} (same : f.SameAs g) : g.SameAs f :=
  fun M table callees ins valid => (same M table callees ins valid).symm

/-- The relation "same meaning" of functions is transitive. -/
theorem TypedFn.SameAs.trans {f g h : TypedFn V fns hdr} (first : f.SameAs g)
    (second : g.SameAs h) : f.SameAs h :=
  fun M table callees ins valid =>
    (first M table callees ins valid).trans (second M table callees ins valid)

/-- What a stored function is typed as is its elaboration. -/
theorem typeFn_ok {region : Region (LocalRaw V) Unit} {f : TypedFn V fns hdr}
    (typed : typeFn fns hdr region = .ok f) :
    elabFn fns hdr region = .ok ⟨f.inputs, f.body, f.conditions⟩ := by
  unfold typeFn at typed
  split at typed
  · cases typed
  · rename_i elaborated
    cases typed
    exact elaborated

/-- **The check of facts is a producer of assurance.** A function that the check of facts
accepts is assured with the bounds that the check gives (`checkFacts_sound`). -/
theorem TypedFn.check_assured (f : TypedFn V fns hdr) {bounds : List (Place × Nat)}
    (checked : f.check = .ok bounds) : f.Assured bounds :=
  ⟨fun _ _ callees ins valid =>
    (checkFacts_sound callees hdr.key f.inputs f.body f.conditions.distinct checked []
      (fun _ _ none => nomatch none) ins valid).2,
   fun _ _ callees F recorded ins valid =>
    (checkFacts_sound callees hdr.key f.inputs f.body f.conditions.distinct checked F recorded
      ins valid).1⟩

open Analysis in
/-- What it is for a second function to follow a first: it follows the analysis of the first
with no refusal and no place that differs, and its bounds are those recorded while it
follows. -/
theorem TypedFn.follows_ok {source target : TypedFn V fns hdr} {bounds : List (Place × Nat)}
    (followed : source.follows target = .ok bounds) :
    (follow (localFactRules V fns) (localSkelRules V fns) hdr.key none
        (analyse (localFactRules V fns) (localSkelRules V fns) hdr.key none source.inputs
          source.body) target.inputs target.body).accepted = true ∧
      bounds = (follow (localFactRules V fns) (localSkelRules V fns) hdr.key none
        (analyse (localFactRules V fns) (localSkelRules V fns) hdr.key none source.inputs
          source.body) target.inputs target.body).state.st.bounds.reverse := by
  unfold TypedFn.follows at followed
  dsimp only at followed
  split at followed
  · rename_i refused same
    cases followed
    exact ⟨by simp only [Exit.accepted, refused, same, List.isEmpty_nil, Bool.and_self], rfl⟩
  · cases followed

open Analysis FactCheck in
/-- **Following is a producer of assurance and of sameness, from a source that is safe by any
route.** When a second function follows the analysis of a first that is safe, however that is
known, the second is assured with the bounds recorded while it follows, and the two mean the
same (`Analysis.follow_assured`). The refusals of the first's own analysis are not read. -/
theorem TypedFn.follows_assured {source target : TypedFn V fns hdr}
    {bounds : List (Place × Nat)} (safe : source.Safe)
    (followed : source.follows target = .ok bounds) :
    target.Assured bounds ∧ source.SameAs target := by
  obtain ⟨accepted, recordedBounds⟩ := TypedFn.follows_ok followed
  have sound := fun (M : Model V) (table : FnTable M fns) (callees : Callees M table)
      (F : List (Place × Nat))
      (recorded : ∀ p b, (p, b) ∈ F → p.definition = hdr.key → p.role = none → (p, b) ∈ bounds)
      (ins : HList M.Val hdr.ins) (valid : ins.All M.Valid) =>
    follow_assured (localFactRules V fns) (localSkelRules V fns) (localSem M fns table)
      (fun _ _ => True) (localReading M) (LocalReturns M table) (ValidDyn M) (· = .undefined)
      (localFactRules_lawful M table callees.distinct callees.safe callees.keeps callees.quiet _)
      (localSkelRules_lawful callees.distinct) hdr.key hdr.key none source.inputs target.inputs
      source.body target.body target.conditions.distinct accepted F
      (fun p b inside here unowned => by
        have mine := recorded p b inside here unowned
        rw [recordedBounds] at mine
        exact List.mem_reverse.mp mine)
      ins (by rw [localDyns_eq_toDyns M table]; exact toDyns_valid valid)
      (Process.every_mono _ _ (fun _ _ => trivial) (fun _ stop => stop)
        (safe M table callees ins valid))
  refine ⟨⟨fun M table callees ins valid => ?_,
    fun M table callees F recorded ins valid => (sound M table callees F recorded ins valid).1⟩,
    fun M table callees ins valid =>
      (sound M table callees [] (fun _ _ none => nomatch none) ins valid).2.2.eq_of_noSig⟩
  refine Process.every_mono _ _ (fun outs returned => ?_) (fun _ stop => stop)
    (sound M table callees [] (fun _ _ none => nomatch none) ins valid).2.1
  rw [localDyns_eq_toDyns M table] at returned
  exact valid_of_toDyns returned

open FactCheck in
/-- **A function is safe exactly when its body is assured** in the scope of a function: for
every model and callees, on the empty path and the inputs bound to valid values, with the
validity of the model and the stop `undefined` (`Assured`, `Evidence/Claim.lean`). The judgment
about a function is the generic one at that scope. -/
theorem TypedFn.safe_iff_assured (f : TypedFn V fns hdr) :
    f.Safe ↔ ∀ (M : Model V) (table : FnTable M fns), Callees M table →
      Zkc.Core.Assured (localSem M fns table) (fun _ _ => True) (ValidDyn M) (· = .undefined)
        f.body
        (fun path env => path = [] ∧
          ∃ ins : HList M.Val hdr.ins, ins.All M.Valid ∧ env = Env.empty.extend f.inputs ins) := by
  constructor
  · intro safe M table callees
    refine ⟨fun path env ⟨empty, ins, valid, bound⟩ => ?_⟩
    subst empty bound
    refine Process.every_mono _ _ (fun outs returned => ?_) (fun _ stop => stop)
      (safe M table callees ins valid)
    rw [localDyns_eq_toDyns M table]
    exact toDyns_valid returned
  · intro assured M table callees ins valid
    refine Process.every_mono _ _ (fun outs returned => ?_) (fun _ stop => stop)
      ((assured M table callees).holds [] _ ⟨rfl, ins, valid, rfl⟩)
    rw [localDyns_eq_toDyns M table] at returned
    exact valid_of_toDyns returned

end

/-! ## Two programs over the same headers -/

section
variable {V : Vocabulary}

open Analysis in
/-- A second program that follows at a function of the first ends with a function of the same
header, which follows the analysis of the first's with no refusal and no place that differs,
after definitions that follow. -/
theorem Defs.followsFn_true {fns : List (FnHeader V)} {protocols : List (ProtocolHeader V)}
    {hdr : FnHeader V} {inputs : Names hdr.ins} {body : Fn V fns hdr inputs}
    {rest : Defs V ⟨fns, protocols⟩ → Bool} :
    ∀ {hs : Headers V} (defs' : Defs V hs) (headers : hs = ⟨hdr :: fns, protocols⟩),
      Defs.followsFn fns protocols hdr inputs body rest defs' headers = true →
      ∃ (inputs' : Names hdr.ins) (body' : Fn V fns hdr inputs') (ok' : FnConditions body')
        (rest' : Defs V ⟨fns, protocols⟩),
        HEq defs' (Defs.fn (hs := ⟨fns, protocols⟩) hdr inputs' body' ok' rest') ∧
          (follow (localFactRules V fns) (localSkelRules V fns) hdr.key none
            (analyse (localFactRules V fns) (localSkelRules V fns) hdr.key none inputs body)
            inputs' body').accepted = true ∧
          rest rest' = true
  | _, .nil, headers, _ => nomatch headers
  | _, .fn _ inputs' body' ok' rest', rfl, follows => by
      obtain ⟨accepted, restFollows⟩ := Bool.and_eq_true_iff.mp follows
      exact ⟨inputs', body', ok', rest', HEq.rfl, accepted, restFollows⟩
  | _, .protocol .., _, follows => nomatch follows

/-- A second program that follows at a protocol of the first ends with a protocol of the same
header, after definitions that follow. -/
theorem Defs.followsProtocol_true {fns : List (FnHeader V)} {protocols : List (ProtocolHeader V)}
    {hdr : ProtocolHeader V} {rest : Defs V ⟨fns, protocols⟩ → Bool} :
    ∀ {hs : Headers V} (defs' : Defs V hs) (headers : hs = ⟨fns, hdr :: protocols⟩),
      Defs.followsProtocol fns protocols hdr rest defs' headers = true →
      ∃ (inputs' : Names hdr.ins) (body' : Prot V ⟨fns, protocols⟩ hdr inputs')
        (ok' : ProtocolConditions hdr body') (rest' : Defs V ⟨fns, protocols⟩),
        HEq defs' (Defs.protocol (hs := ⟨fns, protocols⟩) hdr inputs' body' ok' rest') ∧
          rest rest' = true
  | _, .nil, headers, _ => nomatch headers
  | _, .fn .., _, follows => nomatch follows
  | _, .protocol _ inputs' body' ok' rest', rfl, follows =>
      ⟨inputs', body', ok', rest', HEq.rfl, follows⟩

end

end Zkc.Core
