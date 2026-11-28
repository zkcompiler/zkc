module

public import ZkcFormal.Form.Computation
public import Zkc.Core.Evidence.EarlierMeaning

@[expose] public section

/-!
The computation of a stored program, by recursion on its term.

`term` gives, for a term of any dialect, the computation of its process: a `for` over the
iterations of a loop, `if` at a guard and at a choice, the monad's bind between an instruction
and the rest, and at an operation what the dialect's `Operations` give. `term_agrees` is the one
theorem: where the operations read as the dialect's own, the reading of the term's process is
that computation. It is proved once, by induction on the term; a program gets its computation by
applying it (`storedRole`, `storedFunction`), with a proof whose size does not grow with the
program.

An instruction's computation is a `Fragment`: a computation, a value, or a computation with what
is made of its result. The distinction is kept so that a value is passed on without a bind, and a
query's reply is bound once and read under its own binder.

The operations of a role name every other definition as a member of the whole program: a
function that the role calls is `fnMeaning M p` at the program's member, and a protocol that it
applies is `roleMeaning M p` at the program's member, renamed. A definition has one meaning
whichever definition applies it (`Zkc.Core.Defs.rTable_protocolBefore`), so the computations of
two callers name one callee by one term.
-/

namespace ZkcFormal.Form
open Zkc.Core ProbabilisticProcess Reading

variable {S : Sig} {H A B : Type}

/-- What an instruction gives: a computation, a value, or a computation with what is made of its
result. -/
inductive Fragment (S : Sig) (H A : Type) where
  | ready (p : Comp S H A)
  | value (a : A)
  | action {X : Type} (x : Comp S H X) (f : X → A)

/-- A fragment followed by a computation of its result. -/
def Fragment.next (p : Fragment S H A) (k : A → Comp S H B) : Comp S H B :=
  match p with
  | .ready x => x >>= k
  | .value a => k a
  | .action x f => x >>= fun v => k (f v)

/-- The computation of a fragment. -/
def Fragment.eval (p : Fragment S H A) : Comp S H A :=
  match p with
  | .ready x => x
  | .value a => pure a
  | .action x f => x >>= fun v => pure (f v)

theorem Fragment.next_eq (p : Fragment S H A) (k : A → Comp S H B) : p.eval >>= k = p.next k := by
  cases p <;> simp [Fragment.eval, Fragment.next]

/-- A computation as a fragment. -/
def atomic (p : Comp S H A) : Fragment S H A := .ready p

theorem eval_atomic (p : Comp S H A) : (atomic p).eval = p := rfl

/-! ## The computation of a term -/

section
variable {D : Dialect} (s : Semantics D)

/-- What the operations of a dialect give, each as a fragment. -/
abbrev Operations := ∀ {ins res : List D.Ty}, Key → D.Op ins res → List Frame →
  HList s.Val ins → Fragment s.S s.H (HList s.Val res)

variable (op : Operations s)

mutual
  /-- The computation of a term, at a path and in an environment. -/
  def term : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Frame →
      Env s.Val Γ → Fragment s.S s.H (HList s.Val outs)
    | _, _, .ret exit, _, env => .value (env.all exit)
    | _, _, .step key i ns rest, path, env =>
        atomic <| (instr key i path env).next fun vs => (term rest path (extend env ns vs)).eval
  /-- The computation of an instruction at its key. -/
  def instr (key : Key) : {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List Frame →
      Env s.Val Γ → Fragment s.S s.H (HList s.Val mid)
    | _, _, .op o args, path, env => op key o path (env.all args)
    | _, _, .guard w c ok why, path, env =>
        atomic <| if s.holds ok (env.get c) then pure .nil else throw (s.stop w why ⟨path, key⟩)
    | _, _, .choose _ c ok _ t f, path, env =>
        atomic <| if s.holds ok (env.get c) then (term t path env).eval else (term f path env).eval
    | _, _, .cases _ x ok _ alts, path, env => arms alts path env (s.pick ok (env.get x))
    | _, _, .loop (each := each) w times _ initial ns body, path, env => atomic <| do
        let state ← forIn (List.range' 0 (s.times times env))
          ((env.all initial, HList.empties each) : s.LoopState _ _) fun j state =>
            ForInStep.yield <$> (do
              let out ← (term body (path ++ [.iteration key j])
                (extend env ns (.cons (s.index w j) state.1))).eval
              let parts := HList.split _ out
              pure (parts.1, state.2.push parts.2))
        pure (state.1.append (s.collected times.size state.2))
    | _, _, .block n body, path, env => term body (path ++ [.iteration key n]) env
    | _, _, .attempt w _ ns body, path, env => atomic <| do
        let n ← read (s.begin w key path)
        let vs ← (term body path (extend env ns (.cons n .nil))).eval
        let _ ← read (s.settle w key path)
        pure vs
  /-- The computation of the arm that a value of a variant takes. -/
  def arms : {Γ : Ctx D.Ty} → {mid ps : List D.Ty} → Arms D Γ mid ps → List Frame →
      Env s.Val Γ → Pick s.Val ps → Fragment s.S s.H (HList s.Val mid)
    | _, _, _, .nil, _, _, p => nomatch p
    | _, _, _, .cons ns t rest, path, env, p =>
        atomic <| branch p (fun x => (term t path (extend env ns (.cons x .nil))).eval)
          (fun q => (arms rest path env q).eval)
end

variable (reads : ∀ {ins res} (k) (o : D.Op ins res) (path vs),
  read (s.op k o path vs) = (op k o path vs).eval)
include reads

/-- **The reading of a term's process is its computation**, where the operations read as the
dialect's. -/
theorem term_agrees {Γ outs} (t : Term D Γ outs) :
    ∀ path (env : Env s.Val Γ), read (t.denote s path env) = (term s op t path env).eval := by
  induction t using Term.rec
    (motive_2 := fun _ _ i => ∀ k path env,
      read (i.denote s k path env) = (instr s op k i path env).eval)
    (motive_3 := fun _ _ _ a => ∀ path env p,
      read (a.denote s path env p) = (arms s op a path env p).eval) with
  | ret => intros; rfl
  | step _ _ _ _ hi hr =>
    intros
    rw [Term.denote_step, term, eval_atomic, read_bind, hi, ← Fragment.next_eq]
    apply bind_congr
    intro vs
    rw [hr, extend_eq]
  | op o => apply reads
  | guard => rw [Instr.denote_guard, read_cond, instr, eval_atomic]; rfl
  | choose _ _ _ _ _ _ ht hf => rw [Instr.denote_choose, read_cond, instr, eval_atomic, ht, hf]
  | cases _ _ _ _ _ ha => simpa only [instr, eval_atomic, Instr.denote_cases] using ha _ _ _
  | block _ _ ht => simpa only [instr, eval_atomic, Instr.denote_block] using ht _ _
  | attempt _ _ _ _ ht =>
    simp only [Instr.denote_attempt, instr, eval_atomic, read_bind, ht, read_done, extend_eq]
  | loop _ _ _ _ _ _ ht =>
    rw [Instr.denote_loop, instr, eval_atomic, read_bind, read_iterate]
    congr 1
    apply congrArg (forIn _ _)
    funext j state
    simp only [Semantics.loopStep, read_bind, ht, read_done, extend_eq]
  | nil => rename_i p; exact nomatch p
  | cons ns t rest ht hr =>
    rename_i path env p
    cases rest with
    | nil =>
      cases p with
      | here => simpa only [Arms.denote, arms, eval_atomic, branch, onlyPayload, extend_eq] using ht _ _
      | there q => exact nomatch q
    | cons =>
      cases p with
      | here => simpa only [Arms.denote, arms, eval_atomic, branch, splitPick, extend_eq] using ht _ _
      | there => simpa only [Arms.denote, arms, eval_atomic, branch, splitPick] using hr _ _ _

end

/-! ## The operations of a function and of a role -/

variable {V : Vocabulary} (M : Model V)

/-- A local process without effects as a fragment: its value, or its stop. -/
def fromLocal {A : Type} : Local A → Fragment NoSig Stop A
  | .done a => .value a
  | .halt e => atomic (throw e)
  | .call o _ => nomatch o

theorem fromLocal_reads {A : Type} (q : Local A) : read q = (fromLocal q).eval := by
  cases q with
  | done => rfl
  | halt => rfl
  | call o => exact nomatch o

/-- An operation of the core's own, as a fragment: the element of a sequence at a position is a
value or a stop; a slice is its own process read; every other is its value or its stop. -/
def ownedFragment : {ins outs : List V.Ty} → OwnedOp V ins outs → HList M.Val ins →
    Fragment NoSig Stop (HList M.Val outs)
  | _, _, .seqAt item _ _, vs =>
      atomic (optionE ((headV vs : List (M.Val item))[headV (tailV vs)]?)
        (fun x => HList.cons x HList.nil))
  | _, _, .seqSlice item size result h, vs =>
      atomic (read (ownedOp M (.seqSlice item size result h) vs))
  | _, _, o, vs => fromLocal (ownedOp M o vs)

section
variable {fns : List (FnHeader V)} (table : FnTable M fns)
  (called : ∀ {h : FnHeader V}, Member fns h → HList M.Val h.ins → Local (HList M.Val h.outs))

include table in
theorem owned_reads {ins outs} (o : OwnedOp V ins outs) (vs : HList M.Val ins) :
    read (ownedOp M o vs) = (ownedFragment M o vs).eval := by
  cases o with
  | seqAt item size h =>
    cases vs with | cons v tail =>
      cases tail with | cons i tail =>
        cases tail
        exact read_seqAt table item size h v i
  | seqSlice => rfl
  | _ => apply fromLocal_reads

/-- A local operation as a fragment. A function that is called is read as `called` gives it. -/
def localFragment : {ins outs : List V.Ty} → LocalOp V fns ins outs →
    HList M.Val ins → Fragment NoSig Stop (HList M.Val outs)
  | _, _, .row k sig h, vs => atomic (optionE (M.apply k sig h vs) id)
  | _, _, .literal t data h, _ => .value (.cons (Ty.readLiteral M t data h) .nil)
  | _, _, .owned o, vs => ownedFragment M o vs
  | _, _, .call m, vs => atomic (read (called m vs))

variable (same : ∀ {h : FnHeader V} (m : Member fns h) (vs : HList M.Val h.ins),
  table h m vs = called m vs)
include same

theorem local_reads {ins outs} (o : LocalOp V fns ins outs) (vs : HList M.Val ins) :
    read (localOp M table o vs) = (localFragment M called o vs).eval := by
  cases o with
  | row => rw [localFragment, eval_atomic]; apply read_row
  | literal => rfl
  | owned => apply owned_reads M table
  | call m => rw [localFragment, eval_atomic, ← same m vs]; rfl

end

/-- A fragment without effects among a role's effects, with what is made of its result. -/
def computed {S : Sig} {A B : Type} (f : A → B) : Fragment NoSig Stop A → Fragment S Stop B
  | .ready x => .ready (liftEmpty S id x >>= fun v => pure (f v))
  | .value x => .value (f x)
  | .action x g => .ready
      (liftEmpty S id ((Fragment.action x g : Fragment NoSig Stop A).eval) >>= fun v => pure (f v))

theorem computed_reads {S : Sig} {A B : Type} (f : A → B) (q : Fragment NoSig Stop A) :
    (liftEmpty S id q.eval >>= fun v => pure (f v)) = (computed f q).eval := by
  cases q <;> rfl

section
variable {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
  (called : ∀ {h : FnHeader V}, Member hs.fns h → HList M.Val h.ins → Local (HList M.Val h.outs))
  (applied : ∀ {h : ProtocolHeader V}, Member hs.protocols h → (j : Role) → List Frame →
    HList (RV M j) h.ins → Program M (HList (RV M j) h.outs))

/-- An operation of a role as a fragment. A value given, got, drawn or heard is a query with
what the role keeps of the reply; a computation is a local fragment among the role's effects; an
application is the callee's computation, as `applied` gives its process, with the callee's roles
renamed and its results carried back. -/
def roleFragment (r : Role) (key : Key) : {ins outs : List (LTy V)} →
    RoleOp V hs r ins outs → List Frame → HList (RV M r) ins →
    Fragment (RSig M) Stop (HList (RV M r) outs)
  | _, _, .compute R o _ types _ here, _, vs =>
      computed (fun outs => hideAll M r (HList.located M R outs))
        (localFragment M called o (computeArgs M types (revealAll M here vs)))
  | _, _, .absent _ out, _, _ => .value (nothings M out)
  | _, _, .give (τ := τ) (H := H) kind getters here, path, .cons v .nil =>
      .action (ask (RSig M) Stop
          (.give kind getters ⟨path, key⟩ τ (reveal M (a := ⟨τ, H⟩) here v))) fun _ =>
        .cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here v)) .nil
  | _, _, .get τ H kind giver getters _, path, _ =>
      .action (ask (RSig M) Stop (.get kind giver ⟨path, key⟩ τ)) fun x =>
        .cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ x) .nil
  | _, _, .keep _ same, _, .cons v .nil => .value (.cons (carry M same v) .nil)
  | _, _, .own kind hearers operands τ _ here, path, vs =>
      .action (ask (RSig M) Stop (.own kind hearers ⟨path, key⟩ (operands.map LTy.ty)
          (HList.ofLocated M (revealAll M here vs)) τ)) fun x =>
        .cons (hide M r ⟨τ, Holders.ofList (r :: hearers)⟩ x) .nil
  | _, _, .hear kind owner hearers τ _, path, _ =>
      .action (ask (RSig M) Stop (.hear kind owner ⟨path, key⟩ τ)) fun x =>
        .cons (hide M r ⟨τ, Holders.ofList (owner :: hearers)⟩ x) .nil
  | _, _, .apply callee roles distinct _ _ fits, path, vs =>
      let ρ := RoleMap.ofList roles distinct
      Fragment.ready (renamed ρ.to (read (applied callee (ρ.back r) (path ++ [.application key])
        (enterAll M ρ r (fitAllRV M fits vs)))) >>= fun outs => pure (leaveAll M ρ r outs))

variable (sameFunction : ∀ {h : FnHeader V} (m : Member hs.fns h) (vs : HList M.Val h.ins),
    fnTable h m vs = called m vs)
  (sameProtocol : ∀ {h : ProtocolHeader V} (m : Member hs.protocols h) (j : Role)
    (path : List Frame) (ins : HList (RV M j) h.ins), rTable h m j path ins = applied m j path ins)
include sameFunction sameProtocol

theorem role_reads (r : Role) (k : Key) {ins outs} (o : RoleOp V hs r ins outs) (path)
    (vs : HList (RV M r) ins) :
    read (roleOp M r fnTable rTable k o path vs) =
      (roleFragment M called applied r k o path vs).eval := by
  cases o with
  | absent | get | own | hear => rfl
  | keep | give => cases vs with | cons _ tail => cases tail; rfl
  | compute =>
    simp only [roleOp, roleFragment, Process.map_eq_bind, read_bind, read_liftLocal,
      local_reads M fnTable called sameFunction, read_done, computed_reads]
  | apply callee =>
    simp only [roleOp, roleFragment, Process.map_eq_bind, read_bind, read_mapR, sameProtocol,
      read_done, Fragment.eval]

end

/-! ## A stored definition -/

variable (p : Typed V)

/-- The definitions before a protocol of a program, as a program. -/
abbrev beforeProtocol {hdr : ProtocolHeader V} (x : Member p.headers.protocols hdr) : Typed V :=
  let e := p.defs.protocolEntry p.distinct x
  ⟨e.earlier, e.definitions, e.distinct⟩

/-- The operations of a role of a protocol of a program: every function that it calls and every
protocol that it applies is named as a member of the program. -/
abbrev roleOperations {hdr : ProtocolHeader V} (x : Member p.headers.protocols hdr) (r : Role) :
    Operations (roleSem M r (Defs.fnTable M (p.defs.protocolEntry p.distinct x).definitions)
      (Defs.rTable M (p.defs.protocolEntry p.distinct x).definitions)) :=
  fun k o path vs =>
    roleFragment M (fun m vs => fnMeaning M p (p.defs.functionBefore p.distinct x m) vs)
      (fun m j path ins => roleMeaning M p (p.defs.protocolBefore p.distinct x m) j path ins)
      r k o path vs

/-- **The computation of a role of a stored protocol**: the reading of the role's process is the
computation of the projection of the protocol's body to the role, in which every other
definition is named as a member of the program. -/
theorem storedRole {hdr : ProtocolHeader V} (x : Member p.headers.protocols hdr) (r : Role)
    (path : List Frame) (ins : HList (RV M r) hdr.ins) :
    read (roleMeaning M p x r path ins) =
      (term _ (roleOperations M p x r) (project r (p.defs.protocolEntry p.distinct x).body) path
        (extend Env.empty (p.defs.protocolEntry p.distinct x).inputs ins)).eval := by
  rw [roleMeaning_entry, extend_eq]
  exact term_agrees _ (roleOperations M p x r)
    (fun k o path vs => role_reads M _ _ _ _
      (fun m vs => by
        unfold fnMeaning
        rw [Defs.fnTable_functionBefore])
      (fun m j path ins => by
        unfold roleMeaning
        rw [Defs.rTable_protocolBefore])
      r k o path vs) _ path _

/-- The operations of a function of a program: every function that it calls is named as a member
of the program. -/
abbrev functionOperations {hdr : FnHeader V} (x : Member p.headers.fns hdr) :
    Operations (localSem M _ (Defs.fnTable M
      (p.defs.functionEntry (List.nodup_append.mp p.distinct).1 x).definitions)) :=
  fun _ o _ vs =>
    localFragment M
      (fun m vs => fnMeaning M p
        (p.defs.functionBeforeFunction (List.nodup_append.mp p.distinct).1 x m) vs) o vs

/-- **The computation of a stored function**: the reading of the function's process is the
computation of its body, in which every function that it calls is named as a member of the
program. -/
theorem storedFunction {hdr : FnHeader V} (x : Member p.headers.fns hdr)
    (ins : HList M.Val hdr.ins) :
    read (fnMeaning M p x ins) =
      (term _ (functionOperations M p x)
        (p.defs.functionEntry (List.nodup_append.mp p.distinct).1 x).body []
        (extend Env.empty (p.defs.functionEntry (List.nodup_append.mp p.distinct).1 x).inputs
          ins)).eval := by
  rw [fnMeaning_entry, extend_eq]
  exact term_agrees _ (functionOperations M p x)
    (fun _ o _ vs => local_reads M _ _
      (fun m vs => by
        unfold fnMeaning
        rw [Defs.fnTable_functionBeforeFunction]) o vs) _ [] _

end ZkcFormal.Form
