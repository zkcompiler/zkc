module

public import Zkc.Core.Program.Term
public import Zkc.Core.Process.Process

@[expose] public section

/-!
The meaning of a term, once for every dialect.

A dialect's semantics says what its values are, what an operation does, how a guard, a
choice and a loop read their subject, and what marks an attempt. A value with its type
(`Semantics.Dyn`), and the values of a list with their types (`Semantics.dyns`), are what a
statement about values of any type speaks of. The process of a term is one fold over the term
with that; the three meanings (a function, a protocol, a role program) are this fold at three
semantics. Nothing that reads the structure of a term is written per dialect. A loop holds what
its iterations collect latest first (`HList.push`), and reverses it once where it becomes one
value (`Semantics.collected`), so that each iteration adds in constant time.

A value is read and bound by name: a variable is read from the environment (`Env.get`,
`Env.all`), and a binding binds its names to its values (`Env.extend`), a later name anew.
-/

namespace Zkc.Core

/-! ## Lists of values -/

namespace HList

/-- The one value of a list of one. -/
def single {α : Type} {F : α → Type} {a : α} : HList F [a] → F a
  | .cons v .nil => v

/-- No value collected yet, of each type. -/
def empties {α : Type} {V : α → Type} : (items : List α) → HList (fun a => List (V a)) items
  | [] => .nil
  | _ :: rest => .cons [] (empties rest)

/-- One more value of each type, before those collected: what a loop collects is held latest
first, and reversed once where it becomes one value (`Semantics.collected`). -/
def push {α : Type} {V : α → Type} :
    {items : List α} → HList (fun a => List (V a)) items → HList V items →
      HList (fun a => List (V a)) items
  | [], .nil, .nil => .nil
  | _ :: _, .cons vs rest, .cons v more => .cons (v :: vs) (rest.push more)

end HList


/-! ## The semantics of a dialect -/

/-- A value of one of the types, with its place among them. -/
inductive Pick {α : Type} (V : α → Type) : List α → Type where
  | here {a : α} {rest : List α} : V a → Pick V (a :: rest)
  | there {a : α} {rest : List α} : Pick V rest → Pick V (a :: rest)

/-- The payload of the alternative of a variant satisfies a predicate of its type. -/
def Pick.All {α : Type} {V : α → Type} (P : ∀ a, V a → Prop) :
    {items : List α} → Pick V items → Prop
  | _, .here v => P _ v
  | _, .there p => p.All P

structure Semantics (D : Dialect) where
  Val : D.Ty → Type
  S : Sig
  /-- What a stop carries. -/
  H : Type
  /-- An operation at its key, under the path of applications and iterations that reached
  it. -/
  op : ∀ {ins res : List D.Ty}, Key → D.Op ins res → List Frame → HList Val ins →
    Process S H (HList Val res)
  /-- Whether a condition holds. -/
  holds : ∀ {w : D.Who} {t : D.Ty}, D.Condition w t → Val t → Bool
  /-- The stop of a guard whose condition is false, at the guard's occurrence. -/
  stop : D.Who → Reason → Occurrence → H
  /-- The alternative of a variant, with its payload. -/
  pick : ∀ {w : D.Who} {t : D.Ty} {payloads : List D.Ty}, D.Alternatives w t payloads → Val t →
    Pick Val payloads
  count : ∀ {w : D.Who} {t : D.Ty}, D.Count w t → Val t → Nat
  /-- The iteration number as a value. -/
  index : (w : D.Who) → Nat → Val (D.index w)
  /-- The beginning of an attempt that `w` own, at its key under the path: the number of the
  attempt. It is `0` in the protocol as written. -/
  begin : (w : D.Who) → Key → List Frame → Process S H (Val (D.index w))
  /-- The end of the body of an attempt. -/
  settle : D.Who → Key → List Frame → Process S H Unit
  /-- The values that the iterations gave, as one value; of the size given, for a loop of a
  written number of iterations. -/
  collect : (size : Option Nat) → (a : D.Ty) → List (Val a) → Val (D.collected size a)

/-! ## Values with their types -/

section
variable {D : Dialect}

/-- A value of a semantics with its type. -/
abbrev Semantics.Dyn (sem : Semantics D) : Type := (τ : D.Ty) × sem.Val τ

/-- Values, each with its type. -/
def Semantics.dyns (sem : Semantics D) : {items : List D.Ty} → HList sem.Val items → List sem.Dyn
  | [], .nil => []
  | _ :: _, .cons v rest => ⟨_, v⟩ :: sem.dyns rest

/-- Values with their types are as many as the types. -/
theorem Semantics.dyns_length (sem : Semantics D) :
    ∀ {items : List D.Ty} (values : HList sem.Val items), (sem.dyns values).length = items.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (sem.dyns_length rest)

/-- Two values of one type that are equal with their type are equal. -/
theorem Semantics.dyn_inj (sem : Semantics D) {τ : D.Ty} {v v' : sem.Val τ}
    (same : (⟨τ, v⟩ : sem.Dyn) = ⟨τ, v'⟩) : v = v' :=
  eq_of_heq (Sigma.mk.inj same).2


/-- Values that are equal with their types are of the same types, and equal. -/
theorem Semantics.dyns_heq (sem : Semantics D) :
    ∀ {as bs : List D.Ty} (xs : HList sem.Val as) (ys : HList sem.Val bs),
      sem.dyns xs = sem.dyns ys → as = bs ∧ HEq xs ys
  | [], [], .nil, .nil, _ => ⟨rfl, HEq.rfl⟩
  | [], _ :: _, .nil, .cons _ _, same => by simp [Semantics.dyns] at same
  | _ :: _, [], .cons _ _, .nil, same => by simp [Semantics.dyns] at same
  | _ :: _, _ :: _, .cons x xs, .cons y ys, same => by
      simp only [Semantics.dyns, List.cons.injEq, Sigma.mk.injEq] at same
      obtain ⟨⟨sameType, sameValue⟩, others⟩ := same
      subst sameType
      cases eq_of_heq sameValue
      obtain ⟨sameTypes, sameValues⟩ := sem.dyns_heq xs ys others
      subst sameTypes
      cases eq_of_heq sameValues
      exact ⟨rfl, HEq.rfl⟩

/-- Values of the same types that are equal with their types are equal. -/
theorem Semantics.dyns_injective (sem : Semantics D) {items : List D.Ty}
    {values values' : HList sem.Val items} (same : sem.dyns values = sem.dyns values') :
    values = values' :=
  eq_of_heq (sem.dyns_heq values values' same).2

/-- Values of two lists, one after the other, with their types. -/
theorem Semantics.dyns_append (sem : Semantics D) :
    ∀ {as bs : List D.Ty} (xs : HList sem.Val as) (ys : HList sem.Val bs),
      sem.dyns (xs.append ys) = sem.dyns xs ++ sem.dyns ys
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons x xs, ys => by
      show (⟨_, x⟩ :: sem.dyns (xs.append ys)) = ⟨_, x⟩ :: (sem.dyns xs ++ sem.dyns ys)
      rw [sem.dyns_append xs ys]

/-- Values split after a prefix of their types, with their types: those of the prefix, then
those of the rest. -/
theorem Semantics.dyns_split (sem : Semantics D) {carried each : List D.Ty}
    (out : HList sem.Val (carried ++ each)) :
    sem.dyns out = sem.dyns (HList.split carried out).1 ++ sem.dyns (HList.split carried out).2 := by
  conv => lhs; rw [← split_append carried out]
  exact sem.dyns_append _ _

/-- A value at a position of values with their types has the type at that position. -/
theorem Semantics.dyns_typed (sem : Semantics D) :
    ∀ {items : List D.Ty} (vs : HList sem.Val items) (j : Nat) (d : sem.Dyn),
      (sem.dyns vs)[j]? = some d → items[j]? = some d.1
  | [], .nil, _, _, e => by simp [Semantics.dyns] at e
  | _ :: _, .cons v vs, j, d, e => by
      cases j with
      | zero =>
          simp only [Semantics.dyns, List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          rfl
      | succ j =>
          simp only [Semantics.dyns, List.getElem?_cons_succ] at e ⊢
          exact sem.dyns_typed vs j d e

end

/-- The collected values of each type, as the loop gives them: held latest first, each list is
reversed here, so that the value is of the iterations in order. -/
def Semantics.collected {D : Dialect} (sem : Semantics D) (size : Option Nat) :
    {each : List D.Ty} → HList (fun a => List (sem.Val a)) each →
      HList sem.Val (each.map (D.collected size))
  | [], .nil => .nil
  | a :: _, .cons vs rest => .cons (sem.collect size a vs.reverse) (sem.collected size rest)

/-- How often a loop runs, in an environment. -/
def Semantics.times {D : Dialect} (sem : Semantics D) {w : D.Who} {Γ : Ctx D.Ty} :
    Times D w Γ → Env sem.Val Γ → Nat
  | .fixed n, _ => n
  | .value count ok, env => sem.count ok (env.get count)

/-- The carried values and what was collected so far. -/
abbrev Semantics.LoopState {D : Dialect} (sem : Semantics D) (carried each : List D.Ty) : Type :=
  HList sem.Val carried × HList (fun a => List (sem.Val a)) each

/-- One iteration of a loop: the body, from the iteration number and the carried values bound to
the names of its inputs, under the frame of the iteration; it gives the carried values and adds
one value of each collected type. `run` is the process of the body. -/
def Semantics.loopStep {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {carried each : List D.Ty}
    (w : D.Who) (inputs : Names (D.index w :: carried))
    (run : List Frame → Env sem.Val (Γ.extend inputs) →
      Process sem.S sem.H (HList sem.Val (carried ++ each)))
    (key : Key) (path : List Frame) (env : Env sem.Val Γ) (i : Nat)
    (state : sem.LoopState carried each) : Process sem.S sem.H (sem.LoopState carried each) :=
  (run (path ++ [.iteration key i]) (env.extend inputs (.cons (sem.index w i) state.1))).bind
    fun out => .done ((HList.split carried out).1, state.2.push (HList.split carried out).2)


/-! ## The meaning -/

mutual
  /-- The process of a term in steps. -/
  def Term.denote {D : Dialect} (sem : Semantics D) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Frame → Env sem.Val Γ →
        Process sem.S sem.H (HList sem.Val outs)
    | _, _, .ret exit, _, env => .done (env.all exit)
    | _, _, .step key i results rest, path, env =>
        (Instr.denote sem key i path env).bind fun values =>
          rest.denote sem path (env.extend results values)
  /-- The process of what an instruction at a key runs: the values that it binds. -/
  def Instr.denote {D : Dialect} (sem : Semantics D) (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List Frame → Env sem.Val Γ →
        Process sem.S sem.H (HList sem.Val mid)
    | _, _, .op o operands, path, env => sem.op key o path (env.all operands)
    | _, _, .guard w c ok why, path, env =>
        bif sem.holds ok (env.get c) then .done .nil else .halt (sem.stop w why ⟨path, key⟩)
    | _, _, .choose _ c ok _ onTrue onFalse, path, env =>
        bif sem.holds ok (env.get c) then onTrue.denote sem path env
        else onFalse.denote sem path env
    | _, _, .cases _ x ok _ arms, path, env => arms.denote sem path env (sem.pick ok (env.get x))
    | _, _, .loop (each := each) w times _ initial inputs body, path, env =>
        (Process.iterate (sem.times times env)
          (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
          0 (env.all initial, HList.empties each)).bind fun state =>
          .done (state.1.append (sem.collected times.size state.2))
    | _, _, .block number body, path, env => body.denote sem (path ++ [.iteration key number]) env
    | _, _, .attempt w _ inputs body, path, env =>
        (sem.begin w key path).bind fun n =>
          (body.denote sem path (env.extend inputs (.cons n .nil))).bind fun mids =>
            (sem.settle w key path).bind fun _ => .done mids
  /-- The process of the region of the alternative that a variant is, its payload bound to the
  name of the region's input. -/
  def Arms.denote {D : Dialect} (sem : Semantics D) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List Frame →
        Env sem.Val Γ → Pick sem.Val payloads → Process sem.S sem.H (HList sem.Val mid)
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        arm.denote sem path (env.extend inputs (.cons v .nil))
    | _, _, _, .cons _ _ rest, path, env, .there p => rest.denote sem path env p
end

section
variable {D : Dialect} (sem : Semantics D)

/-! ## The equations -/

/-- An exit gives the values of its names. -/
theorem Term.denote_ret {Γ : Ctx D.Ty} {outs : List D.Ty} (exit : HList (Var Γ) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.ret exit).denote sem path env = .done (env.all exit) :=
  rfl

/-- **A step is its instruction's process, then the rest on what it returns**, bound to the names
of the step. -/
theorem Term.denote_step {Γ : Ctx D.Ty} {outs mid : List D.Ty} (key : Key)
    (i : Instr D Γ mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs) (path : List Frame) (env : Env sem.Val Γ) :
    (Term.step key i results rest).denote sem path env =
      (i.denote sem key path env).bind fun values =>
        rest.denote sem path (env.extend results values) :=
  rfl

/-- An operation runs the semantics' operation at its key on the values of its operands. -/
theorem Instr.denote_op {Γ : Ctx D.Ty} {ins res : List D.Ty} (key : Key) (o : D.Op ins res)
    (operands : HList (Var Γ) ins) (path : List Frame) (env : Env sem.Val Γ) :
    (Instr.op o operands).denote sem key path env = sem.op key o path (env.all operands) :=
  rfl

/-- A guard returns no value when its condition holds, and stops at its occurrence when it does
not. -/
theorem Instr.denote_guard {Γ : Ctx D.Ty} {t : D.Ty} (key : Key) (w : D.Who) (c : Var Γ t)
    (ok : D.Condition w t) (why : Reason) (path : List Frame) (env : Env sem.Val Γ) :
    (Instr.guard w c ok why).denote sem key path env =
      bif sem.holds ok (env.get c) then .done .nil else .halt (sem.stop w why ⟨path, key⟩) :=
  rfl

/-- A choice runs the region that its condition chooses. -/
theorem Instr.denote_choose {Γ : Ctx D.Ty} {mid : List D.Ty} {t : D.Ty} (key : Key)
    (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (onTrue onFalse : Term D Γ mid) (path : List Frame) (env : Env sem.Val Γ) :
    (Instr.choose w c ok gives onTrue onFalse).denote sem key path env =
      bif sem.holds ok (env.get c) then onTrue.denote sem path env
      else onFalse.denote sem path env :=
  rfl

/-- A case analysis runs its arms at the alternative that its subject is. -/
theorem Instr.denote_cases {Γ : Ctx D.Ty} {mid payloads : List D.Ty} {t : D.Ty} (key : Key)
    (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Instr.cases w x ok gives arms).denote sem key path env =
      arms.denote sem path env (sem.pick ok (env.get x)) :=
  rfl

/-- A loop iterates its body, from its initial carried values and nothing collected, as often as
its count says, and returns the last carried values and what was collected. -/
theorem Instr.denote_loop {Γ : Ctx D.Ty} {carried each : List D.Ty} (key : Key) (w : D.Who)
    (times : Times D w Γ) (gives : ∀ a, a ∈ carried ++ each → D.Gives w a)
    (initial : HList (Var Γ) carried) (inputs : Names (D.index w :: carried))
    (body : Term D (Γ.extend inputs) (carried ++ each)) (path : List Frame)
    (env : Env sem.Val Γ) :
    (Instr.loop w times gives initial inputs body).denote sem key path env =
      (Process.iterate (sem.times times env)
        (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
        0 (env.all initial, HList.empties each)).bind fun state =>
        .done (state.1.append (sem.collected times.size state.2)) :=
  rfl

/-- A block runs its body under its frame. -/
theorem Instr.denote_block {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (number : Nat)
    (body : Term D Γ mid) (path : List Frame) (env : Env sem.Val Γ) :
    (Instr.block number body).denote sem key path env =
      body.denote sem (path ++ [.iteration key number]) env :=
  rfl

/-- An attempt begins, runs its body with the number of the attempt, ends, and returns what the
body returned. -/
theorem Instr.denote_attempt {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (w : D.Who)
    (owns : D.Attempt w) (inputs : Names [D.index w]) (body : Term D (Γ.extend inputs) mid)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Instr.attempt w owns inputs body).denote sem key path env =
      (sem.begin w key path).bind fun n =>
        (body.denote sem path (env.extend inputs (.cons n .nil))).bind fun mids =>
          (sem.settle w key path).bind fun _ => .done mids :=
  rfl

/-- A case analysis without an alternative has no variant to run on: what its arms run at a pick
is any process. -/
theorem Arms.denote_nil {Γ : Ctx D.Ty} {mid : List D.Ty} (path : List Frame)
    (env : Env sem.Val Γ) (pick : Pick sem.Val []) (p : Process sem.S sem.H (HList sem.Val mid)) :
    (Arms.nil : Arms D Γ mid []).denote sem path env pick = p :=
  nomatch pick

/-- The arms of a case analysis run the first arm, on its payload, at the first alternative, and
the other arms at another. -/
theorem Arms.denote_cons {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Term D (Γ.extend inputs) mid)
    (rest : Arms D Γ mid payloads) (path : List Frame) (env : Env sem.Val Γ)
    (pick : Pick sem.Val (payload :: payloads)) :
    (Arms.cons inputs arm rest).denote sem path env pick =
      match pick with
      | .here v => arm.denote sem path (env.extend inputs (.cons v .nil))
      | .there p => rest.denote sem path env p := by
  cases pick <;> rfl

/-! ## Equations for instruction builders -/

theorem Term.denote_op {Γ outs ins res} (key : Key) (o : D.Op ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.op key o operands results rest).denote sem path env =
        (sem.op key o path (env.all operands)).bind fun values =>
          rest.denote sem path (env.extend results values) := rfl

theorem Term.denote_guard {Γ outs t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (why : Reason) (rest : Term D Γ outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.guard key w c ok why rest).denote sem path env =
        bif sem.holds ok (env.get c) then rest.denote sem path env
        else .halt (sem.stop w why ⟨path, key⟩) := by
  change ((bif sem.holds ok (env.get c) then Process.done .nil else
    .halt (sem.stop w why ⟨path, key⟩)).bind fun vs =>
      rest.denote sem path (env.extend (.nil : Names ([] : List D.Ty)) vs)) = _
  cases sem.holds ok (env.get c) <;> rfl

theorem Term.denote_choose {Γ outs mid t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid)
    (results : Names mid) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.choose key w c ok gives onTrue onFalse results rest).denote sem path env =
        (bif sem.holds ok (env.get c) then onTrue.denote sem path env
          else onFalse.denote sem path env).bind fun mids =>
          rest.denote sem path (env.extend results mids) := rfl

theorem Term.denote_cases {Γ outs mid t payloads} (key : Key) (w : D.Who) (x : Var Γ t)
    (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (arms : Arms D Γ mid payloads)
    (results : Names mid) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.cases key w x ok gives arms results rest).denote sem path env =
        (arms.denote sem path env (sem.pick ok (env.get x))).bind fun mids =>
          rest.denote sem path (env.extend results mids) := rfl

theorem Term.denote_loop {Γ outs carried each} (key : Key) (w : D.Who) (times : Times D w Γ)
    (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
    (inputs : Names (D.index w :: carried))
    (body : Term D (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (D.collected times.size)))
    (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.loop key w times gives initial inputs body results rest).denote sem path env =
        (Process.iterate (sem.times times env)
          (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
          0 (env.all initial, HList.empties each)).bind fun state =>
          rest.denote sem path
            (env.extend results (state.1.append (sem.collected times.size state.2))) := by
  simp only [Term.loop, Term.denote_step, Instr.denote_loop, Process.bind_assoc, Process.bind]

theorem Term.denote_block {Γ outs mid} (key : Key) (number : Nat) (body : Term D Γ mid)
    (results : Names mid) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.block key number body results rest).denote sem path env =
        (body.denote sem (path ++ [.iteration key number]) env).bind fun mids =>
          rest.denote sem path (env.extend results mids) := rfl

theorem Term.denote_attempt {Γ outs mid} (key : Key) (w : D.Who) (owns : D.Attempt w)
    (inputs : Names [D.index w]) (body : Term D (Γ.extend inputs) mid)
    (results : Names mid) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.attempt key w owns inputs body results rest).denote sem path env =
        (sem.begin w key path).bind fun n =>
          (body.denote sem path (env.extend inputs (.cons n .nil))).bind fun mids =>
            (sem.settle w key path).bind fun _ =>
              rest.denote sem path (env.extend results mids) := by
  simp only [Term.attempt, Term.denote_step, Instr.denote_attempt, Process.bind_assoc, Process.bind]

end

section
variable {D : Dialect}

/-- One iteration of a loop, from the process of its body at an iteration number and carried
values: what `Semantics.loopStep` is, without the environment. -/
def Semantics.stepOf (sem : Semantics D) {carried each : List D.Ty}
    (bodyOf : Nat → HList sem.Val carried → Process sem.S sem.H (HList sem.Val (carried ++ each)))
    (i : Nat) (state : sem.LoopState carried each) :
    Process sem.S sem.H (sem.LoopState carried each) :=
  (bodyOf i state.1).bind fun out =>
    .done ((HList.split carried out).1, state.2.push (HList.split carried out).2)

end

end Zkc.Core
