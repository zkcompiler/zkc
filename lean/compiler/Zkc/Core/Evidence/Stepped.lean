module

public import Zkc.Core.Evidence.Subject
public import Zkc.Core.Meaning.Stepped

@[expose] public section

/-!
The rules of the term in steps, for any dialect, semantics and permitted replies: what an
instruction runs is its subject, and a property on every path is said once for a step and once
for each kind of instruction.

Every instruction runs something before the rest: its subject (`Stepped.Instr.subject`), what it
runs as a process of the path and the environment. A step's process is its subject's process
bound to the rest (`Stepped.Term.step_subject`), so the two rules for the continuation of
`Evidence/Subject.lean` apply to every kind of instruction: a subject that satisfies a contract
(`Stepped.Term.step_satisfies`) and a subject that yields a function (`Stepped.Term.step_yields`).
The subject of an operation is `Subject.op` (`Stepped.Instr.subject_op`), and the subject of a
block is `Subject.block` of its body as a term (`Stepped.Instr.subject_block`).

A property on every path of a step is the instruction's process on every path with, at each
return, the rest on every path (`Stepped.Term.every_step`). For each kind of instruction, a
property on every path of what it runs is said in terms of its condition and its regions: a guard
(`Stepped.Instr.every_guard`) and a choice (`Stepped.Instr.every_choose`) by the value of the
condition, a case analysis by its arms at the alternative of its subject
(`Stepped.Instr.every_cases`, with the arms' `Stepped.Arms.every_here` and
`Stepped.Arms.every_there`), a loop by an invariant over its iterations, kept by its body from each
iteration below its count to the next (`Stepped.Instr.every_loop`), a block by its body under its
frame (`Stepped.Instr.every_block`), and an attempt by its beginning, its body and its end
(`Stepped.Instr.every_attempt`). A prefix filled with a term has a property on every path exactly
when the prefix's process ends, on every path, in environments from which the term has it
(`Prefix.every_fill`, and in the form of an intermediate property of those environments,
`Prefix.every_fill_of_run`).

Nothing here unfolds the mutual recursion of the meaning: every proof uses the equations of
`Meaning/Stepped.lean`, and the rule of a loop also unfolds one iteration (`Semantics.loopStep`).
-/

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)

/-! ## The subject of an instruction -/

/-- What an instruction at a key runs before the rest: its process, as a function of the path and
the environment. -/
def Stepped.Instr.subject {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key)
    (i : Stepped.Instr D Γ mid) : Subject sem Γ mid :=
  fun path env => i.denote sem key path env

/-- **A step's process is its subject's process, then the rest** on what it returns. -/
theorem Stepped.Term.step_subject {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Stepped.Instr D Γ mid) (results : Names mid)
    (rest : Stepped.Term D (Γ.extend results) outs) (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Term.step key i results rest).denote sem path env =
      (Stepped.Instr.subject sem key i path env).bind fun values =>
        rest.denote sem path (env.extend results values) :=
  Stepped.Term.denote_step sem key i results rest path env

/-- The subject of an operation is the operation on its operands. -/
theorem Stepped.Instr.subject_op {Γ : Ctx D.Ty} {ins res : List D.Ty} (key : Key)
    (o : D.Op ins res) (operands : HList (Var Γ) ins) :
    Stepped.Instr.subject sem key (.op o operands) = Subject.op sem key o operands := by
  funext path env
  exact Stepped.Instr.denote_op sem key o operands path env

/-- The subject of a block is the subject of a block whose body is its body as a term: its body,
under the block's frame. -/
theorem Stepped.Instr.subject_block {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (number : Nat)
    (body : Stepped.Term D Γ mid) :
    Stepped.Instr.subject sem key (.block number body) =
      Subject.block sem key number body.toTerm := by
  funext path env
  exact (Stepped.Instr.denote_block sem key number body path env).trans
    (Stepped.Term.denote_toTerm sem body _ env).symm

/-- **A step whose subject satisfies a contract**: the step satisfies `returns` and `halts` when the
rest does on every result that the contract promises and the contract's stops are among
`halts`. It is `Term.op_satisfies` for every kind of instruction. -/
theorem Stepped.Term.step_satisfies {Γ : Ctx D.Ty} {mid outs : List D.Ty} {key : Key}
    {i : Stepped.Instr D Γ mid} {entry : Entry sem Γ}
    {post : Env sem.Val Γ → HList sem.Val mid → Prop} {stops : sem.H → Prop}
    (satisfies : (Stepped.Instr.subject sem key i).Satisfies sem permitted entry post stops)
    (results : Names mid) (rest : Stepped.Term D (Γ.extend results) outs)
    (returns : HList sem.Val outs → Prop) (halts : sem.H → Prop) (path : List Frame)
    (env : Env sem.Val Γ) (authorized : entry path env)
    (continues : ∀ values, post env values →
      (rest.denote sem path (env.extend results values)).Every permitted returns halts)
    (stopped : ∀ stop, stops stop → halts stop) :
    ((Stepped.Term.step key i results rest).denote sem path env).Every permitted returns halts := by
  rw [Stepped.Term.step_subject]
  exact satisfies.then sem permitted
    (fun path env values => rest.denote sem path (env.extend results values)) returns halts path
    env authorized continues stopped

/-- **A step whose subject yields a function** is the rest on what the function gives. It is
`Term.op_yields` for every kind of instruction. -/
theorem Stepped.Term.step_yields {Γ : Ctx D.Ty} {mid outs : List D.Ty} {key : Key}
    {i : Stepped.Instr D Γ mid} {entry : Entry sem Γ}
    {compute : Env sem.Val Γ → HList sem.Val mid}
    (yields : (Stepped.Instr.subject sem key i).Yields sem entry compute)
    (results : Names mid) (rest : Stepped.Term D (Γ.extend results) outs) (path : List Frame)
    (env : Env sem.Val Γ) (authorized : entry path env) :
    (Stepped.Term.step key i results rest).denote sem path env =
      rest.denote sem path (env.extend results (compute env)) := by
  rw [Stepped.Term.step_subject]
  exact yields.then sem (fun values => rest.denote sem path (env.extend results values)) path env
    authorized

/-! ## On every path -/

/-- **A property on every path of a step** is the instruction's process on every path with, at
each return, the rest on every path. -/
theorem Stepped.Term.every_step {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Stepped.Instr D Γ mid) (results : Names mid)
    (rest : Stepped.Term D (Γ.extend results) outs) (path : List Frame) (env : Env sem.Val Γ)
    (returns : HList sem.Val outs → Prop) (halts : sem.H → Prop) :
    ((Stepped.Term.step key i results rest).denote sem path env).Every permitted returns halts ↔
      (i.denote sem key path env).Every permitted
        (fun values => (rest.denote sem path (env.extend results values)).Every permitted returns
          halts) halts := by
  rw [Stepped.Term.denote_step]
  exact Process.every_bind _ _ _ _ _

/-- A guard has a property on every path exactly when, where its condition holds, its return of
no value has it, and where it does not, its stop has it. -/
theorem Stepped.Instr.every_guard {Γ : Ctx D.Ty} {t : D.Ty} (key : Key) (w : D.Who) (c : Var Γ t)
    (ok : D.Condition w t) (why : Reason) (path : List Frame) (env : Env sem.Val Γ)
    (returns : HList sem.Val [] → Prop) (halts : sem.H → Prop) :
    ((Stepped.Instr.guard w c ok why).denote sem key path env).Every permitted returns halts ↔
      (sem.holds ok (env.get c) = true → returns .nil) ∧
        (sem.holds ok (env.get c) = false → halts (sem.stop w why ⟨path, key⟩)) := by
  rw [Stepped.Instr.denote_guard]
  cases sem.holds ok (env.get c) with
  | false =>
      exact ⟨fun stop => ⟨(fun never => nomatch never), fun _ => stop⟩, fun both => both.2 rfl⟩
  | true =>
      exact ⟨fun done => ⟨fun _ => done, (fun never => nomatch never)⟩, fun both => both.1 rfl⟩

/-- **A choice** has a property on every path exactly when, where its condition holds, its first
region has it, and where it does not, its second. -/
theorem Stepped.Instr.every_choose {Γ : Ctx D.Ty} {mid : List D.Ty} {t : D.Ty} (key : Key)
    (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (onTrue onFalse : Stepped.Term D Γ mid) (path : List Frame) (env : Env sem.Val Γ)
    (returns : HList sem.Val mid → Prop) (halts : sem.H → Prop) :
    ((Stepped.Instr.choose w c ok gives onTrue onFalse).denote sem key path env).Every permitted
        returns halts ↔
      (sem.holds ok (env.get c) = true →
          (onTrue.denote sem path env).Every permitted returns halts) ∧
        (sem.holds ok (env.get c) = false →
          (onFalse.denote sem path env).Every permitted returns halts) := by
  rw [Stepped.Instr.denote_choose]
  cases sem.holds ok (env.get c) with
  | false =>
      exact ⟨fun second => ⟨(fun never => nomatch never), fun _ => second⟩, fun both => both.2 rfl⟩
  | true =>
      exact ⟨fun first => ⟨fun _ => first, (fun never => nomatch never)⟩, fun both => both.1 rfl⟩

/-- **A case analysis** has a property on every path exactly when its arms have it at the
alternative of its subject. -/
theorem Stepped.Instr.every_cases {Γ : Ctx D.Ty} {mid payloads : List D.Ty} {t : D.Ty} (key : Key)
    (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Stepped.Arms D Γ mid payloads)
    (path : List Frame) (env : Env sem.Val Γ) (returns : HList sem.Val mid → Prop)
    (halts : sem.H → Prop) :
    ((Stepped.Instr.cases w x ok gives arms).denote sem key path env).Every permitted returns
        halts ↔
      (arms.denote sem path env (sem.pick ok (env.get x))).Every permitted returns halts := by
  rw [Stepped.Instr.denote_cases]

/-- At the first alternative, the arms have a property on every path exactly when the first arm
has it on the payload. -/
theorem Stepped.Arms.every_here {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Stepped.Term D (Γ.extend inputs) mid)
    (rest : Stepped.Arms D Γ mid payloads) (path : List Frame) (env : Env sem.Val Γ)
    (v : sem.Val payload) (returns : HList sem.Val mid → Prop) (halts : sem.H → Prop) :
    ((Stepped.Arms.cons inputs arm rest).denote sem path env (.here v)).Every permitted returns
        halts ↔
      (arm.denote sem path (env.extend inputs (.cons v .nil))).Every permitted returns halts := by
  rw [Stepped.Arms.denote_cons]
  exact Iff.rfl

/-- At another alternative, the arms have a property on every path exactly when the other arms
have it there. -/
theorem Stepped.Arms.every_there {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Stepped.Term D (Γ.extend inputs) mid)
    (rest : Stepped.Arms D Γ mid payloads) (path : List Frame) (env : Env sem.Val Γ)
    (pick : Pick sem.Val payloads) (returns : HList sem.Val mid → Prop) (halts : sem.H → Prop) :
    ((Stepped.Arms.cons inputs arm rest).denote sem path env (.there pick)).Every permitted returns
        halts ↔
      (rest.denote sem path env pick).Every permitted returns halts := by
  rw [Stepped.Arms.denote_cons]
  exact Iff.rfl

/-- **A loop, with an invariant over its iterations**: when the invariant holds of the initial
carried values and nothing collected, when the body, from each iteration below the count where the
invariant holds of the state, keeps it to the next iteration on what it returns, and when every
final state where the invariant holds at the count gives values with the property, the loop has
the property on every path, and its stops have the property that the body's have. -/
theorem Stepped.Instr.every_loop {Γ : Ctx D.Ty} {carried each : List D.Ty} (key : Key) (w : D.Who)
    (times : Times D w Γ) (gives : ∀ a, a ∈ carried ++ each → D.Gives w a)
    (initial : HList (Var Γ) carried) (inputs : Names (D.index w :: carried))
    (body : Stepped.Term D (Γ.extend inputs) (carried ++ each)) (path : List Frame)
    (env : Env sem.Val Γ) (invariant : Nat → sem.LoopState carried each → Prop)
    {returns : HList sem.Val (carried ++ each.map (D.collected times.size)) → Prop}
    {halts : sem.H → Prop}
    (start : invariant 0 (env.all initial, HList.empties each))
    (keeps : ∀ i state, i < sem.times times env → invariant i state →
      (body.denote sem (path ++ [.iteration key i])
          (env.extend inputs (.cons (sem.index w i) state.1))).Every permitted
        (fun out => invariant (i + 1)
          ((HList.split carried out).1, state.2.push (HList.split carried out).2))
        halts)
    (finish : ∀ state, invariant (sem.times times env) state →
      returns (state.1.append (sem.collected times.size state.2))) :
    ((Stepped.Instr.loop w times gives initial inputs body).denote sem key path env).Every permitted
      returns halts := by
  rw [Stepped.Instr.denote_loop, Process.every_bind]
  have iterated := Process.every_iterate_below permitted halts
    (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env) invariant
    (sem.times times env)
    (fun i state below holds => by
      rw [Semantics.loopStep, Process.every_bind]
      exact keeps i state below holds)
    (sem.times times env) 0 _ (Nat.le_of_eq (Nat.zero_add _)) start
  rw [Nat.zero_add] at iterated
  exact Process.every_mono _ permitted finish (fun _ stop => stop) iterated

/-- **A block** has a property on every path exactly when its body has it under the block's
frame. -/
theorem Stepped.Instr.every_block {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (number : Nat)
    (body : Stepped.Term D Γ mid) (path : List Frame) (env : Env sem.Val Γ)
    (returns : HList sem.Val mid → Prop) (halts : sem.H → Prop) :
    ((Stepped.Instr.block number body).denote sem key path env).Every permitted returns halts ↔
      (body.denote sem (path ++ [.iteration key number]) env).Every permitted returns halts := by
  rw [Stepped.Instr.denote_block]

/-- **An attempt** has a property on every path exactly when, on every number that its beginning
gives, its body with that number has, on every path, at each return, the end of the attempt
followed by that return with the property. -/
theorem Stepped.Instr.every_attempt {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (w : D.Who)
    (owns : D.Attempt w) (inputs : Names [D.index w]) (body : Stepped.Term D (Γ.extend inputs) mid)
    (path : List Frame) (env : Env sem.Val Γ) (returns : HList sem.Val mid → Prop)
    (halts : sem.H → Prop) :
    ((Stepped.Instr.attempt w owns inputs body).denote sem key path env).Every permitted returns
        halts ↔
      (sem.begin w key path).Every permitted
        (fun n => (body.denote sem path (env.extend inputs (.cons n .nil))).Every permitted
          (fun mids => (sem.settle w key path).Every permitted (fun _ => returns mids) halts)
          halts)
        halts := by
  simp only [Stepped.Instr.denote_attempt, Process.every_bind, Process.Every]

/-! ## A prefix -/

/-- **A prefix filled with a term** has a property on every path exactly when the prefix's process
has, on every path, at the environment that it ends in, the term with the property. -/
theorem Prefix.every_fill {outs : List D.Ty} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (rest : Stepped.Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ)
    (returns : HList sem.Val outs → Prop) (halts : sem.H → Prop) :
    ((p.fill rest).denote sem path env).Every permitted returns halts ↔
      (p.run sem path env).Every permitted
        (fun env' => (rest.denote sem path env').Every permitted returns halts) halts := by
  rw [Prefix.denote_fill_run]
  exact Process.every_bind _ _ _ _ _

/-- A prefix filled with a term has a property on every path when the prefix reaches its end, on
every path, with an environment of which `reached` holds, and the term has the property from
every such environment. -/
theorem Prefix.every_fill_of_run {outs : List D.Ty} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (rest : Stepped.Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ)
    {returns : HList sem.Val outs → Prop} {halts : sem.H → Prop}
    {reached : Env sem.Val Δ → Prop} (runs : (p.run sem path env).Every permitted reached halts)
    (continues : ∀ env', reached env' → (rest.denote sem path env').Every permitted returns halts) :
    ((p.fill rest).denote sem path env).Every permitted returns halts :=
  (Prefix.every_fill sem permitted p rest path env returns halts).mpr
    (Process.every_mono _ permitted continues (fun _ stop => stop) runs)

end

end Zkc.Core
