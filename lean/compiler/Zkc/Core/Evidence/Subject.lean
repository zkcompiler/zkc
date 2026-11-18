module

public import Zkc.Core.Evidence.Relation

@[expose] public section

/-!
What an instruction runs, as the one thing that what is known of a computation is attached to,
whether the instruction is an application of an operation of the vocabulary, a call of a
definition, or a block (a region with a key).

Every instruction that binds results means "run something, bind what it returns, go on": the
*subject* is that something, a process as a function of the path and the environment
(`Subject`): for an application, the operation on its operands (`Subject.op`); for a block, its
body under the block's frame (`Subject.block`). The meaning of each is its subject, then the
continuation (`Term.op_subject`, `Term.block_subject`). What is known of a subject comes in two
strengths, each with one rule for the continuation, for every kind of subject:

- `Subject.Satisfies`: on authorized starts, every return satisfies a postcondition (which may
  mention the environment) and every stop a condition on stops: a contract. A subject that
  satisfies one, followed by a continuation that satisfies `returns` and `halts` on every result
  that the contract promises, satisfies them when the contract's stops are among `halts`
  (`Subject.Satisfies.then`; on a term, `Term.op_satisfies`).
- `Subject.Yields`: on authorized starts, the subject returns exactly what a function of the
  environment gives, with no question to the world and no stop: an implementation witness, by
  which every law of the function applies to the subject. Followed by a continuation, it is the
  continuation on what the function gives (`Subject.Yields.then`; on a term, `Term.op_yields`,
  `Term.block_yields`). A witness is a contract with no stop (`Subject.Yields.satisfies`); a
  contract does not give a witness.

A law lifts through witnesses: two subjects that yield functions which agree on the authorized
starts are the same process there (`Subject.Yields.same`), so two instructions with those
subjects, each followed by the same continuation, mean the same in that scope
(`Term.equivalent_of_yields`). A specification is a Lean function, or for a contract a relation:
there is no registry of concepts, and two subjects are known to compute the same thing when their
witnesses name functions that a theorem relates. What is known of a block's body is known of the
block, and stays known along the relation "same meaning" of the body under the block's frame, a
contract (`Subject.block_transfers`) and a witness (`Subject.block_yields_transfers`) alike.

Nothing here depends on an analysis. For the function dialect, a contract or a law of a callee,
and a summary that holds of it, are knowledge of every call of it (`Evidence/Call.lean`); an
operation that the core owns, where its requirements hold, and a row of the vocabulary that is not
restricted yield what the model gives (`ownedOp_yields`, `row_yields`, `Facts/LocalLaws.lean`).
-/

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)

/-- What an instruction runs before its continuation: a process of the values that it binds, as
a function of the path and the environment. -/
abbrev Subject (Γ : Ctx D.Ty) (mid : List D.Ty) : Type :=
  List Frame → Env sem.Val Γ → Process sem.S sem.H (HList sem.Val mid)

/-- The subject of an application of an operation (a row, a call, an effect). -/
def Subject.op {Γ : Ctx D.Ty} {ins res : List D.Ty} (key : Key) (o : D.Op ins res)
    (operands : HList (Var Γ) ins) : Subject sem Γ res :=
  fun path env => sem.op key o path (env.all operands)

/-- The subject of a block: its body, under the block's frame. -/
def Subject.block {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (number : Nat)
    (body : Term D Γ mid) : Subject sem Γ mid :=
  fun path env => body.denote sem (path ++ [.iteration key number]) env

/-- A subject satisfies a contract: from every authorized start, on permitted replies, what it
returns satisfies the postcondition (which may mention the environment) and how it stops
satisfies the condition on stops. -/
def Subject.Satisfies {Γ : Ctx D.Ty} {mid : List D.Ty} (subject : Subject sem Γ mid)
    (entry : Entry sem Γ) (post : Env sem.Val Γ → HList sem.Val mid → Prop)
    (stops : sem.H → Prop) : Prop :=
  ∀ path env, entry path env → (subject path env).Every permitted (post env) stops

/-- A subject yields a function: from every authorized start it returns exactly what the
function gives of the environment, with no question to the world and no stop. -/
def Subject.Yields {Γ : Ctx D.Ty} {mid : List D.Ty} (subject : Subject sem Γ mid)
    (entry : Entry sem Γ) (compute : Env sem.Val Γ → HList sem.Val mid) : Prop :=
  ∀ path env, entry path env → subject path env = .done (compute env)

/-! ## An instruction is its subject, then its continuation -/

/-- **The meaning of an application is its subject, then the continuation.** -/
theorem Term.op_subject {Γ : Ctx D.Ty} {ins res outs : List D.Ty} (key : Key) (o : D.Op ins res)
    (operands : HList (Var Γ) ins) (results : Names res) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.op key o operands results rest).denote sem path env =
      (Subject.op sem key o operands path env).bind fun values =>
        rest.denote sem path (env.extend results values) :=
  rfl

/-- **The meaning of a block is its subject, then the continuation.** -/
theorem Term.block_subject {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key) (number : Nat)
    (body : Term D Γ mid) (results : Names mid) (rest : Term D (Γ.extend results) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Term.block key number body results rest).denote sem path env =
      (Subject.block sem key number body path env).bind fun values =>
        rest.denote sem path (env.extend results values) :=
  rfl

/-! ## The two rules for the continuation -/

/-- **The rule of an instruction, for a contract.** A subject that satisfies a contract, followed
by a continuation that satisfies `returns` and `halts` on every result that the contract promises,
satisfies them, when the contract's stops are among `halts`. One statement for an operation, a
call and a block. -/
theorem Subject.Satisfies.then {Γ : Ctx D.Ty} {mid outs : List D.Ty} {subject : Subject sem Γ mid}
    {entry : Entry sem Γ} {post : Env sem.Val Γ → HList sem.Val mid → Prop} {stops : sem.H → Prop}
    (satisfies : subject.Satisfies sem permitted entry post stops)
    (continuation : List Frame → Env sem.Val Γ → HList sem.Val mid →
      Process sem.S sem.H (HList sem.Val outs))
    (returns : HList sem.Val outs → Prop) (halts : sem.H → Prop) (path : List Frame)
    (env : Env sem.Val Γ) (authorized : entry path env)
    (continues : ∀ values, post env values →
      (continuation path env values).Every permitted returns halts)
    (stopped : ∀ stop, stops stop → halts stop) :
    ((subject path env).bind (continuation path env)).Every permitted returns halts := by
  rw [Process.every_bind]
  exact Process.every_mono _ _ continues stopped (satisfies path env authorized)

/-- **The rule of an instruction, for a witness.** A subject that yields a function, followed by
a continuation, is the continuation on what the function gives. -/
theorem Subject.Yields.then {Γ : Ctx D.Ty} {mid outs : List D.Ty} {subject : Subject sem Γ mid}
    {entry : Entry sem Γ} {compute : Env sem.Val Γ → HList sem.Val mid}
    (yields : subject.Yields sem entry compute)
    (continuation : HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs))
    (path : List Frame) (env : Env sem.Val Γ) (authorized : entry path env) :
    (subject path env).bind continuation = continuation (compute env) := by
  rw [yields path env authorized]
  rfl

/-- **A law lifts through witnesses.** Two subjects that yield functions which agree on the
authorized starts are the same process there. -/
theorem Subject.Yields.same {Γ : Ctx D.Ty} {mid : List D.Ty} {first second : Subject sem Γ mid}
    {entry : Entry sem Γ} {compute compute' : Env sem.Val Γ → HList sem.Val mid}
    (yields : first.Yields sem entry compute) (yields' : second.Yields sem entry compute')
    (agree : ∀ path env, entry path env → compute env = compute' env) :
    ∀ path env, entry path env → first path env = second path env :=
  fun path env authorized => by
    rw [yields path env authorized, yields' path env authorized, agree path env authorized]

/-- **A witness is a contract**: what is yielded satisfies any postcondition that the function's
result satisfies, and there is no stop. -/
theorem Subject.Yields.satisfies {Γ : Ctx D.Ty} {mid : List D.Ty} {subject : Subject sem Γ mid}
    {entry : Entry sem Γ} {compute : Env sem.Val Γ → HList sem.Val mid}
    (yields : subject.Yields sem entry compute) (post : Env sem.Val Γ → HList sem.Val mid → Prop)
    (holds : ∀ path env, entry path env → post env (compute env)) :
    subject.Satisfies sem permitted entry post (fun _ => False) :=
  fun path env authorized => by
    rw [yields path env authorized]
    exact holds path env authorized

/-! ## What is known of a block's body -/

/-- **What is known of a block's body is known of the block, for a contract.** A body that means
the same as another under the block's frame gives a block subject that satisfies every contract
that the first does. This is how what is known of a definition stays known of its body spliced
under a block, and of that body after an edit that a relation covers. -/
theorem Subject.block_transfers {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (number : Nat)
    (body body' : Term D Γ mid) (entry : Entry sem Γ)
    (same : Equivalent sem permitted body body'
      (fun path env => ∃ outer, path = outer ++ [.iteration key number] ∧ entry outer env))
    (post : Env sem.Val Γ → HList sem.Val mid → Prop) (stops : sem.H → Prop)
    (satisfies : (Subject.block sem key number body).Satisfies sem permitted entry post stops) :
    (Subject.block sem key number body').Satisfies sem permitted entry post stops :=
  fun path env authorized =>
    (same (path ++ [.iteration key number]) env ⟨path, rfl, authorized⟩).every
      (satisfies path env authorized)

/-- **What is known of a block's body is known of the block, for a witness.** A body that means
the same as another under the block's frame, equal processes among them, gives a block subject
that yields every function that the first yields: a process that returns at once is related only
to itself. -/
theorem Subject.block_yields_transfers {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key)
    (number : Nat) (body body' : Term D Γ mid) (entry : Entry sem Γ)
    (same : Equivalent sem permitted body body'
      (fun path env => ∃ outer, path = outer ++ [.iteration key number] ∧ entry outer env))
    (compute : Env sem.Val Γ → HList sem.Val mid)
    (yields : (Subject.block sem key number body).Yields sem entry compute) :
    (Subject.block sem key number body').Yields sem entry compute := by
  intro path env authorized
  have related := same (path ++ [.iteration key number]) env ⟨path, rfl, authorized⟩
  have returned : body.denote sem (path ++ [.iteration key number]) env = .done (compute env) :=
    yields path env authorized
  rw [returned] at related
  show body'.denote sem (path ++ [.iteration key number]) env = .done (compute env)
  generalize body'.denote sem (path ++ [.iteration key number]) env = other at related ⊢
  cases related
  rfl

/-! ## The rules on terms -/

/-- **An application whose subject satisfies a contract**: the whole term satisfies `returns`
and `halts` when the continuation does on every result that the contract promises and the
contract's stops are among `halts`. The rule of a call (`Contract.call`) is its case for a call of
a function. -/
theorem Term.op_satisfies {Γ : Ctx D.Ty} {ins res outs : List D.Ty} {key : Key} {o : D.Op ins res}
    {operands : HList (Var Γ) ins} {entry : Entry sem Γ}
    {post : Env sem.Val Γ → HList sem.Val res → Prop} {stops : sem.H → Prop}
    (satisfies : (Subject.op sem key o operands).Satisfies sem permitted entry post stops)
    (results : Names res) (rest : Term D (Γ.extend results) outs)
    (returns : HList sem.Val outs → Prop) (halts : sem.H → Prop) (path : List Frame)
    (env : Env sem.Val Γ) (authorized : entry path env)
    (continues : ∀ values, post env values →
      (rest.denote sem path (env.extend results values)).Every permitted returns halts)
    (stopped : ∀ stop, stops stop → halts stop) :
    ((Term.op key o operands results rest).denote sem path env).Every permitted returns halts := by
  rw [Term.op_subject]
  exact satisfies.then sem permitted
    (fun path env values => rest.denote sem path (env.extend results values)) returns halts path
    env authorized continues stopped

/-- **An application whose subject yields a function** is its continuation on what the function
gives. The rule of a call of a total function (`Law.call`) is its case for a call. -/
theorem Term.op_yields {Γ : Ctx D.Ty} {ins res outs : List D.Ty} {key : Key} {o : D.Op ins res}
    {operands : HList (Var Γ) ins} {entry : Entry sem Γ}
    {compute : Env sem.Val Γ → HList sem.Val res}
    (yields : (Subject.op sem key o operands).Yields sem entry compute)
    (results : Names res) (rest : Term D (Γ.extend results) outs) (path : List Frame)
    (env : Env sem.Val Γ) (authorized : entry path env) :
    (Term.op key o operands results rest).denote sem path env =
      rest.denote sem path (env.extend results (compute env)) := by
  rw [Term.op_subject]
  exact yields.then sem (fun values => rest.denote sem path (env.extend results values)) path env
    authorized

/-- **A block whose subject yields a function** is its continuation on what the function
gives. -/
theorem Term.block_yields {Γ : Ctx D.Ty} {mid outs : List D.Ty} {key : Key} {number : Nat}
    {body : Term D Γ mid} {entry : Entry sem Γ} {compute : Env sem.Val Γ → HList sem.Val mid}
    (yields : (Subject.block sem key number body).Yields sem entry compute)
    (results : Names mid) (rest : Term D (Γ.extend results) outs) (path : List Frame)
    (env : Env sem.Val Γ) (authorized : entry path env) :
    (Term.block key number body results rest).denote sem path env =
      rest.denote sem path (env.extend results (compute env)) := by
  rw [Term.block_subject]
  exact yields.then sem (fun values => rest.denote sem path (env.extend results values)) path env
    authorized

/-- **A law lifted through witnesses, on terms.** Two instructions of the same result types in
one context, each its subject then the same continuation (`Term.op_subject`,
`Term.block_subject`), whose subjects yield functions that agree on the authorized starts, mean
the same in that scope. -/
theorem Term.equivalent_of_yields {Γ : Ctx D.Ty} {mid outs : List D.Ty} {term term' : Term D Γ outs}
    {first second : Subject sem Γ mid} {results : Names mid}
    {rest : Term D (Γ.extend results) outs} {entry : Entry sem Γ}
    {compute compute' : Env sem.Val Γ → HList sem.Val mid}
    (runs : ∀ path env, term.denote sem path env =
      (first path env).bind fun values => rest.denote sem path (env.extend results values))
    (runs' : ∀ path env, term'.denote sem path env =
      (second path env).bind fun values => rest.denote sem path (env.extend results values))
    (yields : first.Yields sem entry compute) (yields' : second.Yields sem entry compute')
    (agree : ∀ path env, entry path env → compute env = compute' env) :
    Equivalent sem permitted term term' entry := by
  intro path env authorized
  rw [runs, runs', yields.same sem yields' agree path env authorized]
  exact Process.SameWhen.refl _

end

end Zkc.Core
