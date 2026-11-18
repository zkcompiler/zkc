module

public import Zkc.Core.Evidence.Subject
public import Zkc.Core.Meaning.Validity

@[expose] public section

/-!
The rule of a call: what is known of a function is knowledge of every call of it.

A contract of a function is a property of its entry in a table of functions: on inputs that
satisfy its precondition, every return satisfies what it promises of the results, and every stop
what it promises of the stops (`Contract`). A law of a total function gives its results by a
mathematical function and never stops (`Law`). Each is knowledge of the subject of every call of
the function (`Evidence/Subject.lean`): at operands whose values satisfy the precondition, the
subject satisfies the contract at those values (`Contract.satisfies`), and a law says that the
subject yields the law's function of the operands (`Law.yields`). The rule of a call
(`Contract.call`, `Law.call`) is the rule of an instruction (`Term.op_satisfies`,
`Term.op_yields`) at a call: the operands and the continuation come from the term, so that
whoever uses it proves nothing about the plumbing of the call. A consumer of the rule quantifies
over every table that has the contract, so it cannot unfold the callee.

The summary of a function, read as a function reads its values (`localReading`, with no written
operation, the validity of the model and the stop `undefined`), holds of its entry in a table
exactly when the entry has the contract whose precondition is valid inputs that satisfy the
requirements, whose postcondition is valid results that, with the inputs, satisfy the guarantees,
and whose stops are not `undefined` (`localSummary_contract`); so a summary that holds of a callee
is knowledge of every call of it (`localSummary_satisfies`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
  {hdr : FnHeader V} (callee : Member fns hdr)

/-- The contract of a function at its entry in a table: on inputs that satisfy `pre`, every
return satisfies `post` and every stop satisfies `stops`. -/
structure Contract (pre : HList M.Val hdr.ins → Prop)
    (post : HList M.Val hdr.ins → HList M.Val hdr.outs → Prop)
    (stops : HList M.Val hdr.ins → Stop → Prop) : Prop where
  holds : ∀ args, pre args → (table _ callee args).Every (fun _ _ => True) (post args) (stops args)

/-- The law of a total function at its entry in a table: it returns what `model` gives. -/
structure Law (model : HList M.Val hdr.ins → HList M.Val hdr.outs) : Prop where
  implements : ∀ args, table _ callee args = .done (model args)

/-- **A contract of a function is knowledge of every call of it.** At operands whose values are
the inputs given and satisfy the precondition, the subject of a call of the function satisfies
the contract at those inputs: what it returns satisfies the postcondition, and how it stops the
condition on stops. -/
theorem Contract.satisfies {pre : HList M.Val hdr.ins → Prop}
    {post : HList M.Val hdr.ins → HList M.Val hdr.outs → Prop}
    {stops : HList M.Val hdr.ins → Stop → Prop} (contract : Contract M table callee pre post stops)
    {Γ : Ctx V.Ty} (key : Key) (args : HList (Var Γ) hdr.ins) (inputs : HList M.Val hdr.ins) :
    (Subject.op (localSem M fns table) key (LocalOp.call callee) args).Satisfies
      (localSem M fns table) (fun _ _ => True) (fun _ env => env.all args = inputs ∧ pre inputs)
      (fun _ results => post inputs results) (stops inputs) := by
  intro path env ⟨same, admitted⟩
  subst same
  exact contract.holds _ admitted

/-- **A law of a function is a witness of every call of it**: the subject of a call yields what
the law gives of the operands' values, from every start. -/
theorem Law.yields {model : HList M.Val hdr.ins → HList M.Val hdr.outs}
    (law : Law M table callee model) {Γ : Ctx V.Ty} (key : Key) (args : HList (Var Γ) hdr.ins) :
    (Subject.op (localSem M fns table) key (LocalOp.call callee) args).Yields
      (localSem M fns table) (fun _ _ => True) (fun env => model (env.all args)) :=
  fun _ env _ => law.implements (env.all args)

/-- **The rule of a call**: at a call of the function in a body, with its operands from the
environment, every path satisfies what the continuation satisfies on every result that the
contract promises, and the stops that it promises, where the operands satisfy the
precondition. It is the rule of an instruction for a contract (`Term.op_satisfies`) at a call,
with the contract at the operands' values (`Contract.satisfies`). -/
theorem Contract.call {pre : HList M.Val hdr.ins → Prop}
    {post : HList M.Val hdr.ins → HList M.Val hdr.outs → Prop}
    {stops : HList M.Val hdr.ins → Stop → Prop} (contract : Contract M table callee pre post stops)
    {Γ : Ctx V.Ty} {outs : List V.Ty} (key : Key) (args : HList (Var Γ) hdr.ins)
    (results : Names hdr.outs) (rest : Term (localDialect V fns) (Γ.extend results) outs)
    (path : List Frame) (env : Env M.Val Γ) (Q : HList M.Val outs → Prop) (R : Stop → Prop)
    (admitted : pre (env.all args))
    (continues : ∀ values, post (env.all args) values →
      (rest.denote (localSem M fns table) path (env.extend results values)).Every
        (fun _ _ => True) Q R)
    (stopped : ∀ why, stops (env.all args) why → R why) :
    ((Term.op (D := localDialect V fns) key (LocalOp.call callee) args results rest).denote
      (localSem M fns table) path env).Every (fun _ _ => True) Q R :=
  Term.op_satisfies (localSem M fns table) (fun _ _ => True)
    (contract.satisfies M table callee key args (env.all args)) results rest Q R path env
    ⟨rfl, admitted⟩ continues stopped

/-- **The rule of a call of a total function**: the call is the continuation on what the law
gives. It is the rule of an instruction for a witness (`Term.op_yields`) at a call, with the law
as the witness (`Law.yields`). -/
theorem Law.call {model : HList M.Val hdr.ins → HList M.Val hdr.outs}
    (law : Law M table callee model) {Γ : Ctx V.Ty} {outs : List V.Ty} (key : Key)
    (args : HList (Var Γ) hdr.ins) (results : Names hdr.outs)
    (rest : Term (localDialect V fns) (Γ.extend results) outs) (path : List Frame)
    (env : Env M.Val Γ) :
    (Term.op (D := localDialect V fns) key (LocalOp.call callee) args results rest).denote
        (localSem M fns table) path env =
      rest.denote (localSem M fns table) path (env.extend results (model (env.all args))) :=
  Term.op_yields (localSem M fns table) (law.yields M table callee key args) results rest path
    env trivial

end

/-! ## A summary of a function is a contract -/

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
  {hdr : FnHeader V} (callee : Member fns hdr)

/-- **A summary that holds of a function's entry is its contract.** For the function dialect,
read as a function reads its values (`localReading`, with no written operation, the validity of
the model and the stop `undefined`), the summary of a function holds of the entry of a function in
a table exactly when the entry has the contract (`Contract`) whose precondition is valid inputs
that satisfy the requirements, whose postcondition is valid results that, with the inputs,
satisfy the guarantees, and whose stops are not `undefined`. -/
theorem localSummary_contract (summary : Summary Empty) :
    Summary.Holds (localSem M fns table) (fun _ _ => True) (localReading M) Empty.elim
        (ValidDyn M) (· = .undefined) summary (table hdr callee) ↔
      Contract M table callee
        (fun args => args.All M.Valid ∧ ∀ requirement, requirement ∈ summary.requires →
          requirement.Holds Empty.elim (localReading M) ((localSem M fns table).dyns args))
        (fun args results => results.All M.Valid ∧ ∀ guarantee, guarantee ∈ summary.ensures →
          guarantee.Holds Empty.elim (localReading M)
            ((localSem M fns table).dyns args ++ (localSem M fns table).dyns results))
        (fun _ stop => stop ≠ .undefined) := by
  constructor
  · intro holds
    refine ⟨fun args pre => ?_⟩
    exact Process.every_mono _ _
      (fun results returned => ⟨((localSem M fns table).dyns_valid_iff results).mp returned.1,
        returned.2⟩)
      (fun _ stop => stop)
      (holds args (((localSem M fns table).dyns_valid_iff args).mpr pre.1) pre.2)
  · intro contract inputs valid requirements
    exact Process.every_mono _ _
      (fun results returned => ⟨((localSem M fns table).dyns_valid_iff results).mpr returned.1,
        returned.2⟩)
      (fun _ stop => stop)
      (contract.holds inputs
        ⟨((localSem M fns table).dyns_valid_iff inputs).mp valid, requirements⟩)

/-- **A summary that holds of a function is knowledge of every call of it**, through the contract
that it is (`localSummary_contract`): at valid operands whose values satisfy the summary's
requirements, the subject of a call returns valid values that, with the operands, satisfy its
guarantees, and never stops `undefined`. -/
theorem localSummary_satisfies {summary : Summary Empty}
    (holds : Summary.Holds (localSem M fns table) (fun _ _ => True) (localReading M) Empty.elim
      (ValidDyn M) (· = .undefined) summary (table hdr callee))
    {Γ : Ctx V.Ty} (key : Key) (args : HList (Var Γ) hdr.ins) :
    (Subject.op (localSem M fns table) key (LocalOp.call callee) args).Satisfies
      (localSem M fns table) (fun _ _ => True)
      (fun _ env => (env.all args).All M.Valid ∧ ∀ requirement, requirement ∈ summary.requires →
        requirement.Holds Empty.elim (localReading M) ((localSem M fns table).dyns (env.all args)))
      (fun env results => results.All M.Valid ∧ ∀ guarantee, guarantee ∈ summary.ensures →
        guarantee.Holds Empty.elim (localReading M)
          ((localSem M fns table).dyns (env.all args) ++ (localSem M fns table).dyns results))
      (· ≠ .undefined) :=
  fun path env pre =>
    ((localSummary_contract M table callee summary).mp holds).satisfies M table callee key args
      (env.all args) path env ⟨rfl, pre⟩

end

end Zkc.Core
