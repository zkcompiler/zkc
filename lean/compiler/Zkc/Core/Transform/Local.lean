module

public import Zkc.Core.Value.Soundness
public import Zkc.Core.Transform.Step
public import Zkc.Core.Facts.Soundness

@[expose] public section

/-!
The value form of the function dialect, and the theorem that two accepted functions of which
one follows the other's skeleton mean the same.

An operation of a function is a value, written as `LocalOp.print` writes it, unless it can stop
with a reason (`LocalOp.canStop`: a call of a function whose header says that it can stop); such
a call is kept in order (`localValueRules`, `Transform/Step.lean`, a module that computes,
since the step of a transformation runs the decision). The table places the applications as the
check of facts places them. The sum and the product of naturals, the conjunction and the
disjunction of truth values, and the equality of naturals and of truth values commute: each is
placed with its operands in one order, whichever way they were written; a row of the vocabulary
and a call do not.

A written form gives results on operands when it is the printed form of a local operation that
returns those results on those operands (`LocalReturns`), whatever the values, valid or not: the
law `computes` of the value form is for every value, and so is the law `commutative`, since the
meaning of each operation that commutes is symmetric for all values of its operands. Against
callees with distinct keys, of which those whose headers say that they cannot stop stop only
`undefined`, the local operations that are values satisfy the laws of the value form
(`localValueRules_binding`). Following decides
types and performers by equality and two operations by their printed forms (`localSkelRules`),
which is lawful over headers with distinct keys (`localSkelRules_lawful`).

So two bodies of functions over the same headers and of the same types, each with distinct
addresses and accepted by the check of facts, of which the second follows the skeleton of the
first, mean the same on every valid input, for any replies permitted
(`functions_follow_same`); a function has no effects, so their processes are equal
(`functions_follow_equal`). The check of facts gives what following does not decide: neither
stops `undefined` on valid inputs.
-/

namespace Zkc.Core

open FactCheck (Dyn toDyns toDyns_inj)

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A written form gives results on operands when it is the printed form of a local operation
that returns those results on those operands. The values need not be valid. -/
def LocalReturns (written : LocalRaw V) (operands results : List (Dyn M)) : Prop :=
  ∃ (ins res : List V.Ty) (o : LocalOp V fns ins res) (args : HList M.Val ins)
    (returned : HList M.Val res), o.print = written ∧ toDyns args = operands ∧
    toDyns returned = results ∧ localOp M table o args = .done returned

/-- Values with their types, of the local semantics, are the values of some type of the check of
facts. -/
theorem localDyns_eq_toDyns :
    ∀ {items : List V.Ty} (values : HList M.Val items),
      (localSem M fns table).dyns values = toDyns values
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show ⟨_, v⟩ :: (localSem M fns table).dyns rest = ⟨_, v⟩ :: toDyns rest
      rw [localDyns_eq_toDyns rest]

/-- The equality of naturals as the core computes it (`Nat.beq`) does not depend on the order of
its operands. -/
theorem natEqual_symmetric (first second : Nat) : Nat.beq first second = Nat.beq second first :=
  Bool.eq_iff_iff.mpr (by simp only [Nat.beq_eq]; exact eq_comm)

/-- The local operations that are values satisfy the laws of the value form: one that is a
value returns what its printed form gives, or stops `undefined`; a printed form gives one
result; and a printed form that commutes, which is that of an operation that the core owns whose
meaning is symmetric in its two operands, gives the same result on them exchanged. Its
hypotheses: the callees have distinct keys, so that a printed form names one operation; and a
callee whose header says that it cannot stop stops only `undefined`, since a call of it is a
value. -/
theorem localValueRules_binding (distinct : (fns.map (·.key)).Nodup)
    (quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
      (table hdr callee args).Stops (· = .undefined)) :
    (localValueRules V fns).Binding (localSem M fns table) (LocalReturns M table)
      (· = Stop.undefined) where
  computes := by
    intro ins res o raw written key path values
    cases stops : LocalOp.canStop o with
    | true => simp only [localValueRules, stops, Bool.cond_true, reduceCtorEq] at written
    | false =>
        simp only [localValueRules, stops, Bool.cond_false, Option.some.injEq] at written
        show (∃ results, localOp M table o values = .done results ∧ _) ∨
          ∃ stop, localOp M table o values = .halt stop ∧ stop = Stop.undefined
        have undefinedOnly := localOp_stops_undefined M table quiet o values stops
        cases ran : localOp M table o values with
        | done returned =>
            exact .inl ⟨returned, rfl, ins, res, o, values, returned, written,
              (localDyns_eq_toDyns M table values).symm,
              (localDyns_eq_toDyns M table returned).symm, ran⟩
        | halt stop =>
            rw [ran] at undefinedOnly
            exact .inr ⟨stop, rfl, undefinedOnly⟩
        | call op _ => exact nomatch op
  functional := by
    intro raw operands results results' first second
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := first
    obtain ⟨ins', res', o', args', returned', printed', sameArgs', sameResults', ran'⟩ := second
    obtain ⟨rfl, sameValues⟩ := toDyns_inj args args' (sameArgs.trans sameArgs'.symm)
    cases eq_of_heq sameValues
    obtain ⟨rfl, sameOp⟩ :=
      Sigma.mk.inj (LocalOp.print_injective distinct o o' (printed.trans printed'.symm))
    cases eq_of_heq sameOp
    rw [ran] at ran'
    cases ran'
    rw [← sameResults, ← sameResults']
  commutative := by
    intro raw commutes first second results returns
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := returns
    subst printed
    cases o with
    | row => simp [localValueRules, LocalOp.print, LocalRaw.commutes] at commutes
    | literal => simp [localValueRules, LocalOp.print, LocalRaw.commutes] at commutes
    | call => simp [localValueRules, LocalOp.print, LocalRaw.commutes] at commutes
    | owned o =>
        cases o <;> simp [localValueRules, LocalOp.print, OwnedOp.name, LocalRaw.commutes,
          OwnedName.commutes] at commutes
        all_goals
          rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
          simp only [toDyns, List.cons.injEq] at sameArgs
          obtain ⟨rfl, rfl, -⟩ := sameArgs
          refine ⟨_, _, .owned _, .cons b (.cons a .nil), returned, rfl, rfl, sameResults, ?_⟩
          rw [← ran]
          simp only [localOp, ownedOp, Nat.add_comm, Nat.mul_comm, Bool.and_comm, Bool.or_comm,
            Bool.beq_comm, natEqual_symmetric]

end

/-- Operations that following finds the same are the same, over headers with distinct keys: a
printed form names one operation. -/
theorem localSkelRules_lawful {V : Vocabulary} {fns : List (FnHeader V)}
    (distinct : (fns.map (·.key)).Nodup) : (localSkelRules V fns).Lawful := by
  intro ins res res' o o' found
  exact Sigma.mk.inj (LocalOp.print_injective distinct o o' (of_decide_eq_true found))

section
variable {V : Vocabulary} {fns : List (FnHeader V)}

/-- **Two accepted functions of which the second follows the first mean the same.** For two
bodies of
functions over the same headers, with the same input and result types, each with distinct
addresses and accepted by the check of facts, of which the second follows the skeleton of the
first: against callees with distinct keys that never stop `undefined` on valid inputs, keep
validity, and stop only `undefined` where their headers say that they cannot stop, on every
valid input the two processes mean the same, for any replies permitted. -/
theorem functions_follow_same {types outs : List V.Ty} (inputs inputs' : Names types)
    (body : Term (localDialect V fns) (Ctx.empty.extend inputs) outs)
    (body' : Term (localDialect V fns) (Ctx.empty.extend inputs') outs)
    (definition definition' : Key) {bounds bounds' : List (Place × Nat)}
    (distinctBody : Term.Distinct body) (distinctBody' : Term.Distinct body')
    (accepted : checkFacts (localFactRules V fns) definition none inputs body = .ok bounds)
    (accepted' : checkFacts (localFactRules V fns) definition' none inputs' body' = .ok bounds')
    (decided : followsSkeleton (localValueRules V fns) (localSkelRules V fns) inputs inputs' body
      body' = true)
    (M : Model V) (table : FnTable M fns) (distinct : (fns.map (·.key)).Nodup)
    (safe : FnTable.Safe table) (keeps : FnTable.KeepsValidity table)
    (quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
      (table hdr callee args).Stops (· = .undefined))
    (ins : HList M.Val types) (valid : ins.All M.Valid)
    (permitted : ∀ op, NoSig.Reply op → Prop) :
    Process.SameWhen permitted
      (body.denote (localSem M fns table) [] (Env.empty.extend inputs ins))
      (body'.denote (localSem M fns table) [] (Env.empty.extend inputs' ins)) :=
  followsSkeleton_sound (localSem M fns table) permitted (LocalReturns M table)
    (localValueRules V fns) (localValueRules_binding M table distinct quiet) (localSkelRules V fns)
    (localSkelRules_lawful distinct) inputs inputs' body body' decided [] ins
    (Process.every_noSig (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h)
      (FactCheck.checkFacts_sound distinct safe keeps definition inputs body distinctBody
        accepted [] (fun _ _ none => nomatch none) ins valid).2))
    (Process.every_noSig (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h)
      (FactCheck.checkFacts_sound distinct safe keeps definition' inputs' body' distinctBody'
        accepted' [] (fun _ _ none => nomatch none) ins valid).2))

/-- Two accepted functions of which the second follows the skeleton of the first have equal
processes on every valid input: a function has no effects, so meaning the same is equality. -/
theorem functions_follow_equal {types outs : List V.Ty} (inputs inputs' : Names types)
    (body : Term (localDialect V fns) (Ctx.empty.extend inputs) outs)
    (body' : Term (localDialect V fns) (Ctx.empty.extend inputs') outs)
    (definition definition' : Key) {bounds bounds' : List (Place × Nat)}
    (distinctBody : Term.Distinct body) (distinctBody' : Term.Distinct body')
    (accepted : checkFacts (localFactRules V fns) definition none inputs body = .ok bounds)
    (accepted' : checkFacts (localFactRules V fns) definition' none inputs' body' = .ok bounds')
    (decided : followsSkeleton (localValueRules V fns) (localSkelRules V fns) inputs inputs' body
      body' = true)
    (M : Model V) (table : FnTable M fns) (distinct : (fns.map (·.key)).Nodup)
    (safe : FnTable.Safe table) (keeps : FnTable.KeepsValidity table)
    (quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
      (table hdr callee args).Stops (· = .undefined))
    (ins : HList M.Val types) (valid : ins.All M.Valid) :
    body.denote (localSem M fns table) [] (Env.empty.extend inputs ins) =
      body'.denote (localSem M fns table) [] (Env.empty.extend inputs' ins) :=
  (functions_follow_same inputs inputs' body body' definition definition' distinctBody
    distinctBody' accepted accepted' decided M table distinct safe keeps quiet ins valid
    fun _ _ => True).eq_of_noSig

end

end Zkc.Core
