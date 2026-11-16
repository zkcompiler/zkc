module

public import Zkc.Core.Value.Skeleton

@[expose] public section

/-!
The decision that two terms mean the same: the second follows the skeleton of the first.

Following walks a second term along the skeleton of the first, with the first's table
(`Term.follows`): the second term's values are found in or added to the table, the operands of
an operation that commutes in one order whichever way they were written, and each instruction
that it keeps in order must be the skeleton's next entry, on the same identifiers.
What a dialect must decide for it is said by `SkelRules`: its types, its performers, and whether
two operations are the same. `same` decides two definitions, with the inputs of both on the
same identifiers.

That a term that follows a skeleton runs it, so that two terms of which one follows the other's
skeleton mean the same, is `Term.follows_runs` and `same_sound` (`Value/Soundness.lean`).
-/

namespace Zkc.Core

open FactCheck (St share idOf idsOf bindIds)

section
variable {D : Dialect} {Raw : Type}

/-! ## Following a skeleton -/

/-- What following a skeleton compares that a dialect must decide. -/
structure SkelRules (D : Dialect) where
  sameTy : DecidableEq D.Ty
  sameWho : DecidableEq D.Who
  /-- Whether two operations on operands of the same types are the same operation. -/
  sameOp : ∀ {ins res res' : List D.Ty}, D.Op ins res → D.Op ins res' → Bool

/-- Operations that are found the same are the same. -/
def SkelRules.Lawful (checks : SkelRules D) : Prop :=
  ∀ {ins res res' : List D.Ty} (o : D.Op ins res) (o' : D.Op ins res'),
    checks.sameOp o o' = true → res = res' ∧ HEq o o'

/-- Whether two lists of types are equal, by the dialect's decision for types. -/
def SkelRules.sameTys (checks : SkelRules D) : DecidableEq (List D.Ty) :=
  @instDecidableEqList D.Ty checks.sameTy

/-- Whether how often a loop runs follows how often a loop of a skeleton runs: the same written
number, or a count of the same type, by the dialect's decision, on the same identifier. -/
def Times.follows (checks : SkelRules D) {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Nat) :
    Times D w Γ → Count D w → Bool
  | .fixed n, .fixed n' => decide (n = n')
  | .value (t := t) count _, .value (t := t') id _ =>
      match checks.sameTy t t' with
      | isTrue _ => decide (idOf ids count.name = id)
      | isFalse _ => false
  | .fixed _, .value .. => false
  | .value .., .fixed _ => false

mutual
  /-- A term follows a skeleton, from the identifiers of the names in scope and a state whose
  next identifier is above every leaf of the skeleton: the state with the term's values added,
  or nothing. A value of the term is shared in the table, with its operands in the order of
  `ValueRules.order`, and the skeleton stays where it is.
  Every other instruction of the term must be the skeleton's next entry: the same key, the same
  performers, the same operation on the same types, its operands and its condition on the same
  identifiers, a written count or the same identifier of a count, the same reason; its regions
  follow the entry's regions; and the names that it binds get the entry's leaves. The exit of
  the term must be the skeleton's, on the same identifiers. No identifier is made for a leaf:
  the state's next identifier moves only for values. -/
  def Term.follows (rules : ValueRules D Raw) [DecidableEq Raw] (checks : SkelRules D) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} →
      Term D Γ outs → Skel D outs → Ctx Nat → St D.Ty Raw → Option (St D.Ty Raw)
    | _, _, .ret exit, skel, ids, st =>
        match skel with
        | .ret exit' => if idsOf ids exit = exit' then some st else none
        | _ => none
    | _, _, .op (ins := ins) (res := res) key o operands results rest, skel, ids, st =>
        match rules.written o with
        | some raw =>
            let made := share raw (rules.order raw (idsOf ids operands)) res.length st
            Term.follows rules checks rest skel (bindIds ids results made.1) made.2
        | none =>
            match skel with
            | .effect (ins := ins') (res := res') key' o' operands' results' rest' =>
                match checks.sameTys ins ins', checks.sameTys res res' with
                | isTrue sameIns, isTrue sameRes =>
                    if checks.sameOp o
                          (cast (show D.Op ins' res' = D.Op ins res by rw [sameIns, sameRes]) o') =
                        true ∧ key = key' ∧ idsOf ids operands = operands' then
                      Term.follows rules checks rest rest'
                        (bindIds ids results (List.range' results' res.length)) st
                    else none
                | _, _ => none
            | _ => none
    | _, _, .guard (t := t) key w c _ why rest, skel, ids, st =>
        match skel with
        | .guard (t := t') key' w' condition _ why' rest' =>
            match checks.sameWho w w', checks.sameTy t t' with
            | isTrue _, isTrue _ =>
                if key = key' ∧ why = why' ∧ idOf ids c.name = condition then
                  Term.follows rules checks rest rest' ids st
                else none
            | _, _ => none
        | _ => none
    | _, _, .choose (mid := mid) (t := t) key w c _ _ onTrue onFalse results rest, skel, ids, st =>
        match skel with
        | .choose (mid := mid') (t := t') key' w' condition _ onTrue' onFalse' results' rest' =>
            match checks.sameWho w w', checks.sameTy t t', checks.sameTys mid mid' with
            | isTrue _, isTrue _, isTrue sameMid =>
                if key = key' ∧ idOf ids c.name = condition then
                  (Term.follows rules checks onTrue (cast (congrArg (Skel D) sameMid.symm) onTrue')
                      ids st).bind fun afterTrue =>
                    (Term.follows rules checks onFalse
                        (cast (congrArg (Skel D) sameMid.symm) onFalse') ids afterTrue).bind
                      fun afterFalse =>
                        Term.follows rules checks rest rest'
                          (bindIds ids results (List.range' results' mid.length)) afterFalse
                else none
            | _, _, _ => none
        | _ => none
    | _, _, .cases (mid := mid) (t := t) (payloads := payloads) key w x _ _ arms results rest, skel,
        ids, st =>
        match skel with
        | .cases (mid := mid') (t := t') (payloads := payloads') key' w' subject _ arms' results'
            rest' =>
            match checks.sameWho w w', checks.sameTy t t', checks.sameTys mid mid',
              checks.sameTys payloads payloads' with
            | isTrue _, isTrue _, isTrue sameMid, isTrue samePayloads =>
                if key = key' ∧ idOf ids x.name = subject then
                  (Arms.follows rules checks arms
                      (cast (by rw [sameMid, samePayloads]) arms') ids st).bind fun afterArms =>
                    Term.follows rules checks rest rest'
                      (bindIds ids results (List.range' results' mid.length)) afterArms
                else none
            | _, _, _, _ => none
        | _ => none
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, skel, ids, st =>
        match skel with
        | .loop (carried := carried') (each := each') key' w' times' initial' inputs' body' results'
            rest' =>
            match checks.sameWho w w', checks.sameTys carried carried',
              checks.sameTys each each' with
            | isTrue sameWho, isTrue sameCarried, isTrue sameEach =>
                if key = key' ∧
                    times.follows checks ids (cast (congrArg (Count D) sameWho.symm) times') =
                      true ∧
                    idsOf ids initial = initial' then
                  (Term.follows rules checks body (cast (by rw [sameCarried, sameEach]) body')
                      (bindIds ids inputs (List.range' inputs' (carried.length + 1))) st).bind
                    fun afterBody =>
                      Term.follows rules checks rest rest'
                        (bindIds ids results
                          (List.range' results' (carried.length + each.length))) afterBody
                else none
            | _, _, _ => none
        | _ => none
    | _, _, .block (mid := mid) key number body results rest, skel, ids, st =>
        match skel with
        | .block (mid := mid') key' number' body' results' rest' =>
            match checks.sameTys mid mid' with
            | isTrue sameMid =>
                if key = key' ∧ number = number' then
                  (Term.follows rules checks body (cast (congrArg (Skel D) sameMid.symm) body')
                      ids st).bind fun afterBody =>
                    Term.follows rules checks rest rest'
                      (bindIds ids results (List.range' results' mid.length)) afterBody
                else none
            | isFalse _ => none
        | _ => none
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, skel, ids, st =>
        match skel with
        | .attempt (mid := mid') key' w' input' body' results' rest' =>
            match checks.sameWho w w', checks.sameTys mid mid' with
            | isTrue _, isTrue sameMid =>
                if key = key' then
                  (Term.follows rules checks body (cast (congrArg (Skel D) sameMid.symm) body')
                      (bindIds ids inputs (List.range' input' 1)) st).bind fun afterBody =>
                    Term.follows rules checks rest rest'
                      (bindIds ids results (List.range' results' mid.length)) afterBody
                else none
            | _, _ => none
        | _ => none
  /-- The arms of a term follow the arms of a skeleton. -/
  def Arms.follows (rules : ValueRules D Raw) [DecidableEq Raw] (checks : SkelRules D) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Arms D Γ mid payloads → SkelArms D mid payloads → Ctx Nat → St D.Ty Raw →
      Option (St D.Ty Raw)
    | _, _, _, .nil, .nil, _, st => some st
    | _, _, _, .cons inputs arm rest, .cons input' arm' rest', ids, st =>
        (Term.follows rules checks arm arm' (bindIds ids inputs (List.range' input' 1)) st).bind
          fun afterArm => Arms.follows rules checks rest rest' ids afterArm
end

variable [DecidableEq Raw] (rules : ValueRules D Raw)

/-! ## The decision -/

/-- Whether the second definition follows the skeleton of the first, with the inputs of both on
the same identifiers. -/
def same (checks : SkelRules D) {types outs : List D.Ty} (inputs inputs' : Names types)
    (t : Term D (Ctx.empty.extend inputs) outs) (t' : Term D (Ctx.empty.extend inputs') outs) :
    Bool :=
  let start : St D.Ty Raw := ⟨FactCheck.Table.empty rules.place, types.length, [], []⟩
  let first := t.skeleton rules (bindIds Ctx.empty inputs (List.range types.length)) start
  (t'.follows rules checks first.1 (bindIds Ctx.empty inputs' (List.range types.length))
    first.2).isSome

end

end Zkc.Core
