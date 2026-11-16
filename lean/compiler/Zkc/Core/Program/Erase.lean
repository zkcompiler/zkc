module

public import Zkc.Core.Program.Elaborate

@[expose] public section

/-!
Erasure: the program by names of a typed term, and the round trip.

Erasing a term drops its contexts and its proofs: what is left is its instructions in order,
then its exit, with the names that the term keeps; the erased form of a region of an
instruction has the names of its inputs.

Erasure and elaboration are inverse to each other. For rules whose laws hold (`Rules.Lawful`:
what is written for an operation reads back as it), the erased form of a term whose case
analyses without an arm give nothing elaborates to the term. For rules whose written forms are
canonical (`Rules.Canonical`: an operation that a written form reads as is written as that
form), a term that elaboration gives erases to what was elaborated.
-/

namespace Zkc.Core

section
variable {D : Dialect} {Raw Who : Type}

/-! ## Erasure -/

/-- How often a loop runs, by names. -/
def eraseTimes {w : D.Who} {Γ : Ctx D.Ty} : Times D w Γ → Repeat
  | .fixed n => .fixed n
  | .value count _ => .count count.name

mutual
  /-- The instructions and the exit of a term, by names. -/
  def eraseBody (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List (Instruction Raw Who) × List Name
    | _, _, .ret exit => ([], HList.names exit)
    | _, _, .op key o operands results rest =>
        let erased := eraseBody printOp printWho rest
        (.op key results.toList (printOp o) (HList.names operands) :: erased.1, erased.2)
    | _, _, .guard key w c _ why rest =>
        let erased := eraseBody printOp printWho rest
        (.guard key (printWho w) c.name why :: erased.1, erased.2)
    | _, _, .choose key w c _ _ onTrue onFalse results rest =>
        let yes := eraseBody printOp printWho onTrue
        let no := eraseBody printOp printWho onFalse
        let erased := eraseBody printOp printWho rest
        (.choose key (printWho w) c.name results.toList (.mk [] yes.1 yes.2) (.mk [] no.1 no.2) ::
          erased.1, erased.2)
    | _, _, .cases key w x _ _ arms results rest =>
        let erased := eraseBody printOp printWho rest
        (.cases key (printWho w) x.name results.toList (eraseArms printOp printWho arms) ::
          erased.1, erased.2)
    | _, _, .loop key w times _ initial inputs body results rest =>
        let inside := eraseBody printOp printWho body
        let erased := eraseBody printOp printWho rest
        (.loop key (printWho w) (eraseTimes times) (HList.names initial) results.toList
            (.mk inputs.toList inside.1 inside.2) :: erased.1, erased.2)
    | _, _, .block key number body results rest =>
        let inside := eraseBody printOp printWho body
        let erased := eraseBody printOp printWho rest
        (.block key number results.toList (.mk [] inside.1 inside.2) :: erased.1, erased.2)
    | _, _, .attempt key w _ inputs body results rest =>
        let inside := eraseBody printOp printWho body
        let erased := eraseBody printOp printWho rest
        (.attempt key (printWho w) results.toList (.mk inputs.toList inside.1 inside.2) ::
          erased.1, erased.2)
  /-- The regions of the arms of a case analysis, each with the name of its payload. -/
  def eraseArms (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List (Region Raw Who)
    | _, _, _, .nil => []
    | _, _, _, .cons inputs arm rest =>
        let inside := eraseBody printOp printWho arm
        .mk inputs.toList inside.1 inside.2 :: eraseArms printOp printWho rest
end

end

/-- A decision of a proposition that holds. -/
theorem Decidable.eq_isTrue {p : Prop} (decision : Decidable p) (holds : p) :
    decision = isTrue holds := by
  cases decision with
  | isFalse fails => exact absurd holds fails
  | isTrue _ => rfl

section
variable {D : Dialect} {Raw Who : Type}

/-- The laws of the rules of a dialect: what erasure writes, the rules read back. -/
structure Rules.Lawful (rules : Rules D Raw Who) : Prop where
  op : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.op (rules.printOp o) ins = .ok ⟨res, o⟩
  who : ∀ w, rules.who (rules.printWho w) = .ok w
  alternatives : ∀ w t payloads, D.Alternatives w t payloads →
    ∃ ok, rules.alternatives w t = some ⟨payloads, ok⟩

/-- The other half of the laws: an operation that a written form reads as is written as that
form, and so is who performs. With it a region by names has one spelling. -/
structure Rules.Canonical (rules : Rules D Raw Who) : Prop where
  op : ∀ {ins res : List D.Ty} (raw : Raw) (o : D.Op ins res),
    rules.op raw ins = .ok ⟨res, o⟩ → rules.printOp o = raw
  who : ∀ (written : Who) (w : D.Who), rules.who written = .ok w → rules.printWho w = written

end

end Zkc.Core
