module

public import Zkc.Core.Program.Erase

@[expose] public section
namespace Zkc.Core.OperationSite
variable {D : Dialect} {ins res : List D.Ty}

/-- Descent from a protocol entry to a specific executable instruction. -/
inductive Move where
  | next
  | fixedLoop (key : Key) (count : Nat)
  deriving DecidableEq

inductive Contains (key : Key) (op : D.Op ins res) (names : List Name) :
    {Γ : Ctx D.Ty} → {outs : List D.Ty} → List Move → Term D Γ outs → Prop where
  | here {Γ outs} (args : HList (Var Γ) ins) (ns : Names res) (rest : Term D (Γ.extend ns) outs)
      (same : args.names = names) : Contains key op names [] (.op key op args ns rest)
  | next {Γ outs mid moves} {instruction : Instr D Γ mid} {ns : Names mid} {rest : Term D (Γ.extend ns) outs}
      (atKey : Key) (found : Contains key op names moves rest) :
      Contains key op names (.next::moves) (.step atKey instruction ns rest)
  | loop {Γ outs carried each moves} {w : D.Who} {count : Nat} {gives : ∀ a, a ∈ carried ++ each → D.Gives w a}
      {start : HList (Var Γ) carried} {inputs : Names (D.index w :: carried)}
      {inside : Term D (Γ.extend inputs) (carried ++ each)} {loopKey : Key} {ns : Names (carried ++ each.map (D.collected (some count)))}
      {rest : Term D (Γ.extend ns) outs} (found : Contains key op names moves inside) :
      Contains key op names (.fixedLoop loopKey count::moves) (.loop loopKey w (.fixed count) gives start inputs inside ns rest)

def read (checks : SkelRules D) (exactOp : checks.Lawful) (key : Key) (op : D.Op ins res) (names : List Name) :
    (moves : List Move) → {Γ : Ctx D.Ty} → {outs : List D.Ty} → (term : Term D Γ outs) →
      Option (PLift (Contains key op names moves term))
  | [], _, _, .op (ins := actualIns) atKey actual args ns rest => by
    letI := checks.sameTy
    exact if types : actualIns = ins then by
      subst actualIns
      exact if k : atKey = key then by
        subst atKey
        exact if code : checks.sameOp op actual then by
          obtain ⟨rfl,eq⟩ := exactOp op actual code
          cases eq_of_heq eq
          exact if operands : args.names = names then some ⟨.here args ns rest operands⟩ else none
        else none
      else none
    else none
  | .next::moves, _, _, .step atKey _ _ rest => do
    let ⟨found⟩ ← read checks exactOp key op names moves rest
    return ⟨.next atKey found⟩
  | .fixedLoop key' count'::moves, _, _, .loop loopKey _ (.fixed count) _ _ _ inside _ _ =>
    if same : key' = loopKey ∧ count' = count then by
      obtain ⟨rfl,rfl⟩ := same
      exact do
        let ⟨found⟩ ← read checks exactOp key op names moves inside
        return ⟨.loop found⟩
    else none
  | _, _, _, _ => none

end Zkc.Core.OperationSite
