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

/-- The actual operand types include all holders at this point in the caller. -/
structure Located {Γ : Ctx D.Ty} {outs : List D.Ty} (moves : List Move) (term : Term D Γ outs) where
  key : Key
  ins : List D.Ty
  res : List D.Ty
  op : D.Op ins res
  names : List Name
  found : Contains key op names moves term

def locate : (moves : List Move) → {Γ : Ctx D.Ty} → {outs : List D.Ty} → (term : Term D Γ outs) →
    Option (Located moves term)
  | [], _, _, .op key op args ns rest => some ⟨key,_,_,op,args.names,.here args ns rest rfl⟩
  | .next::moves, _, _, .step key _ _ rest => do
    let ⟨k,ins,res,op,ns,found⟩ ← locate moves rest
    return ⟨k,ins,res,op,ns,.next key found⟩
  | .fixedLoop key count::moves, _, _, .loop actual _ (.fixed n) _ _ _ inside _ _ =>
    if same : key = actual ∧ count = n then by
      obtain ⟨rfl,rfl⟩ := same
      exact do
        let ⟨k,ins,res,op,ns,found⟩ ← locate moves inside
        return ⟨k,ins,res,op,ns,.loop found⟩
    else none
  | _, _, _, _ => none

def Located.check {Γ : Ctx D.Ty} {outs : List D.Ty} {moves : List Move} {term : Term D Γ outs}
    (actual : Located moves term) (checks : SkelRules D) (exactOp : checks.Lawful)
    (key : Key) (op : D.Op ins res) (names : List Name) : Option (PLift (Contains key op names moves term)) := by
  letI := checks.sameTy
  obtain ⟨k,inputs,outputs,code,args,found⟩ := actual
  exact if types : inputs = ins then by
    subst inputs
    exact if same : checks.sameOp op code then by
      obtain ⟨rfl,eq⟩ := exactOp op code same
      cases eq_of_heq eq
      exact if identity : k = key ∧ args = names then by
        obtain ⟨rfl,rfl⟩ := identity
        exact some ⟨found⟩
      else none
    else none
  else none

def read (checks : SkelRules D) (exactOp : checks.Lawful) (key : Key) (op : D.Op ins res) (names : List Name)
    (moves : List Move) {Γ : Ctx D.Ty} {outs : List D.Ty} (term : Term D Γ outs) :
    Option (PLift (Contains key op names moves term)) := do
  let actual ← locate moves term
  actual.check checks exactOp key op names

end Zkc.Core.OperationSite
