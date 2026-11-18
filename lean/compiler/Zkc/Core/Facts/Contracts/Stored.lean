module

public import Zkc.Core.Facts.Contracts.LocalReader
public import Zkc.Core.Facts.Contracts.LocalOperations
public import Zkc.Core.Facts.Local

@[expose] public section

namespace Zkc.Core.BodyAnalysis
namespace HeaderContracts
variable {V : Vocabulary}
abbrev Assertion (V : Vocabulary) := Expr (LocalRaw V)

def unary (op : LocalRaw V) (arg : Assertion V) : Assertion V := .apply op (.cons arg .nil) 0
def binary (op : LocalRaw V) (a b : Assertion V) : Assertion V := .apply op (.cons a (.cons b .nil)) 0
def number (n : Nat) : Assertion V := .apply (.literal .nat [n]) .nil 0
def less (a b : Assertion V) := binary (.owned .natLess [] []) a b
def equal (a b : Assertion V) := binary (.owned .natEqual [] []) a b
def add (a b : Assertion V) := binary (.owned .natAdd [] []) a b
def negate (a : Assertion V) := unary (.owned .boolNot [] []) a

/-- A positive lower bound on a natural is a strict comparison with its predecessor.
The zero case still checks the numeric operand. -/
def atLeast (a : Assertion V) : Nat → Assertion V
  | 0 => equal a a
  | n+1 => less (number n) a

/-- An old header can only refer to its arguments and results by position. -/
def position : Operand Empty → Nat
  | .arg n => n
  | .apply impossible _ => nomatch impossible

def natural (types : List V.Ty) (operand : Operand Empty) : Option (Assertion V) := do
  let i := position operand
  match ← types[i]? with
  | .nat => return .arg i
  | .fin n => return unary (.owned .finToNat [.fin n] []) (.arg i)
  | _ => none

/-- The static upper-bound demand of a legacy bounded clause is observable at checking time.
Its semantic obligation only asks that the argument read as a natural. -/
abbrev Clause (V : Vocabulary) := ContractClause (LocalRaw V)

def clauseWith {m : Type → Type} [Monad m] {Raw : Type}
    (asNat asBool : Operand Raw → m (Assertion V)) : Requirement Raw → m (Clause V)
  | .le a b => do return ⟨negate (less (← asNat b) (← asNat a)), none⟩
  | .lt a b => do return ⟨less (← asNat a) (← asNat b), none⟩
  | .atLeast a n => do return ⟨atLeast (← asNat a) n, none⟩
  | .below a n => do return ⟨less (← asNat a) (number n), none⟩
  | .exactly a n => do return ⟨equal (← asNat a) (number n), none⟩
  | .difference b a n => do
    let x ← asNat b
    let y ← asNat a
    -- Natural subtraction truncates. A zero difference also holds when x is smaller.
    return ⟨if n = 0 then negate (less y x) else equal (add y (number n)) x, none⟩
  | .holds a => do
    return ⟨← asBool a, none⟩
  | .bounded a => do
    let x ← asNat a
    return ⟨equal x x, some x⟩

def boolean (types : List V.Ty) (a : Operand Empty) : Option (Assertion V) := do
  let i := position a
  guard ((← types[i]?) = .bool)
  return .arg i

def clause (types : List V.Ty) : Requirement Empty → Option (Clause V) :=
  clauseWith (natural types) (boolean types)

/-- A header is read in the vocabulary alone. Use the domain requirements of the
resolved operation, including the vocabulary's declared domain row. -/
def stableAllowed (raw : LocalRaw V) : Bool :=
  match resolveLocal [] raw with
  | some ⟨_, _, op⟩ => !op.canStop && ((localOpFacts []).requires raw).isEmpty
  | none => false

def stableTypes (V : Vocabulary) := localAssertionTypes (V := V) [] stableAllowed

def numeric : V.Ty → Bool
  | .nat | .fin _ => true
  | _ => false

def checkClause (context : List V.Ty) : HeaderClause V → Option (Clause V)
  | .positional q => clause context q
  | .assertion c =>
    if (stableTypes V).infer context c.assertion = some .bool &&
        c.staticBound.all (fun e => ((stableTypes V).infer context e).any numeric) then
      some c
    else none

def translate (ins outs : List V.Ty) (old : HeaderSummary V) : Option (Contract (LocalRaw V)) := do
  let before ← old.requires.mapM (checkClause ins)
  let after ← old.ensures.mapM (checkClause (ins ++ outs))
  return ⟨before, after⟩

end HeaderContracts
end Zkc.Core.BodyAnalysis
