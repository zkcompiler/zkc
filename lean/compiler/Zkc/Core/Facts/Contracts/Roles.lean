module

public import Zkc.Core.Facts.Contracts.Functions
public import Zkc.Core.Facts.Contracts.RoleOperations
public import Zkc.Core.Facts.Contracts.RoleIndex

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

variable {V : Vocabulary} {hs : Headers V}

mutual
  /-- Locate each application at the computation's holders. Arguments retain their own types. -/
  def expression (holders : Holders) : Expr (LocalRaw V) → Expr (RoleRaw V)
    | .arg i => .arg i
    | .apply op args result => .apply (.compute holders op) (expressions holders args) result
  def expressions (holders : Holders) : Exprs (LocalRaw V) → Exprs (RoleRaw V)
    | .nil => .nil
    | .cons e es => .cons (expression holders e) (expressions holders es)
end

def clause (holders : Holders) (c : ContractClause (LocalRaw V)) : ContractClause (RoleRaw V) :=
  ⟨expression holders c.assertion, c.staticBound.map (expression holders)⟩

def contract {fns : List (FnHeader V)} (catalog : FunctionContracts fns) : RoleRaw V → Contract (RoleRaw V)
  | .compute holders op =>
    let c := catalog.contract op
    ⟨c.preconditions.map (clause holders), c.postconditions.map (clause holders)⟩
  | _ => ⟨[], []⟩

def assertable {fns : List (FnHeader V)} (catalog : FunctionContracts fns) (r : Role) : RoleRaw V → Bool
  | .compute holders op => decide (r ∈ holders) && catalog.assertable op
  | .absent types => decide (∀ a ∈ types, r ∉ a.holders)
  | .keep _ => true
  | _ => false

def rules (catalog : FunctionContracts hs.fns) (r : Role) : Rules (roleDialect V hs r) (RoleRaw V) where
  written := roleWritten
  shared := roleShared
  observedOperand
    | .keep holders _ => if r ∈ holders then some 0 else none
    | .give .. => some 0
    | _ => none
  commutes
    | .compute _ op => LocalRaw.commutes op
    | _ => false
  place
    | .compute _ op => 2 * localPlace op
    | _ => 1
  results := roleResultCount hs
  contract := contract catalog
  assertable := assertable catalog r
  numbered w := decide (r ∈ w)
  indexAt w n := some (RoleIndex.atIteration r w n)
  indexFromCount := fun {w _} _ => some (RoleIndex.fromCount w)
  indexNext w := some (RoleIndex.next r w)

/-- Every projected callee runs safely on valid inputs and permitted replies at its actual role. -/
def RCallees (M : Model V) {headers : List (ProtocolHeader V)} (roles : RTable M headers) : Prop :=
  ∀ hdr (callee : Member headers hdr) (j : Role) (path : List Frame) (args : HList (RV M j) hdr.ins),
    args.All (RV.Valid M j) →
    (roles hdr callee j path args).Every (Permitted M) (fun outs => outs.All (RV.Valid M j))
      (· ≠ .undefined)

end Zkc.Core.BodyAnalysis.RoleContracts
