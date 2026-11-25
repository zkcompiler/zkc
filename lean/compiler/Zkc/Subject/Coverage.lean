module

public import Zkc.Core.Program.Links
public import Zkc.Vocabulary.Project

@[expose] public section

namespace Zkc.Subject.Coverage
open Zkc.Core Zkc.Vocabulary.Project

/-- Definition keys used by the body, including calls inside nested regions. -/
def callees {V : Core.Vocabulary} : Definition V → List Key
  | .fn _ _ _ _ _ _ body _ => body.operations.filterMap fun
      | .call k => some k
      | _ => none
  | .protocol _ _ _ _ body => body.operations.filterMap fun
      | .apply k _ | .compute _ (.call k) => some k
      | _ => none

/-- Admitted definitions follow their dependencies. Walking backwards visits each reached
definition once, starting at the protocol and the function for its goal's relation. -/
def reach {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) :
    List Key × List (Definition V) :=
  p.definitions.foldr (fun d (state : List Key × List (Definition V)) =>
    if d.key ∈ state.1 then (callees d ++ state.1, d :: state.2) else state) ([root, relation], [])

abbrev Nominal := Sum Zkc.Vocabulary.TypeKey Parameter
abbrev Row := Sum Zkc.Vocabulary.RowKey PrimitiveName

mutual
  /-- The first nominal sort in a type without a standard interpretation. -/
  def missingSort : LinkedType → Option Nominal
    | .nominal (.inl (.field .bls12381Fr)) | .nominal (.inl (.nonzero .bls12381Fr))
      | .nominal (.inl (.group .g1)) => none
    | .nominal k => some k
    | .seq t _ => missingSort t
    | .tuple ts | .record _ _ ts | .variant _ ts => missingSorts ts
    | .bool | .nat | .fin _ => none
  def missingSorts : Tys Nominal → Option Nominal
    | .nil => none
    | .cons t ts => missingSort t <|> missingSorts ts
end

/-- The formal library proves that this predicate agrees with its semantic row table. -/
def interpreted : Row → Bool
  | .inl (.group .scale (.group .g1)) => true
  | .inl (.group .add (.group .g1)) => true
  | .inl (.group .equal (.group .g1)) => true
  | .inl (.field .add .bls12381Fr .all) => true
  | .inl (.field .sub .bls12381Fr .all) => true
  | .inl (.field .mul .bls12381Fr .all) => true
  | .inl (.field .neg .bls12381Fr .all) => true
  | .inl (.field .equal .bls12381Fr .all) => true
  | .inl (.field .nonzero .bls12381Fr .all) => true
  | .inl (.field .isNonzero .bls12381Fr .all) => true
  | .inl (.field .inverse .bls12381Fr .nonzero) => true
  | .inl (.field .fromNonzero .bls12381Fr .nonzero) => true
  | .inl (.seq .add (.atom (.field .bls12381Fr)) (some _)) => true
  | .inl (.seq .sub (.atom (.field .bls12381Fr)) (some _)) => true
  | .inl (.seq .scale (.atom (.field .bls12381Fr)) (some _)) => true
  | .inl (.seq .sum (.atom (.field .bls12381Fr)) _) => true
  | .inl (.seq .equal (.atom (.field .bls12381Fr)) _) => true
  | _ => false

def positionSampled : Zkc.Vocabulary.Ty → LinkedType → Bool
  | .fin (n + 1), .fin m => m == n + 1
  | _, _ => false

def sampledType : Zkc.Vocabulary.Ty → LinkedType → Bool
  | .nominal (.field .bls12381Fr), .nominal (.inl (.field .bls12381Fr)) => true
  | .seq (.nominal (.field .bls12381Fr)) (some n),
      .seq (.nominal (.inl (.field .bls12381Fr))) (some m) => m == n
  | t, result => positionSampled t result

def localSort {b : Bindings} : LocalRaw b.vocabulary → Option Nominal
  | .owned _ ts _ => ts.findSome? missingSort
  | .literal t _ => missingSort t
  | .row _ | .call _ => none

def definitionSort {b : Bindings} : Definition b.vocabulary → Option Nominal
  | .fn _ ins outs _ _ _ body _ =>
    (ins ++ outs).findSome? missingSort <|> body.operations.findSome? (localSort (b := b))
  | .protocol _ _ ins outs body =>
    (ins ++ outs).findSome? (fun port => missingSort port.ty) <|> body.operations.findSome? fun
      | .compute _ op => localSort (b := b) op
      | .event _ t => missingSort t
      | _ => none

inductive Missing where
  | definition (key : Key)
  | sort (key : Nominal)
  | row (key : Row)
  | law (key : Zkc.Vocabulary.LawKey) (result : LinkedType)

/-- Read both entry points from the same stored program. Report an unsupported row or law
before its types, so that a diagnostic about an operation identifies the operation. -/
def missing {b : Bindings} (p : NamedProgram b.vocabulary) (root relation : Key) : Option Missing := do
  let (keys, defs) := reach p root relation
  if let some k := keys.find? (fun k => !defs.any (·.key == k)) then return .definition k
  let reached : NamedProgram b.vocabulary := ⟨defs⟩
  if let some k := reached.rows.find? (!interpreted ·) then return .row k
  if let some (.uniform t, result) := reached.laws.find? (fun (.uniform t, result) => !sampledType t result)
  then return .law (.uniform t) result
  return .sort (← defs.findSome? (definitionSort (b := b)))

end Zkc.Subject.Coverage
