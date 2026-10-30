module

public import ZkcSecurity.Bindings.Participants.Compiled
public import Zkc.Construction.RetainedTarget

@[expose] public section

/-! Application meanings pinned to deterministic retained targets. The explicit
imported-language alternative is available only to contract-free fixtures. -/

set_option autoImplicit false
namespace ZkcSecurity.Endpoint
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- A declared external language for a fixture whose admitted original retains
no contracts. This is an explicit semantic import, not a retained-source claim.
The evidence must still prove coverage of exactly its complement. -/
structure ImportedLanguage {art : Artifacts} (_compiled : Compiled art) (F G : Type) where
  identifier : String
  noClauses : art.original.contracts.all (fun contract => contract.clauses.isEmpty) = true
  Model : Type
  read : art.Statement F G → Model
  language : Set Model

/-- The two distinct sources of an ordinary soundness claim's meaning. -/
inductive SoundnessTarget {art : Artifacts} (compiled : Compiled art) (F G : Type) where
  | retained (target : RetainedTarget compiled.imported art.participant.policy art.publics)
      (formula : FormulaBinding compiled.imported target.application.relation)
  | importedLanguage (declaration : ImportedLanguage compiled F G)

def SoundnessTarget.FalseStatement {art : Artifacts} {compiled : Compiled art} {F G : Type}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (target : SoundnessTarget compiled F G) (statement : art.Statement F G) : Prop :=
  match target with
  | .retained target formula => target.FalseStatement formula statement
  | .importedLanguage declaration => declaration.read statement ∉ declaration.language

end ZkcSecurity.Endpoint
