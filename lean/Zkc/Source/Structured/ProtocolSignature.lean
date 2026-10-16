module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section

namespace Zkc.Source.Structured

/-- Complete ordered protocol interface. Scopes retain their source order. -/
structure ProtocolSignature where
  name : String
  roles : List String
  inputs : List Ty
  outputs : List Ty
  inputScopes : List (List Nat)
  outputScopes : List (List Nat)
  deriving DecidableEq, Repr

end Zkc.Source.Structured
