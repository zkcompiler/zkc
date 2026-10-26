import Zkc.Construction.OriginProjection

set_option autoImplicit false
open Zkc.Construction

-- Static field contents never act as delimiters, even when all spell `indices`.
example (request : Request) (coordinates : List Nat) :
    (Domain.atCoordinates (Origin.query "indices" "indices" "indices" "indices" "indices" request)
      coordinates).withoutCoordinates =
      Origin.query "indices" "indices" "indices" "indices" "indices" request :=
  Origin.withoutCoordinates_atCoordinates _ _ rfl

example (entry site sender receiver : String) (coordinates : List Nat) :
    (Domain.atCoordinates (Origin.message entry site sender receiver) coordinates).withoutCoordinates =
      Origin.message entry site sender receiver :=
  Origin.withoutCoordinates_atCoordinates _ _ rfl

-- A non-coordinate extension is preserved instead of blindly taking six fields.
example :
    (⟨"entry", ["query", "entry", "site", "port", "contract", "owner", "extension"],
      some (.draw "field")⟩ : Origin).withoutCoordinates =
      ⟨"entry", ["query", "entry", "site", "port", "contract", "owner", "extension"],
        some (.draw "field")⟩ := rfl

-- The old delimiter search would lose a real static field on this legal occurrence.
example :
    ((Domain.atCoordinates (Origin.query "entry" "site" "port" "contract" "indices" (.draw "field"))
      [0]).event.takeWhile (· != "indices")) ≠
      (Origin.query "entry" "site" "port" "contract" "indices" (.draw "field")).event := by
  decide
