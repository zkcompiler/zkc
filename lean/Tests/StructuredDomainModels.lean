import Zkc.Source.Structured.DomainTransfer
import Mathlib.Data.ZMod.Basic

/-! Controls for evaluation over domain models.

One model reads two field identities with two different carriers, `ZMod 5`
and `ZMod 7`, resolving the identity string once to its own case. Arithmetic
at each identity uses that identity's ring, and the same uniform-carrier
operation names stay available for the existing interpretation. -/

set_option autoImplicit false

namespace Tests.StructuredDomainModels
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Evaluation

inductive Case where
  | small | large
  deriving DecidableEq

def resolve (identity : String) : Case :=
  if identity = "small" then .small else .large

/-- The carrier of each case. Not reducible, with declared instances. -/
def carrier : Case → Type
  | .small => ZMod 5
  | .large => ZMod 7

instance (c : Case) : CommRing (carrier c) := by
  cases c <;> unfold carrier <;> infer_instance

instance (c : Case) : DecidableEq (carrier c) := by
  cases c <;> unfold carrier <;> infer_instance

/-- Two field carriers; every group identity reads `ZMod 5` with a trivial
action, which these controls do not use. -/
def model : DomainModel where
  Field identity := carrier (resolve identity)
  Group _ := ZMod 5
  fieldRing _ := inferInstance
  fieldDecEq _ := inferInstance
  inverse _ := none
  embed _ _ _ := 0
  groupAdd _ := inferInstanceAs (AddCommGroup (ZMod 5))
  groupDecEq _ := inferInstanceAs (DecidableEq (ZMod 5))
  smul _ _ _ point := point

def small (value : ZMod 5) : model.Field "small" := value
def large (value : ZMod 7) : model.Field "large" := value

-- Addition at each identity uses that identity's ring.
example : operationOn model SiteObservations.closed [] (.fieldAdd "small")
    (.cons (small 3) (.cons (small 4) .nil)) .nil = .done (.cons (small 2) .nil) := rfl

example : operationOn model SiteObservations.closed [] (.fieldAdd "large")
    (.cons (large 3) (.cons (large 4) .nil)) .nil = .done (.cons (large 0) .nil) := rfl

-- Field constants are read in the identity's carrier.
example : operationOn model SiteObservations.closed [] (.fieldConstant "small" 9) .nil .nil =
    .done (.cons (small 4) .nil) := rfl

-- The uniform carriers give the uniform values by definition.
example (F G : Type) : (uniformCarriers F G).Value = assignment F G := by with_reducible rfl

-- Models that differ only in the inverse agree on every current body.
example {Γ out : List Ty} (region : Region dialect Γ out) :
    region.denote (meaningOn (model.withInverse fun _ => none) SiteObservations.closed []) =
      region.denote (meaningOn model SiteObservations.closed []) :=
  denote_inverse_free model (fun _ => none) SiteObservations.closed [] region (inverse_free region)

end Tests.StructuredDomainModels
