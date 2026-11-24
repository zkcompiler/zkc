module

public import Zkc.Core.Facts.Contracts.RoleLaws
public import Zkc.Core.Facts.Knowledge.Roles
public import Zkc.Core.Facts.Contracts.RoleReaderLaws
public import Zkc.Core.Facts.Contracts.FunctionSetting

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

variable {V : Vocabulary} {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
variable (definition : Key) (lemmas : List (Lemma (LTy V) (RoleRaw V)))

variable (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
variable (notes : Annotations (RoleRaw V)) (bounds : List (Place × Nat))

def setting : Setting (roleDialect V hs r) (RoleRaw V) where
  cfg := config catalog r definition lemmas
  sem := roleSem M r fns roles
  notes := notes
  permitted := Permitted M
  R := roleReading M r
  Run := RoleReturns M r fns roles
  Valid := RoleValueValid M r
  undefined := (· = .undefined)
  domain := roleDomainLawful M r fns roles catalog.distinct
  F := bounds

/-- Every required assertion denotes on every valid input of the actual located operand types. -/
theorem requiresDefined :
    RequiresDefined (setting catalog r definition lemmas M fns roles notes bounds) := by
  intro ins outs op e mem args valid
  cases op with
  | compute R op ins types mine here =>
    subst types
    change e ∈ (contract catalog (.compute R op.print)).requires at mem
    rw [requires_compute] at mem
    obtain ⟨source, listed, rfl⟩ := List.mem_map.mp mem
    have corr := compute_corr M r fns roles here args
    obtain ⟨v, named⟩ := catalog.requiresDefined M fns definition [] [] [] [] op source listed _
      ((corr_valid corr).mp valid)
    obtain ⟨d, den, _⟩ := denotes_toRole (roles := roles) mine corr source named
    exact ⟨d, den⟩
  | absent | keep | give | get | own | hear | apply => cases mem

theorem settingLawful (callees : Callees M fns) (rcallees : RCallees M roles)
    (sound : ∀ l ∈ lemmas, l.Valid (RoleRuns M r fns roles) (roleReading M r)
      (TypedValue (roleSem M r fns roles) (RoleValueValid M r))) :
    (setting catalog r definition lemmas M fns roles notes bounds).Lawful :=
  ⟨lawful catalog r M fns roles callees rcallees, sound,
    requiresDefined catalog r definition lemmas M fns roles notes bounds⟩

theorem readerLawful (callees : Callees M fns) :
    (config catalog r definition lemmas).assertions.Lawful
      (setting catalog r definition lemmas M fns roles notes bounds) :=
  roleAssertionTypes_lawful _ (assertionLaws catalog r M fns roles callees)
    (fun {_ _} op {_} printed => roleValueForm_written op printed)
    (fun passes _ typed => roleAssertionBool M fns roles passes typed)

section

/-- A finite operand's static bound and the returned natural's bound at a located call. -/
private def boundedHeader (V : Vocabulary) : FnHeader V :=
  ⟨⟨11⟩, [.fin 4], [.nat], false, none, ⟨[.bounded (.arg 0)], [.bounded (.arg 1)]⟩⟩

example :
    ((FunctionContracts.check [boundedHeader V]).toOption.map fun checked =>
      let c := contract checked (.compute [2] (.call ⟨11⟩))
      (c.preconditions.map ContractClause.staticBound, c.postconditions.map ContractClause.staticBound)) =
    some ([some (.apply (.compute [2] (.owned .finToNat [.fin 4] [])) (.cons (.arg 0) .nil) 0)],
      [some (.arg 1)]) := by rfl'

example (checked : FunctionContracts hs.fns) :
    (config checked 2 definition lemmas).assertions.signature
      (.compute [2] (.owned .natLess [] [])) [⟨.nat,[2,7]⟩, ⟨.nat,[2]⟩] =
      some [⟨.bool,[2]⟩] := by rfl'

end

end Zkc.Core.BodyAnalysis.RoleContracts
