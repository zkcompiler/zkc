module

public import Zkc.Core.LegalSites
public import Zkc.Core.Thread

public section

/-! The sites of a protocol region, as a list.

`regionSites` lists the sites of the operations of a region, nested regions and every arm
of a `choose` included, in the order in which the check of a definition collects them:
the pass of the check returns them before the sites it met earlier
(`protocolRegionSites_collects`). The sites of a well-formed definition are pairwise
different (`ProtocolDefinition.regionSites_nodup`).

`ProtocolOp.sites_exchange` and the equations after it say which site an operation has.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Sites

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

mutual
  /-- The sites of the operations of a region, the latest first. -/
  @[expose] def regionSites {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → List Nat
    | .ret _ => []
    | .stop _ => []
    | .bind body rest => regionSites rest ++ regionSites body
    | .letOp op _ bodies rest =>
        regionSites rest ++ (regionsSites bodies ++ ProtocolOp.sites op)

  @[expose] def regionsSites {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → List Nat
    | .nil => []
    | .cons body tail => regionsSites tail ++ regionSites body
end

mutual
  /-- The pass of the check over a region returns the sites of the region before the
  sites met so far. -/
  theorem protocolRegionSites_collects (typeTable : TypeTable) (roles : Nat) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (enclosing : Option (List Nat)) (sites result : List Nat),
        protocolRegionSites typeTable roles enclosing region sites = .ok result →
          result = regionSites region ++ sites
    | .ret _, _, _, _, checked => by
        unfold protocolRegionSites at checked
        cases checked
        rfl
    | .stop _, _, _, _, checked => by
        unfold protocolRegionSites at checked
        cases checked
    | .bind (mid := mid) body rest, enclosing, sites, result, checked => by
        unfold protocolRegionSites at checked
        cases named : Located.allNamed typeTable mid with
        | false =>
            rw [named] at checked
            cases checked
        | true =>
            rw [named] at checked
            simp only [Bool.cond_true] at checked
            split at checked
            · cases checked
            · rename_i bodySites bodyChecked
              rw [protocolRegionSites_collects typeTable roles rest enclosing bodySites result
                  checked,
                protocolRegionSites_collects typeTable roles body enclosing sites bodySites
                  bodyChecked]
              exact (List.append_assoc _ _ _).symm
    | .letOp op _ bodies rest, enclosing, sites, result, checked => by
        unfold protocolRegionSites at checked
        split at checked
        · cases checked
        · cases named : Located.allNamed typeTable (ProtocolOp.results op) with
          | false =>
              rw [named] at checked
              cases checked
          | true =>
              rw [named] at checked
              simp only [Bool.cond_true] at checked
              split at checked
              · cases checked
              · rename_i nestedSites nestedChecked
                rw [protocolRegionSites_collects typeTable roles rest enclosing nestedSites result
                    checked,
                  protocolRegionsSites_collects typeTable roles bodies
                    (ProtocolOp.enclosing enclosing op) _ nestedSites nestedChecked]
                show _ = (regionSites rest ++ (regionsSites bodies ++ ProtocolOp.sites op)) ++ sites
                simp only [List.append_assoc]

  theorem protocolRegionsSites_collects (typeTable : TypeTable) (roles : Nat)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (enclosing : Option (List Nat)) (sites result : List Nat),
        protocolRegionsSites typeTable roles enclosing regions sites = .ok result →
          result = regionsSites regions ++ sites
    | .nil, _, _, _, checked => by
        unfold protocolRegionsSites at checked
        cases checked
        rfl
    | .cons body tail, enclosing, sites, result, checked => by
        unfold protocolRegionsSites at checked
        split at checked
        · cases checked
        · rename_i bodySites bodyChecked
          rw [protocolRegionsSites_collects typeTable roles tail enclosing bodySites result checked,
            protocolRegionSites_collects typeTable roles body enclosing sites bodySites bodyChecked]
          exact (List.append_assoc _ _ _).symm
end

/-- The sites of a well-formed definition are pairwise different. -/
theorem ProtocolDefinition.regionSites_nodup {typeTable : TypeTable} {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header}
    (wellFormed : definition.violation typeTable = none) : (regionSites definition.body).Nodup := by
  obtain ⟨sites, collected, nodup⟩ := ProtocolDefinition.sites_nodup wellFormed
  have same := protocolRegionSites_collects typeTable header.roles definition.body none [] sites
    collected
  rw [same, List.append_nil] at nodup
  exact nodup

/-! ## The site of an operation -/

theorem ProtocolOp.sites_at (role : Nat) (op : LocalOp operations functions deployed)
    (bodies : Regions (LocalDialect operations functions deployed) op.regions) :
    ProtocolOp.sites (protocols := protocols) (.at role op bodies) = [] := by rfl

theorem ProtocolOp.sites_exchange (sender receiver site : Nat) (type : Ty) :
    ProtocolOp.sites (operations := operations) (functions := functions) (protocols := protocols)
      (deployed := deployed) (.exchange sender receiver site type) = [site] := by rfl

theorem ProtocolOp.sites_draw (owner : Nat) (receivers : List Nat) (site : Nat) {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true) :
    ProtocolOp.sites (functions := functions) (protocols := protocols) (deployed := deployed)
      (.draw owner receivers site law populated) = [site] := by rfl

theorem ProtocolOp.sites_sample (owner site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true) :
    ProtocolOp.sites (functions := functions) (protocols := protocols) (deployed := deployed)
      (.sample owner site law populated) = [site] := by rfl

theorem ProtocolOp.sites_repeat (participants : List Nat) (count : RepeatCount)
    (carried collected captures : List Located)
    (covered : Located.heldBy participants collected = true) :
    ProtocolOp.sites (operations := operations) (functions := functions) (protocols := protocols)
      (deployed := deployed) (.repeat participants count carried collected captures covered) =
        [] := by rfl

theorem ProtocolOp.sites_choose (participants : List Nat) (tag : ChoiceTag)
    (captures outputs : List Located) (covered : Located.heldBy participants outputs = true) :
    ProtocolOp.sites (operations := operations) (functions := functions) (protocols := protocols)
      (deployed := deployed) (.choose participants tag captures outputs covered) = [] := by rfl

theorem ProtocolOp.sites_apply {header : ProtocolHeader} (callee : Var protocols header)
    (roleMap : RoleMap) (site : Nat)
    (permitted : (deployed && header.specificationOnly) = false) :
    ProtocolOp.sites (operations := operations) (functions := functions)
      (.apply callee roleMap site permitted) = [site] := by rfl

end Sites

end Zkc.Core
