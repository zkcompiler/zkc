import Tests.ConnectionTargetPlacement
import Tests.ConnectionFamilyMetrics

/-! Inspect closed, kernel-checked, registered declarations. An unused extra
premise is still caller work and must not disappear from the interface audit. -/

namespace Tests.ConnectionFamilyAudit

-- A transparent wrapper must not turn classical reflection into finite work.
noncomputable def classicalCheck (proposition : Prop) : Bool :=
  @decide proposition (Classical.propDecidable proposition)

def finiteCheck (values : List Nat) : Bool := decide (values.length ≤ values.length + 1)
opaque opaqueCheck : Bool := true

def processLeft : PIR.Process ⟨Nat, fun _ => Nat⟩ Nat := .call 0 (fun x => .done x)
def processRight : PIR.Process ⟨Nat, fun _ => Nat⟩ Nat := .call 0 (fun x => .done (x + 0))

end Tests.ConnectionFamilyAudit

public meta section
namespace Tests.ConnectionFamilyAudit
open Lean Meta Elab Command Term
open ZkcTools.ConstructionBindings

run_cmd liftTermElabM do
  let source := ``Tests.ConnectionTargetPlacement.checkedStep
  let info ← getConstInfo source
  Interface.auditFamilyType info.type
  let levels := info.levelParams.map Level.param
  -- A kernel-added transparent wrapper has no compiler provenance yet and
  -- must be inspected even without a `noncomputable` tag.
  let wrapperName := `Tests.ConnectionFamilyAudit.uncompiledClassical
  let wrapperValue ← elabTerm (← `(classicalCheck (processLeft = processRight))) (some (mkConst ``Bool))
  Term.synthesizeSyntheticMVarsNoPostponing
  let wrapperValue ← instantiateMVars wrapperValue
  withOptions (Elab.async.set · false) <| addDecl (.defnDecl {
    name := wrapperName, levelParams := [], type := mkConst ``Bool, value := wrapperValue,
    hints := .abbrev, safety := .safe })
  for (suffix, typeSyntax) in [
      ("proposition", ← `(True)),
      ("propositionParameter", ← `(Prop)),
      ("propositionContainer", ← `(List Prop)),
      ("function", ← `(Nat → Nat)),
      ("functionEquality", ← `((fun x : Nat => x) = (fun x => x))),
      ("propositionEquality", ← `(True = True)),
      ("classicalFunctionEquality", ← `(
        @decide ((fun x : Nat => x) = (fun x => x + 0)) (Classical.propDecidable _) = true)),
      ("wrappedClassicalFunctionEquality", ← `(
        classicalCheck ((fun x : Nat => x) = (fun x => x + 0)) = true)),
      ("classicalProcessEquality", ← `(
        @decide (processLeft = processRight) (Classical.propDecidable _) = true)),
      ("wrappedClassicalProcessEquality", ← `(
        classicalCheck (processLeft = processRight) = true)),
      ("classicalNaturalEncoding", ← `(
        Bool.toNat (classicalCheck ((fun x : Nat => x) = (fun x => x + 0))) = 1)),
      ("uncompiledClassicalEquality", ← `($(mkIdent wrapperName) = true)),
      ("opaqueComputation", ← `(opaqueCheck = true))] do
    forallTelescope info.type fun parameters result => do
      let extraType ← elabType typeSyntax
      Term.synthesizeSyntheticMVarsNoPostponing
      let extraType ← instantiateMVars extraType
      withLocalDeclD `forbidden extraType fun extra => do
        let type ← mkForallFVars (parameters.push extra) result
        let value ← mkLambdaFVars (parameters.push extra)
          (mkAppN (mkConst source levels) parameters)
        let name := `Tests.ConnectionFamilyAudit ++ Name.mkSimple suffix
        let declaration ← mkDefinitionValInferringUnsafe name info.levelParams type value
          (.regular (getMaxHeight (← getEnv) value + 1))
        withOptions (Elab.async.set · false) <| addDecl (.defnDecl declaration)
        modifyEnv fun env => addNoncomputable (TargetPlacement.checkedBodies.addEntry env name) name
        let registered := TargetPlacement.checkedBodies.getState (← getEnv)
        unless registered.contains name do throwError "negative family was not registered"
        let refused ← try
          Interface.auditFamilyType (← getConstInfo name).type
          pure false
        catch error =>
          if error.isInterrupt || error.isRuntime then throw error
          let message ← error.toMessageData.toString
          unless message.startsWith "connection-family-forbidden-parameter: forbidden" do
            throwError "unexpected refusal: {message}"
          pure true
        unless refused do throwError "forbidden family interface was accepted: {name}"
        -- Registration alone cannot bypass the same audit at actual reuse.
        -- Isolate this candidate so another valid family cannot mask it.
        let environment ← getEnv
        let solverInvoked ← IO.mkRef false
        try
          modifyEnv fun env => TargetPlacement.checkedBodies.modifyState env fun _ => #[name]
          let checked := mkAppN (mkConst source levels) parameters
          let alignment ← mkAppM ``Zkc.Construction.ConnectionTargetPlacement.CheckedBody.alignment #[checked]
          let goal ← mkFreshExprSyntheticOpaqueMVar (← inferType alignment)
          let _ ← Tactic.run goal.mvarId! do
            let used ← TargetPlacement.propose goal.mvarId! result.getAppArgs[2]!
              result.getAppArgs.back! fun _ => do
                solverInvoked.set true
                throwError "forbidden family reached interface proof search"
            unless used.isNone && !(← goal.mvarId!.isAssigned) do
              throwError "forbidden family was reused: {name}"
          if ← solverInvoked.get then throwError "forbidden interface reached its solver: {name}"
        finally
          setEnv environment
        logInfo m!"FAMILY-POLICY-REFUSED {name}"

  -- The computation vocabulary is open: a new constructive wrapper needs no
  -- protocol-specific entry in the policy. The kernel still checks the family.
  for (suffix, typeSyntax) in [
      ("constructiveWrapper", ← `(finiteCheck [0, 1] = true)),
      ("plainBoolean", ← `(Bool)),
      ("plainNaturals", ← `(List Nat)),
      ("finiteApplication", ← `(
        decide (Zkc.Construction.ConnectionFrame.applicationAdmitted 1 2 [.data 1] none) = true)),
      ("finiteHistory", ← `(
        Zkc.Construction.ConnectionTargetPlacement.historySeparationCheck [.data 1] (some 0) = true)),
      ("finiteRoster", ← `(
        Zkc.Construction.ConnectionFrame.rosterCheck {} 1 2 = true)),
      ("requestIdentity", ← `(
        (some (Zkc.Construction.Request.draw "field") : Option Zkc.Construction.Request) =
          some ⟨"draw", [], .field "field"⟩))] do
    forallTelescope info.type fun parameters result => do
      let extraType ← elabType typeSyntax
      Term.synthesizeSyntheticMVarsNoPostponing
      let extraType ← instantiateMVars extraType
      withLocalDeclD `finite extraType fun extra => do
        let type ← mkForallFVars (parameters.push extra) result
        let value ← mkLambdaFVars (parameters.push extra)
          (mkAppN (mkConst source levels) parameters)
        let name := `Tests.ConnectionFamilyAudit ++ Name.mkSimple suffix
        let declaration ← mkDefinitionValInferringUnsafe name info.levelParams type value
          (.regular (getMaxHeight (← getEnv) value + 1))
        withOptions (Elab.async.set · false) <| addDecl (.defnDecl declaration)
        modifyEnv fun env => addNoncomputable (TargetPlacement.checkedBodies.addEntry env name) name
        Interface.auditFamilyType (← getConstInfo name).type
        logInfo m!"FAMILY-POLICY-ACCEPTED {name}"

end Tests.ConnectionFamilyAudit
