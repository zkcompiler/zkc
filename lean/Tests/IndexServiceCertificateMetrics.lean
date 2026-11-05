import Tests.IndexServiceCertificateRefusals
import Tests.ConnectionProfileCertificate
import Lean.Elab.Command
import Lean.Util.NumObjs

/-! Deterministic inspection of generated proofs. Counts describe these tiny
checked declarations; they are not runtime or large-package timing claims. -/
public meta section
open Lean Meta Elab Command

namespace Tests.IndexServiceCertificateMetrics

def occurrences (expression : Expr) (selected : Name → Bool) : Nat :=
  (go expression).run' {}
where
  go (expression : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some count := (← get)[expression]? then return count
    let count ← match expression with
      | .const name _ => pure (if selected name then 1 else 0)
      | .app function argument => return (← go function) + (← go argument)
      | .lam _ type body _ | .forallE _ type body _ => return (← go type) + (← go body)
      | .letE _ type value body _ => return (← go type) + (← go value) + (← go body)
      | .mdata _ body | .proj _ _ body => go body
      | _ => pure 0
    modify (·.insert expression count)
    return count

def retained (name : Name) : Bool :=
  (name.toString.splitOn "retainedConnectionAlignment").length > 1

/-- Traverse each retained body once. Runtime iterations never multiply the
-- body derivation; syntax declarations are measured separately from rules. -/
partial def reachable (initial : Expr) (includeSyntax : Bool) : MetaM (Array Expr) := do
  let mut pending := [initial]
  let mut seen : Std.HashSet Name := {}
  let mut values := #[]
  let syntaxNames := ZkcTools.ConstructionBindings.Syntax.checkedSyntax.getState (← getEnv)
  repeat
    let expression :: rest := pending | return values
    pending := rest
    values := values.push expression
    for name in expression.getUsedConstants do
      if seen.contains name then continue
      seen := seen.insert name
      if retained name || (includeSyntax && (syntaxNames.contains name ||
          (name.toString.splitOn "connectionSyntax").length > 1)) then
        pending := ((← getConstInfo name).value! true) :: pending
  return values

syntax "service_certificate_metrics " ident num num num num : command
elab_rules : command
  | `(service_certificate_metrics $identifier:ident $queries:num $locals:num $deliveries:num $repeats:num) => liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo identifier
    let value := ((← getConstInfo name).value! true).consumeMData
    let certificate := if value.isAppOf ``Zkc.Construction.ConnectionAdmission.ofRootCertificate then
        value.getAppArgs[5]!.consumeMData.getAppArgs.back!.consumeMData
      else value
    unless certificate.isAppOf ``Zkc.Construction.ConnectionCertificate.Certificate.mk do
      throwError "metric expected the actual root's finite certificate: {name}"
    let derivation := certificate.getAppArgs.back!
    let bodies ← reachable derivation false
    let reachableSyntax ← reachable derivation true
    let alignmentNamespace := ``Zkc.Construction.ConnectionCertificate.Alignment
    let count := fun rule => bodies.foldl (fun total body =>
      total + occurrences body (· == alignmentNamespace ++ rule)) 0
    let actual := [count `publicQuery, count `localQuery, count `delivery,
      count `repeat + count `projectedRepeat]
    let expected := [queries.getNat, locals.getNat, deliveries.getNat, repeats.getNat]
    unless actual == expected do throwError "unexpected derivation expansion: {name}: {actual}, expected {expected}"
    let mut objects := 0
    for body in bodies do objects := objects + (← body.numObjs)
    let mut syntaxObjects := 0
    for declaration in reachableSyntax do syntaxObjects := syntaxObjects + (← declaration.numObjs)
    logInfo m!"SERVICE-CERTIFICATE-METRIC {Json.mkObj [
      ("name", toJson name.toString), ("root_expression_objects", toJson (← value.numObjs)),
      ("derivation_and_body_objects", toJson objects),
      ("reachable_declaration_objects", toJson syntaxObjects),
      ("retained_body_declarations", toJson (bodies.size - 1)),
      ("reachable_syntax_declarations", toJson (reachableSyntax.size - bodies.size)),
      ("alignment_constructors", toJson (bodies.foldl (fun n body => n + occurrences body alignmentNamespace.isPrefixOf) 0)),
      ("public_queries", toJson (count `publicQuery)),
      ("local_queries", toJson (count `localQuery)),
      ("deliveries", toJson (count `delivery)),
      ("repeat_bodies", toJson (count `repeat + count `projectedRepeat))]}"

service_certificate_metrics Tests.IndexServices.Scalar.validator_connected 1 0 0 0
service_certificate_metrics Tests.IndexServices.Scalar.producer_connected 0 0 1 0
service_certificate_metrics Tests.IndexServices.Block.validator_connected 1 0 0 0
service_certificate_metrics Tests.IndexServices.Block.producer_connected 0 0 1 0
service_certificate_metrics Tests.IndexServices.Local.validator_connected 1 1 0 0
service_certificate_metrics Tests.IndexServices.Local.producer_connected 0 2 1 0
service_certificate_metrics Tests.IndexServices.Repeated.validator_connected 1 0 0 1
service_certificate_metrics Tests.IndexServices.Repeated.producer_connected 0 0 1 1
service_certificate_metrics Tests.IndexServiceCertificateControls.shifted_scalar_connected 1 0 0 0
service_certificate_metrics Tests.IndexServiceCertificateControls.extended_repeat_connected 1 0 0 1
service_certificate_metrics Tests.ConnectionProfileCertificate.producerAccepted 0 1 1 0
service_certificate_metrics Tests.ConnectionProfileCertificate.validatorAccepted 1 0 0 0

#print axioms Zkc.Construction.ConnectionServiceRequests.Challenge.simulation
#print axioms Zkc.Construction.ConnectionServiceRequests.Public.fold
#print axioms Zkc.Construction.ConnectionServiceRequests.Local.fold
#print axioms Zkc.Construction.ConnectionServiceRequests.Delivery.receive
#print axioms Zkc.Construction.ConnectionCertificate.Certificate.simulation
#print axioms Zkc.Construction.ConnectionCertificate.Certificate.selectedRouteCoverage
#print axioms Zkc.Construction.ConnectionRoot.RootCertificate.simulation
#print axioms Zkc.Construction.ConnectionRoot.RootCertificate.routeCoverage
#print axioms Zkc.Construction.ConnectionAdmission.ofRootCertificate
#print axioms Tests.ConnectionProfileCertificate.producerAccepted
#print axioms Tests.ConnectionProfileCertificate.validatorAccepted
end Tests.IndexServiceCertificateMetrics
