import Zkc.Claims.Expressions
import Zkc.Claims.Receipt
import Zkc.Claims.Capability
import Zkc.Claims.Methods

/-! Kernel controls for typed extension, immutable request meanings and the
three independent proof-route records. No probability package is imported. -/

set_option autoImplicit false
namespace Tests.Claims
open Zkc.Claims Zkc.Source

private def identity : SubjectRef :=
  ⟨"admitted-unit", "example::Entry", .compiledIdeal, [⟨"validator", "artifact"⟩]⟩

private def request : Wire.Request where
  subject := identity
  property := ⟨"user.view_equal", 7⟩
  model := ⟨⟨"user.observer", 3⟩, []⟩
  target := .retained "example::Protocol" 0 "claim"
  accept := ⟨true, 0, 1, []⟩
  quantity := .scalar (.natural 0)

private abbrev interface : PIR.Signature := ⟨Empty, fun operation => nomatch operation⟩
private abbrev dialect : Dialect where
  Ty := Unit
  Op := Empty
  arguments operation := nomatch operation
  results operation := nomatch operation
  regions operation := nomatch operation

private def semantics : RegionMeaning dialect interface where
  Value _ := Nat
  operation operation := nomatch operation

private def operations : PIR.OperationInterpretation interface interface := fun operation => nomatch operation
private def region : Region dialect [] [] := .ret .nil
private def environment : Environment semantics.Value [] := fun ref => nomatch ref

private def viewEqual : Prop :=
  (region.denote semantics environment).interpret operations = .done .nil

private def property : PropertyExport SubjectRef where
  Arguments _ := Unit
  elaborate wire _ :=
    if wire.model.identifier = ⟨"user.observer", 3⟩ then .ok ()
    else .error (.unknownIdentifier wire.model.identifier)
  meaning _ _ := .ok viewEqual
  requiredLinks _ _ := [⟨"implementation", "fixed request", False, .infrastructure⟩]

private def registry : Registry (PropertyExport SubjectRef) :=
  ⟨[⟨request.property, "user.view-equal/7", some property⟩]⟩

private def resolved : Resolved registry id identity request where
  subjectMatched := rfl
  entry := ⟨request.property, "user.view-equal/7", some property⟩
  registered := rfl
  property := property
  defined := rfl
  arguments := ()
  elaborated := rfl

private def meaning : Evaluated resolved := ⟨viewEqual, rfl⟩
private def provenance : Provenance := ⟨.theorem, "Tests.Claims.viewEqual", ⟨"user.prove_view", 11⟩, [], []⟩

private def direct : Receipt meaning := Receipt.ofTheorem rfl provenance
private def endpoint : Receipt meaning := Receipt.ofEndpoint rfl provenance
private def derived : Receipt meaning := Receipt.ofDerivation
  (Region.Derivation.ret (meaning := semantics) (operations := operations) .nil environment)
  (fun equation => equation) provenance

example : direct.proof = derived.proof := rfl
example : endpoint.proof = direct.proof := rfl
example : direct.provenance.root = .theorem := rfl
example : derived.provenance.root = .derivation := rfl
example : endpoint.provenance.root = .endpoint := rfl

private def method : MethodExport meaning where
  discharge application :=
    if application.arguments.isEmpty then .ok (.proved direct)
    else .ok (.refused "view theorem takes no method arguments")

private def methods : Registry (MethodExport meaning) :=
  ⟨[⟨⟨"user.prove_view", 11⟩, "user.prove-view/11", some method⟩,
    ⟨⟨"user.future_view", 0⟩, "user.future-view/0", none⟩]⟩

example : runMethod methods ⟨⟨"user.prove_view", 11⟩, []⟩ = .ok (.proved direct) := rfl
example : runMethod methods ⟨⟨"user.prove_view", 12⟩, []⟩ =
    .error (.unknownIdentifier ⟨"user.prove_view", 12⟩) := rfl
example : runMethod methods ⟨⟨"user.future_view", 0⟩, []⟩ =
    .ok (.refused "method definition unavailable: user.future_view") := rfl

/-- Attachments and methods cannot change the request's type or meaning. -/
private def attachment : Attachment := ⟨"module", "Claim", "old", "owner", 0, 0, 0, 1⟩
example : ({ attachment with label := "new" }).owner = attachment.owner := rfl
example : resolved.meaning = .ok viewEqual := rfl

example : registry.lookup ⟨"user.view_equal", 8⟩ = .error (.unknownIdentifier ⟨"user.view_equal", 8⟩) := rfl
example : registry.register ⟨request.property, "conflict", none⟩ = .error (.conflict request.property) := rfl

example : resolve registry id identity { request with subject := { identity with unitDigest := "stale" } } =
    .error .subjectMismatch := rfl
example : resolve registry id identity { request with subject := { identity with artifacts := [⟨"validator", "stale"⟩] } } =
    .error .subjectMismatch := rfl

private def unavailable : Registry (PropertyExport SubjectRef) :=
  ⟨[⟨request.property, "user.view-equal/7", none⟩]⟩
example : resolve unavailable id identity request = .ok (.error ⟨["user.view_equal@7"]⟩) := rfl

private def openReceipt : Receipt meaning :=
  Receipt.ofTheorem rfl provenance
example : openReceipt.status = .open := rfl

example : evaluate (fun name => if name = "rounds" then some 8 else none)
    (.binary .div (.reference "rounds") (.natural 2)) = .ok 4 := by decide +kernel
example : evaluate (fun _ => none) (.binary .div (.natural 1) (.natural 0)) =
    .error ⟨["nonzero denominator"]⟩ := rfl
example : evaluateNatural (fun _ => none) (.binary .div (.natural 1) (.natural 2)) =
    .error ⟨["natural expression"]⟩ := by decide +kernel
example : evaluate (fun _ => none) (.reference "missing") = .error ⟨["unbound parameter: missing"]⟩ := rfl

-- The kernel refuses an arbitrary proof, even when the audit label agrees.
#check_failure (show meaning.proposition from False.elim True.intro)
#check_failure (show Receipt meaning from Receipt.ofTheorem True.intro provenance)

end Tests.Claims
