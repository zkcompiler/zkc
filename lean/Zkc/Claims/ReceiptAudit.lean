module

public import Lean

@[expose] public section

/-! Final receipt policy, independent of proof method. The extractor constructs
kernel observations from stored declarations; the frontend supplies external
byte/source admissions. JSON and digest equality do not prove correspondence. -/
set_option autoImplicit false
namespace ReceiptAudit
open Lean

inductive Origin where
  | kernel | externalAdmission | resolution
  deriving DecidableEq, Repr
structure Check where
  origin : Origin
  passed : Bool
  reason : String
  deriving Repr
inductive Resolution where
  | available | refused | undefined (definitions : List String)
  deriving DecidableEq, Repr
def Resolution.missing : Resolution → Bool
  | .undefined _ => true
  | _ => false
structure Envelope where
  receiptPresent : Bool
  resolution : Resolution
  checks : List Check
  deriving Repr
inductive Status where
  | certified | open | incomplete
  deriving DecidableEq, Repr

/-- Attribution is deliberately absent from the certification conditions. -/
def classify (audit : Envelope) : Status :=
  if audit.resolution.missing && !audit.receiptPresent then .incomplete
  else if audit.receiptPresent && audit.resolution == .available && audit.checks.all (·.passed)
    then .certified else .open

/-- Exact positive characterization. External admissions remain admissions,
not kernel theorems about bytes, hashes, source semantics or native execution. -/
theorem certified_iff (audit : Envelope) :
    classify audit = .certified ↔ audit.receiptPresent = true ∧
      audit.resolution = .available ∧ audit.checks.all (·.passed) = true := by
  cases hp : audit.receiptPresent <;> cases hr : audit.resolution <;>
    cases hc : audit.checks.all (·.passed) <;> simp [classify, Resolution.missing, hp, hr, hc]

/-- Every condition is necessary; neither attribution nor transport metadata
can bypass a failed kernel condition or external admission. -/
theorem certified_check (audit : Envelope) (check : Check)
    (positive : classify audit = .certified) (member : check ∈ audit.checks) :
    check.passed = true :=
  List.all_eq_true.mp ((certified_iff audit).mp positive).2.2 check member

def get (value : Json) (key : String) : Json := (value.getObjVal? key).toOption.getD .null
def str (value : Json) : String := value.getStr?.toOption.getD ""
def arr (value : Json) : Array Json := value.getArr?.toOption.getD #[]
def yes (value : Json) : Bool := value == .bool true
def has (value : Json) : Bool := value != .null && value != Json.mkObj []
def text (value : Json) : String :=
  if value == .null then "None" else value.getStr?.toOption.getD value.compress
def strings (value : Json) : Array String := (arr value).map str
def unique (values : Array Json) : Bool := values.toList.eraseDups.length == values.size
def object (fields : List (String × Json)) : Json := Json.mkObj fields

def securityTypes : List String := ["ZkcSecurity.Claims.AdmittedReceipt",
  "ZkcSecurity.Claims.CanonicalReceipt", "ZkcSecurity.Claims.AuthorExtensionReceipt"]
def receiptType := "Zkc.Claims.Receipt"
def requestType := "Zkc.Claims.Wire.Request"
def claimData (record : Json) : Json := get (get record "detail") "claim_data"
def receipt (record : Json) : Json := get (claimData record) "receipt"
def lookup (records : Array Json) (name : Json) : Json :=
  (records.find? (fun record => get record "name" == name)).getD .null

def resolution (mapping : Json) : Resolution := Id.run do
  let value := get mapping "resolution"
  let definitions := get value "definitions"
  if str (get value "status") == "incomplete" &&
      (get value "kind" == .null || str (get value "kind") == "registered-undefined") &&
      !(arr definitions).isEmpty && (arr definitions).all (fun item =>
        item.getStr?.isOk && !(str item).trimAscii.toString.isEmpty) then
    return .undefined (strings definitions).toList
  return if get value "status" == .null then .available else .refused

structure Audit where
  envelope : Envelope
  assumptions : Array Json := #[]
  discharged : Array Json := #[]
def reasons (audit : Envelope) : Array String :=
  ((audit.checks.filter (! ·.passed)).map (·.reason)).eraseDups.toArray
def statusName : Status → String
  | .certified => "certified"
  | .open => "open"
  | .incomplete => "incomplete"
def encode (audit : Audit) : Json := object [
  ("status", .str (statusName (classify audit.envelope))),
  ("outcome", .str (if classify audit.envelope == .certified then "established" else "unresolved")),
  ("reasons", toJson (reasons audit.envelope)),
  ("assumptions", .arr audit.assumptions), ("discharged", .arr audit.discharged),
  ("checks", .arr (audit.envelope.checks.toArray.map fun check => object [
    ("origin", .str (match check.origin with
      | .kernel => "kernel-extraction" | .externalAdmission => "external-admission" | .resolution => "resolution")),
    ("passed", .bool check.passed), ("reason", .str check.reason)]))]

/-- Production records are reconstructed from the kernel environment before
this decoder runs. No caller's final `verified` or status bit is consulted. -/
def auditReceipt (headers records : Array Json) (record requestRecord request : Json) : Audit := Id.run do
  let mut checks : Array Check := #[]
  let mut assumptions := #[]
  let mut discharged := #[]
  let add := fun passed reason => Check.mk .kernel passed reason
  checks := checks.push (add (!headers.isEmpty && headers.all (fun header =>
    str (get header "axiom_provenance") == "resolved-constant-info/0" &&
    str (get header "reference_provenance") == "checked-stored-module/0"))
    "declaration records lack checked stored-provider/actual-axiom provenance")
  let detail := get record "detail"
  let data := claimData record
  let r := receipt record
  let name := text (get record "name")
  checks := checks.push (add ((str (get detail "type_head") == receiptType ||
    securityTypes.contains (str (get detail "type_head"))) && has r)
    s!"proof type mismatch: {name} is not an extracted typed Receipt")
  if has (get data "extraction_error") then
    checks := checks.push (add false s!"receipt extraction failed: {text (get data "extraction_error")}")
  checks := checks.push (add (str (get (get requestRecord "detail") "type_head") == requestType &&
    get (claimData requestRecord) "wire_request" == request)
    "wrong request: emitted Wire.Request differs from the bound source request")
  checks := checks.push (add (get r "wire_request" == request)
    "wrong request: Receipt indices do not name the actual bound request declaration")
  checks := checks.push (add (yes (get r "indices_checked") && yes (get r "proof_type_matches"))
    "proof type mismatch: Resolved/Evaluated/Receipt indices were not checked")
  let property := get request "property"
  checks := checks.push (add (get r "registered_property" == object [
    ("name", get property "name"), ("version", get property "version")])
    "wrong registered property: actual Resolved export differs from the request")
  let authority := get r "authority"
  let recognized := str (get authority "kind") == "canonical" && yes (get authority "checked")
  let admission := get r "admission"
  let security := yes (get admission "security_subject")
  checks := checks.push (add (!(str (get authority "kind") == "reserved" ||
    (security && !yes (get authority "checked"))))
    "unrecognized property/model registry or reserved author extension")
  let quantity := str (get (get request "quantity") "kind")
  let capabilities := strings (get r "exported_capabilities")
  checks := checks.push (add ((arr (get request "capabilities")).isEmpty || recognized)
    "requested capabilities have no recognized checked consumer")
  checks := checks.push (add (capabilities.isEmpty || (recognized && quantity == "charged"))
    "unrecognized or unsupported capability export")
  if recognized then
    checks := checks.push (add (str (get r "quantity_kind") == quantity)
      "wrong quantity: evaluated typed arguments differ from the wire quantity")
    checks := checks.push (add (quantity != "charged" || capabilities.contains "capabilities.charged_reduction@0")
      "missing charged reduction capability in the actual evaluated receipt")
    checks := checks.push (add (quantity != "scalar" || !capabilities.contains "capabilities.charged_reduction@0")
      "scalar request cannot export a charged reduction without a charged meaning")
    let coverage := get r "application_coverage"
    let mode := str (get coverage "mode")
    checks := checks.push (add (yes (get coverage "checked"))
      "application coverage is not checked against the actual designated request binder/model")
    checks := checks.push (add (["fixed-statement", "honest-inputs", "parameter", "fixed"].contains mode)
      "unrecognized application coverage mode")
    if mode == "parameter" || mode == "fixed" then
      checks := checks.push (add (["context_matches", "reference_matches", "model_value_matches"].all
        (fun key => yes (get coverage key))) "application coverage context/reference/value comparison failed")
    if mode == "parameter" then
      checks := checks.push (add (yes (get coverage "value_is_binder") && has (get coverage "designated_binder"))
        "parameter application does not equal the designated free request binder")
    if mode == "fixed" then
      checks := checks.push (add ((get coverage "fixed_value").getStr?.isOk && get coverage "designated_binder" == .null)
        "fixed application scope is not concrete or narrows a designated free request binder")
  for capability in arr (get request "capabilities") do
    let key := text (get capability "name") ++ "@" ++ text (get capability "version")
    checks := checks.push (add (capabilities.contains key) s!"missing requested capability: {key}")
  let subject := get r "subject"
  checks := checks.push (add (!recognized || has (get subject "artifacts_head"))
    "missing actual typed security subject artifact identity")
  let securitySubject := has subject || security || recognized || securityTypes.contains (str (get detail "type_head"))
  if securitySubject then
    checks := checks.push (add (security && yes (get admission "associated"))
      "missing typed security model admission association")
    checks := checks.push (add (yes (get admission "subject_checked"))
      "actual security Subject.check did not admit this request/target/acceptance")
    checks := checks.push (add (str (get admission "model_status") == "admitted")
      s!"actual security model resolution is {if get admission "model_status" == .null then "unchecked" else text (get admission "model_status")}")
    if securityTypes.contains (str (get detail "type_head")) then
      checks := checks.push (add (yes (get admission "certificate_checked"))
        "typed security admission certificate does not match the actual receipt indices")
  for (current, origin) in #[(record, "receipt"), (requestRecord, "request")] do
    if !has current then continue
    let policy := if origin == "receipt" then get r "telescope" else get (claimData current) "telescope"
    if origin == "receipt" then
      if !yes (get policy "accepted") then
        let rejected := (arr (get policy "binders")).filter (fun row => str (get row "classification") == "refused")
        if rejected.isEmpty then checks := checks.push (add false "missing Lean telescope authorization")
        for row in rejected do
          checks := checks.push (add false s!"{text (get row "reason")}: {text (get row "binder")} binder {text (get row "type")} of {text (get current "name")}")
      for row in arr (get policy "conditions") do
        let fields := row.getObj?.toOption.map (·.toArray.toList) |>.getD []
        assumptions := assumptions.push (object (fields ++ [("discharge", .str "assumed"),
          ("source", .str s!"authorized premise of {text (get current "name")}")]))
    else
      checks := checks.push (add (yes (get policy "accepted")) "request declaration lacks Lean telescope authorization")
    let forbidden := (strings (get current "axioms")).filter (fun axiomName =>
      !["propext", "Classical.choice", "Quot.sound"].contains axiomName)
    if !forbidden.isEmpty then
      checks := checks.push (add false s!"{origin} {text (get current "name")} depends on {String.intercalate ", " forbidden.toList}")
  for item in arr (get r "dependencies") do
    let current := lookup records (get item "name")
    if has current then
      let forbidden := (strings (get current "axioms")).filter (fun axiomName =>
        !["propext", "Classical.choice", "Quot.sound"].contains axiomName)
      if !forbidden.isEmpty then
        checks := checks.push (add false s!"dependency {text (get current "name")} depends on {String.intercalate ", " forbidden.toList}")
  let links := arr (get r "required_links")
  checks := checks.push (add (unique (links.map (get · "identifier"))) "ambiguous registered obligation identifiers")
  for link in links do
    checks := checks.push (add (yes (get link "proved")) s!"unproved registered obligation: {text (get link "identifier")}")
  let stageFacts := get r "stage_links"
  if securitySubject || has (get stageFacts "stage") then
    let stageRecognized := yes (get stageFacts "recognized_subject")
    checks := checks.push (add stageRecognized
      "unrecognized actual typed compiled subject: stage obligations were not reconstructed")
    checks := checks.push (add (!stageRecognized || get stageFacts "stage" == get (get request "subject") "stage")
      "wrong interpreted stage: typed subject differs from the request")
    let expected := arr (get stageFacts "obligations")
    checks := checks.push (add (!stageRecognized || (!expected.isEmpty && unique (expected.map (get · "identifier"))))
      "incomplete checked stage obligations: missing or ambiguous Lean authority policy")
    for link in expected do
      let identifier := get link "identifier"
      let same := expected.filter (fun item => get item "identifier" == identifier)
      let comparisons := arr (get link "matches")
      let matching := if comparisons.size == 1 then links.filter (fun item =>
        get item "index" == get comparisons[0]! "index" && get item "identifier" == identifier) else #[]
      let present := stageRecognized && same.size == 1 && matching.size == 1 && yes (get matching[0]! "proved")
      checks := checks.push (add present s!"missing required interpreted-stage link: {text identifier}")
      if present then
        let compared := yes (get comparisons[0]! "goal_defeq") && yes (get comparisons[0]! "subject_matches")
        checks := checks.push (add compared s!"wrong actual subject or goal for interpreted-stage link: {text identifier}")
        if compared then
          discharged := discharged.push (object [("id", identifier), ("category", .str "stage-link"),
            ("schema", get link "goal_head"), ("statement", get link "goal"),
            ("instantiated", get matching[0]! "goal"), ("discharge", .str "proved"),
            ("source", .str "kernel comparison with actual Subject.stageLinks"),
            ("goal_identity", get link "goal_identity"), ("context", get link "context")])
  assumptions := assumptions.push (object [("id", .str "source.correspondence"), ("category", .str "trusted-link"),
    ("schema", .null), ("statement", .str "Source-to-IR correspondence remains unproved"),
    ("instantiated", .null), ("discharge", .str "assumed"), ("source", .str "IR-relative milestone")])
  return ⟨⟨has r, .available, checks.toList⟩, assumptions, discharged⟩

/-- Entry/interface labels remain a frontend admission, with exact association
shape and identity checks here rather than a Python status predicate. -/
def sourceEntry (item : Json) : Json × Array String := Id.run do
  let protocol := get (get (get item "request") "subject") "entry"
  let entry := if get item "source_entry" == .null then protocol else get item "source_entry"
  if !protocol.getStr?.isOk || (str protocol).isEmpty || !entry.getStr?.isOk || (str entry).isEmpty then
    return (.null, #["invalid source/request Entry"])
  let association := get item "entry_association"
  if association == .null then
    return (entry, if entry == protocol then #[] else #["source alias lacks a checked interface Entry association"])
  let keys := association.getObj?.toOption.map (fun obj => obj.toArray.map Prod.fst) |>.getD #[]
  let digest := str (get association "interface_digest")
  let validDigest := digest.startsWith "sha256:" && digest.length == 71 &&
    (digest.drop 7).toString.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))
  let valid := keys.size == 4 && ["source_entry", "protocol", "interface_digest", "attribution"].all keys.contains &&
    get association "source_entry" == entry && get association "protocol" == protocol &&
    str (get association "attribution") == "trusted-frontend-checked-interface" && validDigest
  return (entry, if valid then #[] else #["source/request Entry differs from its checked interface association"])

def scopeReasons (source scope proofEntry : Json) : Array String := Id.run do
  if !scope.getObj?.isOk then return #["missing source claim Entry scope"]
  let entries := arr (get scope "entries")
  if entries.isEmpty || !unique entries || entries.any (fun item => !item.getStr?.isOk || (str item).isEmpty) then
    return #["invalid source claim Entry scope"]
  let mut reasons := #[]
  let selection := str (get scope "selection")
  if !["proof-entry", "explicit"].contains selection then
    reasons := reasons.push "unknown source claim Entry selection"
  let boundEntries := if get source "entries" == .null then #[get source "entry"] else arr (get source "entries")
  if entries != boundEntries then reasons := reasons.push "source claim Entry scope differs from bound Entries"
  if selection == "proof-entry" && entries != #[proofEntry] then
    reasons := reasons.push "default source claim scope differs from the manifest proof Entry"
  let resolved := (arr (get source "claims")).map sourceEntry
  for (_, failures) in resolved do reasons := reasons ++ failures
  if resolved.any (fun pair => !entries.contains pair.1) then
    reasons := reasons.push "source request Entry is outside the selected scope"
  if selection == "explicit" then
    for entry in entries do
      if !resolved.any (fun pair => pair.1 == entry) then
        reasons := reasons.push s!"requested Entry has no matching source claims: {text entry}"
  return reasons

/-- Filesystem hashing/preflight failures retain their exact diagnostics. The
external envelope contains byte/source observations, never proof flags. -/
def auditRequest (input item : Json) : Audit := Id.run do
  let records := arr (get input "records")
  let mappings := arr (get input "mappings")
  let request := get item "request"
  let node := get (get item "attachment") "node"
  let candidates := mappings.filter (fun mapping => get mapping "node" == node)
  let mapping := if candidates.size == 1 then candidates[0]! else .null
  let record := lookup records (get mapping "receipt_declaration")
  let requestRecord := lookup records (get mapping "request_declaration")
  let r := receipt record
  let mut audit := if has record then auditReceipt (arr (get input "headers")) records record requestRecord request
    else ⟨⟨false, .available, []⟩, #[], #[]⟩
  let mut checks : Array Check := #[]
  let add := fun passed reason => Check.mk .externalAdmission passed reason
  for reason in strings (get input "reasons") do checks := checks.push (add false reason)
  for reason in strings (get input "environment_reasons") do checks := checks.push (add false reason)
  let digest := get item "admitted_request_digest"
  checks := checks.push (add (get item "request_digest" == digest) "wrong request digest: bound source request bytes changed")
  checks := checks.push (add (has node && candidates.size == 1) "missing or ambiguous request/receipt source-node association")
  if has mapping then
    checks := checks.push (add (get mapping "request_digest" == digest) "wrong request digest: receipt association is stale")
  if has (get input "reused_reason") then checks := checks.push (add false (str (get input "reused_reason")))
  let subject := get request "subject"
  let evidence := get input "evidence"
  let artifacts := get evidence "artifacts"
  let unitKey := if str (get subject "stage") == "interactive" then "interactive_export" else "original_export"
  checks := checks.push (add (get subject "unit" == get artifacts unitKey)
    "mismatched artifact: request unit is not the admitted original export")
  let roles := arr (get (get r "stage_links") "artifact_roles")
  let supplied := arr (get subject "artifacts")
  let expectedRoles := (roles.map (get · "role")).toList.eraseDups
  checks := checks.push (add (!roles.isEmpty && supplied.size == expectedRoles.length &&
    (supplied.map (get · "role")).toList.eraseDups.all expectedRoles.contains &&
    expectedRoles.all (fun role => supplied.any (fun item => get item "role" == role)))
    "mismatched artifact: request differs from the checked Lean authority artifact roles")
  for artifact in supplied do
    let selected := roles.filter (fun row => get row "role" == get artifact "role")
    checks := checks.push (add (selected.size == 1 && get artifact "digest" == get artifacts (str (get selected[0]! "pipeline_artifact")))
      s!"mismatched artifact: request {text (get artifact "role")} differs from pipeline bytes")
  let (entry, entryFailures) := sourceEntry item
  for reason in entryFailures do checks := checks.push (add false reason)
  let bound := get evidence "source_claims"
  let entries := if get bound "entries" == .null then #[get bound "entry"] else arr (get bound "entries")
  checks := checks.push (add (entries.contains entry)
    "wrong subject: source request Entry differs from the admitted exports")
  checks := checks.push (add (str (get (get input "validation") "outcome") == "accepted")
    "pipeline validation has not accepted this subject")
  if has record then
    for key in ["request_declaration", "receipt_declaration"] do
      let current := lookup records (get mapping key)
      if !has current then
        checks := checks.push (add false s!"missing emitted {key}: {text (get mapping key)}")
      else
        checks := checks.push (add ((strings (get input "attached_modules")).contains (str (get current "module")))
          s!"mismatched artifact: {key} {text (get mapping key)} is outside this subject's generated modules")
    checks := checks.push (add ((arr (get evidence "checks")).any (fun check =>
      str (get check "name") == "claim-receipt" && str (get check "outcome") == "accepted" &&
      get check "module" == get record "module" && get check "request" == get mapping "request_declaration" &&
      get check "receipt" == get mapping "receipt_declaration"))
      "no accepted claim-receipt check built the actual request and receipt declarations")
    let typed := get r "subject"
    if has typed then
      for (key, role) in [("original_source", "source"), ("participant_source", "source"),
          ("participant_candidate", "constructed_candidate")] do
        checks := checks.push (add (get typed key == get artifacts role)
          s!"mismatched artifact: actual typed subject {key} differs from pipeline")
      if get typed "producer_source" != .null then
        for (key, role) in [("producer_source", "source"), ("producer_candidate", "constructed_candidate")] do
          checks := checks.push (add (get typed key == get artifacts role)
            s!"mismatched artifact: actual typed subject {key} differs from pipeline")
      checks := checks.push (add (get typed "original_entry" == get (get request "target") "protocol")
        "wrong target protocol: request differs from actual admitted snapshot")
      let artifactRecord := lookup records (get typed "artifacts_head")
      checks := checks.push (add (has artifactRecord &&
        (strings (get input "attached_modules")).contains (str (get artifactRecord "module")))
        "mismatched artifact: actual typed subject artifacts are outside the regenerated modules")
  else checks := checks.push (add false "no emitted typed receipt proves this request")
  if has r then
    for reason in strings (get item "dependency_reasons") do checks := checks.push (add false reason)
  checks := checks.push (add (get mapping "semantic_dependency_digest" == .null ||
    get mapping "semantic_dependency_digest" == get (get item "semantic_dependencies") "digest")
    "stale semantic dependency digest: referenced definition bodies or environment changed")
  let resolved := resolution mapping
  checks := checks.push ⟨.resolution, !(resolved.missing && has r),
    "inconsistent resolution: a typed receipt accompanies missing definitions"⟩
  checks := checks.push ⟨.resolution, !(resolved == .refused && has r),
    "inconsistent resolution: a typed receipt accompanies failed resolution"⟩
  audit := { audit with envelope := ⟨has r, resolved, checks.toList ++ audit.envelope.checks⟩ }
  return audit

/-- Consumer requirements are fixed independently of the provider's inventory.
They constrain this audit; they never establish a proposition on their own. -/
def consumerReasons (input : Json) : Array String := Id.run do
  let required := get input "consumer_requirements"
  if required == .null then return #[]
  let mut reasons := #[]
  let exactFields := fun (value : Json) (expected : List String) =>
    match value.getObj? with
    | .error _ => false
    | .ok fields =>
      let names := fields.toArray.map Prod.fst
      names.size == expected.length && names.all expected.contains
  if !exactFields required ["format", "context", "claims"] then
    reasons := reasons.push "consumer requirements have unknown or missing fields"
  if str (get required "format") != "zkc.consumer-requirements/0" then
    reasons := reasons.push "unsupported consumer requirements format"
  let context := get required "context"
  if !exactFields context ["subject", "manifest_sha256", "checker"] then
    reasons := reasons.push "consumer requirements context has unknown or missing fields"
  if !has context || context != get input "consumer_context" ||
      !has (get context "checker") || str (get context "manifest_sha256") == "" ||
      str (get context "subject") == "" then
    reasons := reasons.push "consumer requirements name another subject or environment"
  let expected := arr (get required "claims")
  if expected.isEmpty then
    reasons := reasons.push "consumer requirements must contain a nonempty expected request set"
  let nodes := expected.map (fun item => get item "node")
  if !unique nodes then reasons := reasons.push "duplicate consumer requirement occurrence"
  let supplied := arr (get (get input "source") "claims")
  for item in expected do
    if !exactFields item ["node", "request"] then
      reasons := reasons.push "consumer requirement has unknown or missing fields"
    let node := get item "node"
    let request := get item "request"
    if !has node || !has request then
      reasons := reasons.push "consumer requirement lacks an occurrence or a complete request"
    let candidates := supplied.filter (fun actual =>
      get (get actual "attachment") "node" == node)
    if candidates.size != 1 then
      reasons := reasons.push "consumer-required request occurrence is missing or ambiguous"
    else if get candidates[0]! "request" != request then
      reasons := reasons.push "consumer-required request differs from the supplied request"
  return reasons

/-- Scope errors apply to every row before classification. -/
def run (input : Json) : Except String Json := do
  unless str (get input "format") == "zkc.receipt-audit-input/0" do
    throw "unsupported receipt audit input"
  if str (get input "operation") == "entry" then
    let (entry, reasons) := sourceEntry (get input "item")
    return object [("format", .str "zkc.receipt-status/0"), ("entry", entry), ("reasons", toJson reasons)]
  if str (get input "operation") == "scope-reasons" then
    return object [("format", .str "zkc.receipt-status/0"), ("reasons", toJson
      (scopeReasons (get input "source") (get input "scope") (get input "proof_entry")))]
  if str (get input "operation") == "receipt" then
    return object [("format", .str "zkc.receipt-status/0"), ("audit", encode (auditReceipt
      (arr (get input "headers")) (arr (get input "records")) (get input "record")
      (get input "request_record") (get input "request")))]
  unless str (get input "operation") == "scope" do throw "unknown receipt audit operation"
  let source := get input "source"
  let items := arr (get source "claims")
  let nodes := items.map (fun item => get (get item "attachment") "node")
  let mut scopeReasons := strings (get input "reasons") ++ consumerReasons input
  if yes (get input "validate_scope") then
    scopeReasons := scopeReasons ++ ReceiptAudit.scopeReasons source (get input "scope") (get input "proof_entry")
  let available := (arr (get input "mappings")).size == items.size &&
    (arr (get input "mappings")).all (fun mapping =>
      has (lookup (arr (get input "records")) (get mapping "request_declaration")) &&
      (get mapping "receipt_declaration" == .null ||
        has (lookup (arr (get input "records")) (get mapping "receipt_declaration"))))
  if yes (get input "trial") then
    let entry := (arr (get source "entries"))[0]?.getD .null
    let selected := arr (get (get (get input "evidence") "source_claim_scope") "entries")
    let trials := arr (get (get input "evidence") "source_claim_trials")
    if selected.contains entry || (trials.filter (fun trial => get trial "entry" == entry)).size > 1 then
      scopeReasons := scopeReasons.push "duplicate or selected Entry in source claim trials"
  let unaudited := yes (get input "trial") && !available
  if unaudited then
    scopeReasons := scopeReasons.push "trial declaration records unavailable; trial is unaudited"
  if !unique nodes then scopeReasons := scopeReasons.push "duplicate bound source claim node"
  if (arr (get input "mappings")).any (fun mapping => !nodes.contains (get mapping "node")) then
    scopeReasons := scopeReasons.push "receipt association names a source node absent from this scope"
  let fields := input.getObj?.toOption.map (·.toArray.toList) |>.getD []
  let input := object ((fields.filter (fun pair => pair.1 != "reasons")) ++ [("reasons", toJson scopeReasons)])
  let rows := items.map fun item => Id.run do
    let audit := auditRequest input item
    let audit := if unaudited then { audit with envelope := { audit.envelope with resolution := .refused } } else audit
    let node := get (get item "attachment") "node"
    let candidates := (arr (get input "mappings")).filter (fun mapping => get mapping "node" == node)
    let mapping := if candidates.size == 1 then candidates[0]! else .null
    let record := lookup (arr (get input "records")) (get mapping "receipt_declaration")
    let requestRecord := lookup (arr (get input "records")) (get mapping "request_declaration")
    let r := receipt record
    let kind := if get (get r "authority") "kind" != .null then get (get r "authority") "kind"
      else if get (claimData requestRecord) "claim_kind" != .null then get (claimData requestRecord) "claim_kind" else .str "unresolved"
    return object [("node", node), ("request_digest", get item "admitted_request_digest"),
      ("claim_kind", kind), ("semantic_dependencies", get item "semantic_dependencies"),
      ("audit", encode audit)]
  let security := rows.filter (fun row => !["author", "generic"].contains (str (get row "claim_kind")))
  let requiredNodes := (arr (get (get input "consumer_requirements") "claims")).map (get · "node")
  let requiredChecked := requiredNodes.all (fun node => rows.any (fun row =>
    get row "node" == node && str (get (get row "audit") "status") == "certified"))
  if !requiredChecked then
    scopeReasons := scopeReasons.push "consumer-required request has no certified receipt"
  let established := !security.isEmpty && scopeReasons.isEmpty && requiredChecked && security.all (fun row =>
    str (get (get row "audit") "status") == "certified")
  let state := if security.isEmpty && get input "consumer_requirements" == .null &&
      str (get source "format") == "zkc.bound-source-claims/0" then "no-claim"
    else if established then "certified" else if !security.isEmpty && security.all (fun row =>
      str (get (get row "audit") "status") == "incomplete") then "incomplete" else "open"
  return object [("format", .str "zkc.receipt-status/0"), ("claims", .arr rows),
    ("status", .str state), ("outcome", .str (if established then "established" else "unresolved")),
    ("consumer_requirements", get input "consumer_requirements"),
    ("reasons", toJson scopeReasons), ("audit_status", .str (if unaudited then "unaudited" else "checked"))]
end ReceiptAudit
