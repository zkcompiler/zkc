module

public import Zkc.Source.Structured.ProtocolAdmission

@[expose] public section

namespace Zkc.Source.Structured

def Relation.valid (relation : Relation) : Bool :=
  validString relation.name && validString relation.kind && validString relation.key &&
  validString relation.revision && validTypes relation.inputs &&
  !relation.inputs.any Ty.isService && relation.outputs == [.boolean] &&
  relation.purposes.length == relation.inputs.length &&
  relation.purposes.all (fun purpose => ["parameter", "statement", "witness"].contains purpose)

def resolveProtocolOp (snapshot : Snapshot) (domains : List DomainSpec)
    (function : Function) (headers : List ProtocolSignature)
    (interface : ProtocolInterface) (inputScopes : List (List Nat))
    (context : List Ty) (origins : List (Option Nat)) (facts : Facts) (identities : List Nat)
    (descriptor : Descriptor) (operands : List Nat) (results : List Ty) (site : String) :
    LowerM ProtocolOp := do
  if !validRefs operands || !validTypes results || results.any Ty.isService then
    throw "structured-protocol-signature"
  if !site.isEmpty && !validProtocolIdentifier site then throw "structured-site"
  let arguments ← typesAt context operands
  let role := resolveRole interface.roles
  match descriptor with
  | .protocolApply name roles =>
    recordSite site true
    let (signature, indices) ← resolveProtocolApplication snapshot headers interface name roles
    if arguments != signature.inputs || results != signature.outputs then
      throw "structured-protocol-apply-signature"
    for ((type, scope), operand) in (signature.inputs.zip signature.inputScopes).zip operands do
      if type.isService then
        let some (some input) := origins[operand]? | throw "structured-service-root"
        if function.inputs[input]? != some type then throw "structured-service-contract"
        let mapped := scope.map (fun role => indices[role]?.getD 0)
        if mapped.length != 1 || inputScopes[input]? != some mapped then
          throw "structured-service-owner"
    return .protocolApply signature indices site
  | .localCall name owner =>
    recordSite site true
    let owner ← role owner
    let callee ← lookupDefinition snapshot name
    if !callee.acceptsEdge .localCall then throw "structured-call-kind"
    return .localCall ⟨name, .local, callee.inputs, callee.outputs⟩ rfl owner site
  | .guard owner =>
    recordSite site true
    return .guard (← role owner) site
  | .exchange sender receiver =>
    recordSite site true
    let sender ← role sender
    let receiver ← role receiver
    if sender == receiver then throw "structured-exchange-endpoints"
    let [type] := arguments | throw "structured-exchange-signature"
    if type.isService then throw "structured-service-use"
    return .exchange type sender receiver site
  | .restrict selected =>
    if !site.isEmpty then throw "structured-pure-site"
    recordSite site false
    let [type] := arguments | throw "structured-restrict-signature"
    if type.isService then throw "structured-service-use"
    return .restrict type (← resolveScope interface.roles selected)
  | .draw owner field =>
    recordSite site true
    if field != scalarDomain then throw "structured-field-domain"
    let owner ← role owner
    let [operand] := operands | throw "structured-draw-signature"
    let some (some input) := origins[operand]? | throw "structured-service-root"
    if inputScopes[input]? != some [owner] then throw "structured-service-owner"
    if arguments != [.service scalarServiceContract] then throw "structured-service-contract"
    return .draw owner field site
  | .statement relation selectors acceptance =>
    if !site.isEmpty then throw "structured-pure-site"
    recordSite site false
    let some declaration := snapshot.relations.find? (·.name == relation) |
      throw "structured-unknown-relation"
    if arguments != declaration.inputs || !results.isEmpty || arguments.any Ty.isService then
      throw "structured-statement-signature"
    if selectors.length != operands.length || function.outputs[acceptance]? != some .boolean then
      throw "structured-statement-acceptance"
    for (operand, selector) in operands.zip selectors do
      let selected ← role selector
      let some (some input) := origins[operand]? | throw "structured-statement-input"
      if !(inputScopes[input]?.getD []).contains selected then throw "structured-statement-selector"
    return .statement relation arguments selectors acceptance
  | _ =>
    let op ← resolveOp snapshot domains .protocol context facts identities descriptor operands results site
    if allowed : op.isCalculation = true then return .calculate op allowed
    else throw "structured-protocol-operation"

/-- Protocol roots have no nested regions in this profile. Their SSA and typed
formation are still the shared RawRegion/Region formation, not a second IR. -/
def lowerProtocolInstructions (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function) (headers : List ProtocolSignature)
    (interface : ProtocolInterface)
    (scopes : List (List Nat)) (terminal : Terminator) :
    List Ty → List (Option Nat) → Facts → List Nat → List Instruction →
      LowerM (RawRegion Ty ProtocolOp)
  | _, _, _, _, [] => do
    let .ret refs := terminal | throw "structured-protocol-terminator"
    if !validRefs refs then throw "structured-reference-limit"
    return .ret refs
  | context, origins, facts, identities, .instruction descriptor operands results regions site :: rest => do
    if !regions.isEmpty then throw "structured-protocol-region"
    let op ← resolveProtocolOp snapshot domains function headers interface scopes context origins facts identities
      descriptor operands results site
    let operandOrigins := operands.map fun index => identities[index]?
    let resultOrigins := (resultIdentities summaries descriptor operandOrigins results.length).zipIdx.map
      fun (source, result) => match source with
        | some original => original + results.length
        | none => result
    let next ← lowerProtocolInstructions snapshot domains summaries function headers interface scopes terminal
      (results ++ context) (List.replicate results.length none ++ origins)
      (facts.shift results.length) (resultOrigins ++ identities.map (· + results.length)) rest
    return .letOp (.mark site) [] [] .nil (.letOp op operands results .nil next)

/-- The sole body lowering is separate from the full header phase for reusable proofs. -/
def lowerProtocol (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (headers : List ProtocolSignature)
    (function : Function) (signature : ProtocolSignature) : Except String (RawRegion Ty ProtocolOp) := do
  let some interface := function.interface | throw "structured-protocol-interface"
  let .block instructions terminal := function.body
  (lowerProtocolInstructions snapshot domains summaries function headers interface
    signature.inputScopes terminal function.inputs ((List.range function.inputs.length).map some) []
    (List.range function.inputs.length) instructions).run' {}

def formProtocol (signature : ProtocolSignature) (raw : RawRegion Ty ProtocolOp) :
    Except String CheckedProtocol :=
  match formed : raw.elaborate (dialect := protocolDialect) signature.inputs signature.outputs with
  | .error _ => .error "structured-formation"
  | .ok body => .ok ⟨signature, raw, body, formed⟩

/-- Check a complete protocol using the supplied full header table. The empty
default is an application-free convenience: every retained application then
fails header resolution. Whole-unit admission always supplies all headers. -/
def checkProtocol (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function)
    (headers : List ProtocolSignature := []) : Except String CheckedProtocol := do
  let signature ← resolveProtocolSignature function
  let raw ← lowerProtocol snapshot domains summaries headers function signature
  formProtocol signature raw

/-- Successful formation preserves both the complete signature and the exact tree. -/
theorem formProtocol_exact {signature : ProtocolSignature} {raw : RawRegion Ty ProtocolOp}
    {checked : CheckedProtocol} (accepted : formProtocol signature raw = .ok checked) :
    checked.signature = signature ∧ checked.raw = raw := by
  unfold formProtocol at accepted
  split at accepted
  · contradiction
  · cases Except.ok.inj accepted
    exact ⟨rfl, rfl⟩

/-- Generic source association includes resolved scopes and the actual lowering equation. -/
theorem checkProtocol_exact {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {function : Function} {headers : List ProtocolSignature}
    {checked : CheckedProtocol}
    (accepted : checkProtocol snapshot domains summaries function headers = .ok checked) :
    resolveProtocolSignature function = .ok checked.signature ∧
    lowerProtocol snapshot domains summaries headers function checked.signature = .ok checked.raw := by
  unfold checkProtocol at accepted
  cases signatureEq : resolveProtocolSignature function with
  | error error => simp [signatureEq, Except.bind, bind] at accepted
  | ok signature =>
    cases rawEq : lowerProtocol snapshot domains summaries headers function signature with
    | error error => simp [signatureEq, rawEq, Except.bind, bind] at accepted
    | ok raw =>
      have exactForm : formProtocol signature raw = .ok checked := by
        simpa only [signatureEq, rawEq, Except.bind, bind] using accepted
      rcases formProtocol_exact exactForm with ⟨sameSignature, sameRaw⟩
      constructor
      · simp only [sameSignature]
      · simpa only [sameSignature, sameRaw] using rawEq

private theorem lowerM_bind_ok {α β : Type} {action : LowerM α} {next : α → LowerM β}
    {initial final : LowerState} {value : β}
    (accepted : (action >>= next) initial = .ok (value, final)) :
    ∃ result middle, action initial = .ok (result, middle) ∧
      (next result) middle = .ok (value, final) := by
  change (action initial >>= fun result => next result.1 result.2) = .ok (value, final) at accepted
  cases h : action initial with
  | error error => simp [h, Except.bind, bind] at accepted
  | ok result =>
    refine ⟨result.1, result.2, rfl, ?_⟩
    simpa only [StateT.run, h, bind, Except.bind] using accepted

/-- Every retained raw application comes from an actual original instruction.
The witness records the exact resolver state and lexical origin environment:
every preceding result contributes `none`; initial input origins are retained. -/
theorem lowerProtocolInstructions_application_origin {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {function : Function} {headers : List ProtocolSignature}
    {interface : ProtocolInterface} {scopes : List (List Nat)} {terminal : Terminator}
    {context : List Ty} {origins : List (Option Nat)} {facts : Facts} {identities : List Nat}
    {instructions : List Instruction} {initial final : LowerState} {raw : RawRegion Ty ProtocolOp}
    (accepted : (lowerProtocolInstructions snapshot domains summaries function headers interface scopes
      terminal context origins facts identities instructions) initial = .ok (raw, final))
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ raw.operations) :
    ∃ offset context' facts' identities' before after descriptor operands results regions sourceSite,
      .instruction descriptor operands results regions sourceSite ∈ instructions ∧
      (resolveProtocolOp snapshot domains function headers interface scopes context'
        (List.replicate offset none ++ origins) facts' identities'
        descriptor operands results sourceSite) before =
          .ok (.protocolApply signature indices site, after) := by
  induction instructions generalizing context origins facts identities initial final raw with
  | nil =>
    simp only [lowerProtocolInstructions] at accepted
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply] at accepted
    repeat' first | contradiction | split at accepted
    all_goals cases accepted; simp [RawRegion.operations] at occurs
  | cons instruction rest ih =>
    cases instruction with
    | instruction descriptor operands results regions sourceSite =>
      simp only [lowerProtocolInstructions] at accepted
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply] at accepted
      repeat' first | contradiction | split at accepted
      obtain ⟨op, middle, resolved, remaining⟩ := lowerM_bind_ok accepted
      obtain ⟨next, last, lowered, output⟩ := lowerM_bind_ok remaining
      have same : (.letOp (.mark sourceSite) [] [] .nil
          (.letOp op operands results .nil next) : RawRegion Ty ProtocolOp) = raw :=
        congrArg Prod.fst (Except.ok.inj output)
      subst raw
      simp only [RawRegion.operations, RawRegions.operations, List.nil_append,
        List.mem_cons] at occurs
      rcases occurs with impossible | sameOp | occurs
      · cases impossible
      · subst op
        exact ⟨0, context, facts, identities, initial, middle, descriptor, operands, results,
          regions, sourceSite, List.mem_cons_self, resolved⟩
      · obtain ⟨offset, ctx, fs, ids, before, after, desc, args, outs, bodies, s, member, equation⟩ :=
          ih lowered occurs
        refine ⟨offset + results.length, ctx, fs, ids, before, after, desc, args, outs,
          bodies, s, List.mem_cons_of_mem _ member, ?_⟩
        simpa only [← List.replicate_append_replicate, List.append_assoc] using equation

private theorem lowerM_lift_ok {α : Type} {action : Except String α}
    {initial final : LowerState} {value : α}
    (accepted : StateT.lift action initial = .ok (value, final)) :
    action = .ok value := by
  cases h : action with
  | error error => simp [StateT.lift, h, bind, Except.bind] at accepted
  | ok result =>
    rw [h] at accepted
    have same : result = value := congrArg Prod.fst (Except.ok.inj accepted)
    cases same
    rfl

private theorem lowerM_forIn_ok {α : Type} {xs : List α} {P : α → Prop}
    {f : α → PUnit → LowerM (ForInStep PUnit)}
    (checked : ∀ x before after step, f x () before = .ok (step, after) →
      step = .yield () ∧ P x)
    {initial final : LowerState}
    (accepted : (forIn xs () f : LowerM PUnit) initial = .ok ((), final)) :
    ∀ x ∈ xs, P x := by
  induction xs generalizing initial final with
  | nil => simp
  | cons head tail ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨step, middle, first, remaining⟩ := lowerM_bind_ok accepted
    obtain ⟨rfl, property⟩ := checked head initial middle step first
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · exact property
    · exact ih remaining x member

private theorem recordSite_nonempty {site : String} {initial final : LowerState}
    (accepted : recordSite site true initial = .ok ((), final)) : site.isEmpty = false := by
  cases empty : site.isEmpty with
  | false => rfl
  | true =>
    simp [recordSite, validString, empty, bind, StateT.bind, StateT.lift,
      Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- Invert an actual successful operation resolution. Retain its source
descriptor/site, ordered value ABI, finite role resolver and every lexical
service-input check, including unused service arguments. -/
theorem resolveProtocolOp_application {snapshot : Snapshot} {domains : List DomainSpec}
    {function : Function} {headers : List ProtocolSignature} {interface : ProtocolInterface}
    {scopes : List (List Nat)} {context : List Ty} {origins : List (Option Nat)}
    {facts : Facts} {identities : List Nat} {descriptor : Descriptor}
    {operands : List Nat} {results : List Ty} {sourceSite : String}
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    {initial final : LowerState}
    (accepted : (resolveProtocolOp snapshot domains function headers interface scopes context origins
      facts identities descriptor operands results sourceSite).run initial =
        .ok (.protocolApply signature indices site, final)) :
    ∃ name roles, descriptor = .protocolApply name roles ∧ sourceSite = site ∧
      validProtocolIdentifier site = true ∧
      resolveProtocolApplication snapshot headers interface name roles = .ok (signature, indices) ∧
      typesAt context operands = .ok signature.inputs ∧ results = signature.outputs ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (signature.inputs.zip signature.inputScopes).zip operands → type.isService = true →
        ∃ input, origins[operand]? = some (some input) ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => indices[role]?.getD 0)).length = 1 ∧
          scopes[input]? = some (scope.map (fun role => indices[role]?.getD 0))) := by
  by_cases badSignature : (!validRefs operands || !validTypes results || results.any Ty.isService) = true
  · simp [resolveProtocolOp, badSignature, StateT.run, bind, StateT.bind, pure,
      throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind] at accepted
  by_cases badSite : (!sourceSite.isEmpty && !validProtocolIdentifier sourceSite) = true
  · simp [resolveProtocolOp, badSignature, badSite, StateT.run, bind, StateT.bind, pure,
      throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind] at accepted
  simp only [resolveProtocolOp, badSignature, badSite, Bool.false_eq_true, ↓reduceIte] at accepted
  dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
    MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply,
    liftM, monadLift, MonadLift.monadLift] at accepted
  repeat' first
    | contradiction
    | split at accepted
    | (dsimp only [StateT.bind, StateT.pure, StateT.lift, Except.bind,
        Except.pure, bind, pure, liftM, monadLift, MonadLift.monadLift] at accepted
       first | contradiction | split at accepted)
  all_goals
    have same := congrArg Prod.fst (Except.ok.inj accepted)
    cases same
  rename_i _ arguments typesEq _ name roles _ siteState siteEq _ callee resolved abi _ loopState loopEq
  refine ⟨_, _, rfl, rfl, ?_, lowerM_lift_ok (by assumption), ?_, ?_, ?_⟩
  · have nonempty : sourceSite.isEmpty = false := recordSite_nonempty (by assumption)
    simpa [nonempty] using badSite
  · have types := lowerM_lift_ok (action := typesAt context operands) (by assumption)
    simp_all
  · simp_all
  · have each := lowerM_forIn_ok (P := fun entry : (Ty × List Nat) × Nat =>
        entry.1.1.isService = true → ∃ input,
          origins[entry.2]? = some (some input) ∧ function.inputs[input]? = some entry.1.1 ∧
          (entry.1.2.map (fun role => callee.1.2[role]?.getD 0)).length = 1 ∧
          scopes[input]? = some (entry.1.2.map (fun role => callee.1.2[role]?.getD 0)))
        (f := _) ?_ loopEq
    · intro type scope operand member service
      exact each ((type, scope), operand) member service
    · intro entry before after step checked
      by_cases service : entry.1.1.isService = true
      · simp only [service, ↓reduceIte] at checked
        cases originEq : origins[entry.2]? with
        | none =>
          simp [originEq, bind, StateT.bind, StateT.lift, Except.bind] at checked
        | some origin =>
          cases origin with
          | none =>
            simp [originEq, bind, StateT.bind, StateT.lift, Except.bind] at checked
          | some input =>
            simp only [originEq] at checked
            repeat' first
              | contradiction
              | split at checked
              | (dsimp only [StateT.bind, StateT.pure, StateT.lift, Except.bind,
                  Except.pure, bind, pure] at checked
                 first | contradiction | split at checked)
            all_goals
              have same := congrArg Prod.fst (Except.ok.inj checked)
              cases same
              exact ⟨rfl, fun _ => ⟨input, rfl, by simp_all, by simp_all, by simp_all⟩⟩
      · simp only [service] at checked
        have same := congrArg Prod.fst (Except.ok.inj checked)
        cases same
        exact ⟨rfl, fun impossible => False.elim (service impossible)⟩

private theorem lowerM_run'_ok {α : Type} {action : LowerM α} {initial : LowerState} {value : α}
    (accepted : action.run' initial = .ok value) :
    ∃ final, action initial = .ok (value, final) := by
  cases h : action initial with
  | error error => simp [StateT.run', h, Functor.map, Except.map] at accepted
  | ok result =>
    have same : result.1 = value := by
      simpa only [StateT.run', h, Functor.map, Except.map, Except.ok.injEq] using accepted
    exact ⟨result.2, same ▸ rfl⟩

private theorem formalInputOrigin {offset length operand input : Nat}
    (origin : (List.replicate offset none ++ (List.range length).map some)[operand]? =
      some (some input)) : operand = offset + input ∧ input < length := by
  by_cases before : operand < offset
  · rw [List.getElem?_append_left (by simpa using before)] at origin
    simp [before] at origin
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt before)] at origin
    simp only [List.length_replicate, List.getElem?_map] at origin
    by_cases bound : operand - offset < length
    · rw [List.getElem?_range bound] at origin
      simp only [Option.map_some, Option.some.injEq] at origin
      omega
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt bound)] at origin
      contradiction

/-- An application in the recursively inventoried lowered tree identifies an
original source instruction at the same site and a successful application
resolver. Service operands are shifted original formal inputs, never produced
results; the mapped owner and nominal contract come from actual checks. -/
theorem lowerProtocol_application {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {headers : List ProtocolSignature} {function : Function}
    {caller signature : ProtocolSignature} {raw : RawRegion Ty ProtocolOp}
    {indices : List Nat} {site : String}
    (accepted : lowerProtocol snapshot domains summaries headers function caller = .ok raw)
    (occurs : .protocolApply signature indices site ∈ raw.operations) :
    ∃ interface instructions terminal offset name roles operands regions,
      function.interface = some interface ∧ function.body = .block instructions terminal ∧
      .instruction (.protocolApply name roles) operands signature.outputs regions site ∈ instructions ∧
      validProtocolIdentifier site = true ∧
      resolveProtocolApplication snapshot headers interface name roles = .ok (signature, indices) ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (signature.inputs.zip signature.inputScopes).zip operands → type.isService = true →
        ∃ input, operand = offset + input ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => indices[role]?.getD 0)).length = 1 ∧
          caller.inputScopes[input]? = some (scope.map (fun role => indices[role]?.getD 0))) := by
  cases interfaceEq : function.interface with
  | none => simp [lowerProtocol, interfaceEq] at accepted
  | some interface =>
    cases bodyEq : function.body with
    | block instructions terminal =>
      simp only [lowerProtocol, interfaceEq, bodyEq] at accepted
      obtain ⟨final, lowered⟩ := lowerM_run'_ok accepted
      obtain ⟨offset, context, facts, identities, before, after, descriptor, operands,
        results, regions, sourceSite, member, resolved⟩ := lowerProtocolInstructions_application_origin lowered occurs
      obtain ⟨name, roles, rfl, rfl, validSite, application, _, rfl, services⟩ :=
        resolveProtocolOp_application resolved
      refine ⟨interface, instructions, terminal, offset, name, roles, operands, regions,
        rfl, rfl, member, validSite, application, ?_⟩
      intro type scope operand present service
      obtain ⟨input, origin, contract, singleton, owner⟩ := services type scope operand present service
      obtain ⟨position, bounded⟩ := formalInputOrigin origin
      exact ⟨input, position, bounded, contract, singleton, owner⟩

/-- Closed value profile. Group values retain the same explicit F/G assignment;
service capabilities remain at the open boundary. -/
def Ty.closedValue : Ty → Bool
  | .boolean | .index | .field _ | .vector _ | .group _ => true
  | .service _ => false

def Op.closedValues (op : Op) : Bool := (op.arguments ++ op.results).all Ty.closedValue

def ProtocolOp.closed (op : ProtocolOp) : Except String Op :=
  match op with
  | .calculate calculation _ =>
    if calculation.closedValues then .ok calculation else .error "structured-closed-type"
  | .localCall helper _ 0 _ => .ok (.invoke helper)
  | .guard 0 _ => .ok .guard
  | .mark site => .ok (.mark site)
  | _ => .error "structured-open-profile"

def closedRootTree : RawRegion Ty ProtocolOp → Except String (RawRegion Ty Op)
  | .ret refs => .ok (.ret refs)
  | .stop _ => .error "structured-protocol-terminator"
  | .letOp op args results .nil next => do
    return .letOp (← op.closed) args results .nil (← closedRootTree next)
  | .letOp _ _ _ (.cons ..) _ => .error "structured-protocol-region"
  | .bind mid body next => do
    return .bind mid (← closedRootTree body) (← closedRootTree next)

end Zkc.Source.Structured
