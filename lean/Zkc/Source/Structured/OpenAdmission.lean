module

public import Zkc.Source.Structured.RepeatAdmission

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
  | .protocolRepeat carried maximum roles stateScopes =>
    recordSite site true
    return .repeat (← resolveRepeatSpec interface arguments results carried maximum roles stateScopes) site
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
  | .statement relation selectors acceptance target =>
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
    let selectedInputs ← (operands.zip selectors).mapM fun (operand, selector) => do
      let some (some input) := origins[operand]? | throw "structured-statement-input"
      pure (ContractSelector.mk .input input selector)
    let targets := (snapshot.contracts.filter (·.owner == function.name)).flatMap
      (fun contract => contract.clauses.filter (·.kind == .target))
    let projectionMatches := fun clause : ContractClause =>
        clause.subject == ⟨relation, selectedInputs⟩ &&
        match clause.decision with
        | some decision => decision.direction == .output && decision.port == acceptance
        | none => false
    -- Match native original-PIR admission: a standalone statement is allowed;
    -- when targets are declared its projection must agree with one of them.
    match target with
    | some name =>
      if !(targets.any fun clause => clause.name == name && projectionMatches clause) then
        throw "structured-statement-contract"
    | none =>
      if !targets.isEmpty && !targets.any projectionMatches then throw "structured-statement-contract"
    return .statement relation arguments selectors acceptance
  | _ =>
    let op ← resolveOp snapshot domains .protocol context facts identities descriptor operands results site
    if allowed : op.isCalculation = true then return .calculate op allowed
    else throw "structured-protocol-operation"

/-- A callback lowerer receives a fresh isolated context and explicit lexical
origins. It shares the enclosing definition's site state. -/
abbrev ProtocolChild := List Ty → List (Option Nat) → Facts → List Nat → Block →
  LowerM (RawRegion Ty ProtocolOp)

/-- Lower the stored singleton callback. Every other operation has no regions. -/
def lowerProtocolRegions (child : ProtocolChild) (op : ProtocolOp)
    (operands : List Nat) (origins : List (Option Nat)) (facts : Facts)
    (identities : List Nat) (regions : List WireRegion) : LowerM (RawRegions Ty ProtocolOp) := do
  match op with
  | .repeat spec _ =>
    let [.region inputs outputs body] := regions | throw "structured-protocol-region"
    if inputs != .index :: (spec.state ++ spec.captures) || outputs != spec.state then
      throw "structured-protocol-signature"
    let raw ← child inputs (repeatOrigins spec operands origins)
      (repeatFacts spec operands identities facts) spec.roles body
    return .cons inputs outputs raw .nil
  | _ =>
    if !regions.isEmpty then throw "structured-protocol-region"
    return .nil

/-- The ordinary instruction spine is shared by roots and repeat callbacks.
The callback's maximum never participates in this traversal. -/
def lowerProtocolInstructionsWith (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function) (headers : List ProtocolSignature)
    (interface : ProtocolInterface) (scopes : List (List Nat)) (child : ProtocolChild)
    (exitKind : ProtocolExit) (active : List Nat) (terminal : Terminator) :
    List Ty → List (Option Nat) → Facts → List Nat → List Instruction →
      LowerM (RawRegion Ty ProtocolOp)
  | _, _, _, _, [] => do
    let refs ← match exitKind, terminal with
      | .entryReturn, .ret refs | .repeatYield, .yield refs => pure refs
      | _, _ => throw "structured-protocol-terminator"
    if !validRefs refs then throw "structured-reference-limit"
    return .ret refs
  | context, origins, facts, identities, .instruction descriptor operands results regions site :: rest => do
    checkProtocolPlacement exitKind descriptor
    let op ← resolveProtocolOp snapshot domains function headers interface scopes context origins facts identities
      descriptor operands results site
    checkProtocolRoles active op
    let bodies ← lowerProtocolRegions child op operands origins facts identities regions
    let operandOrigins := operands.map fun index => identities[index]?
    let resultOrigins := (resultIdentities summaries descriptor operandOrigins results.length).zipIdx.map
      fun (source, result) => match source with
        | some original => original + results.length
        | none => result
    let next ← lowerProtocolInstructionsWith snapshot domains summaries function headers interface scopes
      child exitKind active terminal
      (results ++ context) (List.replicate results.length none ++ origins)
      (facts.shift results.length) (resultOrigins ++ identities.map (· + results.length)) rest
    return .letOp (.mark site) [] [] .nil (.letOp op operands results bodies next)

/-- Stored depth is admission capacity, independent of iteration count. -/
def lowerProtocolBlock (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function) (headers : List ProtocolSignature)
    (interface : ProtocolInterface) (scopes : List (List Nat)) :
    Nat → ProtocolExit → List Ty → List (Option Nat) → Facts → List Nat → Block →
      LowerM (RawRegion Ty ProtocolOp)
  | 0, _, _, _, _, _, _ => throw "structured-region-depth"
  | depth + 1, exitKind, context, origins, facts, active, .block instructions terminal =>
    lowerProtocolInstructionsWith snapshot domains summaries function headers interface scopes
      (lowerProtocolBlock snapshot domains summaries function headers interface scopes depth .repeatYield)
      exitKind active terminal context origins facts (List.range context.length) instructions

/-- The sole body lowering is separate from the full header phase for reusable proofs. -/
def lowerProtocol (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (headers : List ProtocolSignature)
    (function : Function) (signature : ProtocolSignature) : Except String (RawRegion Ty ProtocolOp) := do
  let some interface := function.interface | throw "structured-protocol-interface"
  (lowerProtocolBlock snapshot domains summaries function headers interface signature.inputScopes
    64 .entryReturn function.inputs ((List.range function.inputs.length).map some) []
    (List.range interface.roles.length) function.body).run' {}

/-- Check a complete protocol using the supplied full header table. The empty
default is an application-free convenience: every retained application then
fails header resolution. Whole-unit admission always supplies all headers. -/
def checkProtocol (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function)
    (headers : List ProtocolSignature := []) : Except String CheckedProtocol := do
  let signature ← resolveProtocolSignature function
  let raw ← lowerProtocol snapshot domains summaries headers function signature
  formProtocol signature raw

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

theorem lowerProtocolRegions_application_origin {child : ProtocolChild} {op : ProtocolOp}
    {operands : List Nat} {origins : List (Option Nat)} {facts : Facts} {identities : List Nat}
    {regions : List WireRegion} {initial final : LowerState} {bodies : RawRegions Ty ProtocolOp}
    (accepted : lowerProtocolRegions child op operands origins facts identities regions initial =
      .ok (bodies, final))
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ bodies.operations) :
    ∃ spec repeatSite inputs outputs body raw,
      op = .repeat spec repeatSite ∧ regions = [.region inputs outputs body] ∧
      child inputs (repeatOrigins spec operands origins) (repeatFacts spec operands identities facts)
        spec.roles body initial = .ok (raw, final) ∧
      .protocolApply signature indices site ∈ raw.operations := by
  cases op <;> simp only [lowerProtocolRegions] at accepted
  all_goals
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply] at accepted
    repeat' first | contradiction | split at accepted
  all_goals first
    | (cases accepted; simp [RawRegions.operations] at occurs)
    | skip
  obtain ⟨raw, middle, lowered, output⟩ := lowerM_bind_ok accepted
  cases Except.ok.inj output
  simp only [RawRegions.operations, List.append_nil] at occurs
  exact ⟨_, _, _, _, _, raw, rfl, rfl, lowered, occurs⟩

/-- One spine inversion either finds the original application instruction or
exposes the actual isolated callback lowering that contains it. -/
theorem lowerProtocolInstructionsWith_application_origin {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {function : Function} {headers : List ProtocolSignature}
    {interface : ProtocolInterface} {scopes : List (List Nat)} {child : ProtocolChild}
    {exitKind : ProtocolExit} {active : List Nat} {terminal : Terminator}
    {context : List Ty} {origins : List (Option Nat)} {facts : Facts} {identities : List Nat}
    {instructions : List Instruction} {initial final : LowerState} {raw : RawRegion Ty ProtocolOp}
    (accepted : (lowerProtocolInstructionsWith snapshot domains summaries function headers interface scopes
      child exitKind active terminal context origins facts identities instructions) initial = .ok (raw, final))
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ raw.operations) :
    ∃ offset context' facts' identities' before after descriptor operands results regions sourceSite,
      .instruction descriptor operands results regions sourceSite ∈ instructions ∧
      ((resolveProtocolOp snapshot domains function headers interface scopes context'
          (List.replicate offset none ++ origins) facts' identities'
          descriptor operands results sourceSite) before =
            .ok (.protocolApply signature indices site, after) ∨
       ∃ spec repeatSite inputs outputs body callback bodyBefore bodyAfter,
        (resolveProtocolOp snapshot domains function headers interface scopes context'
          (List.replicate offset none ++ origins) facts' identities'
          descriptor operands results sourceSite) before = .ok (.repeat spec repeatSite, after) ∧
        regions = [.region inputs outputs body] ∧
        child inputs (repeatOrigins spec operands (List.replicate offset none ++ origins))
          (repeatFacts spec operands identities' facts') spec.roles body bodyBefore =
            .ok (callback, bodyAfter) ∧
        .protocolApply signature indices site ∈ callback.operations ∧
        .repeat spec repeatSite ∈ raw.operations) := by
  induction instructions generalizing context origins facts identities initial final raw with
  | nil =>
    simp only [lowerProtocolInstructionsWith] at accepted
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply] at accepted
    repeat' first
      | contradiction
      | split at accepted
      | (dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply] at accepted
         first | contradiction | split at accepted)
    all_goals cases accepted; simp [RawRegion.operations] at occurs
  | cons instruction rest ih =>
    cases instruction with
    | instruction descriptor operands results regions sourceSite =>
      simp only [lowerProtocolInstructionsWith] at accepted
      obtain ⟨_, middle, _, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨op, resolvedState, resolved, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨_, bodyState, _, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨bodies, nextState, loweredBodies, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨next, last, lowered, output⟩ := lowerM_bind_ok accepted
      have same : (.letOp (.mark sourceSite) [] [] .nil
          (.letOp op operands results bodies next) : RawRegion Ty ProtocolOp) = raw :=
        congrArg Prod.fst (Except.ok.inj output)
      subst raw
      simp only [RawRegion.operations, RawRegions.operations, List.nil_append,
        List.mem_cons, List.mem_append] at occurs
      rcases occurs with impossible | sameOp | inBody | inNext
      · cases impossible
      · subst op
        exact ⟨0, context, facts, identities, middle, resolvedState, descriptor, operands,
          results, regions, sourceSite, List.mem_cons_self, Or.inl resolved⟩
      · obtain ⟨spec, repeatSite, inputs, outputs, body, callback, sameOp, sameRegions,
          childEq, childOccurs⟩ := lowerProtocolRegions_application_origin loweredBodies inBody
        subst op
        exact ⟨0, context, facts, identities, middle, resolvedState, descriptor, operands,
          results, regions, sourceSite, List.mem_cons_self,
          Or.inr ⟨spec, repeatSite, inputs, outputs, body, callback, bodyState, nextState,
            resolved, sameRegions, childEq, childOccurs, by
              simp [RawRegion.operations, RawRegions.operations]⟩⟩
      · obtain ⟨offset, ctx, fs, ids, before, after, desc, args, outs, bodies, s, member, equation⟩ :=
          ih lowered inNext
        refine ⟨offset + results.length, ctx, fs, ids, before, after, desc, args, outs,
          bodies, s, List.mem_cons_of_mem _ member, ?_⟩
        simp only [← List.replicate_append_replicate, List.append_assoc]
        rcases equation with direct | ⟨spec, repeatSite, inputs, outputs, body, callback,
          bodyBefore, bodyAfter, resolved, sameRegions, childEq, childOccurs, parentOccurs⟩
        · exact Or.inl direct
        · exact Or.inr ⟨spec, repeatSite, inputs, outputs, body, callback, bodyBefore,
            bodyAfter, resolved, sameRegions, childEq, childOccurs, by
              simp only [RawRegion.operations, RawRegions.operations, List.nil_append,
                List.mem_cons, List.mem_append]
              exact Or.inr (Or.inr (Or.inr parentOccurs))⟩


/-- Recursive inversion discharges the child hypothesis on stored depth. Every
application in the complete raw tree was resolved under an inherited lexical
origin environment. P may express any invariant stable under result prefixes
and the service-only repeat capture transformation. -/
theorem lowerProtocolBlock_application_source {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {function : Function} {headers : List ProtocolSignature}
    {interface : ProtocolInterface} {scopes : List (List Nat)}
    (P : List (Option Nat) → Prop)
    (resultsPreserve : ∀ count origins, P origins → P (List.replicate count none ++ origins))
    (capturesPreserve : ∀ spec operands origins, P origins → P (repeatOrigins spec operands origins))
    {depth : Nat} {exitKind : ProtocolExit} {active : List Nat} {body : Block}
    {context : List Ty} {origins : List (Option Nat)} {facts : Facts}
    {initial final : LowerState} {raw : RawRegion Ty ProtocolOp}
    (accepted : lowerProtocolBlock snapshot domains summaries function headers interface scopes
      depth exitKind context origins facts active body initial = .ok (raw, final))
    (initialOrigins : P origins)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ raw.operations) :
    ∃ context' origins' facts' identities' before after descriptor operands results regions sourceSite,
      .instruction descriptor operands results regions sourceSite ∈ body.storedInstructions ∧
      P origins' ∧
      (resolveProtocolOp snapshot domains function headers interface scopes context'
        origins' facts' identities' descriptor operands results sourceSite) before =
          .ok (.protocolApply signature indices site, after) := by
  induction depth generalizing exitKind active body context origins facts initial final raw with
  | zero => contradiction
  | succ depth ih =>
    cases body with
    | block instructions terminal =>
      obtain ⟨offset, ctx, fs, ids, before, after, desc, args, outs, bodies, s, member, equation⟩ :=
        lowerProtocolInstructionsWith_application_origin accepted occurs
      have inherited := resultsPreserve offset origins initialOrigins
      rcases equation with equation | ⟨spec, repeatSite, inputs, outputs, body, callback,
        bodyBefore, bodyAfter, _, sameRegions, lowered, inCallback, _⟩
      · refine ⟨ctx, _, fs, ids, before, after, desc, args, outs, bodies, s, ?_, inherited, equation⟩
        rw [Block.storedInstructions]
        exact List.mem_flatMap.mpr ⟨_, member, by rw [Instruction.storedInstructions]; exact List.mem_cons_self⟩
      · obtain ⟨ctx', origins', fs', ids', before', after', desc', args', outs', regions',
          site', source, invariant, resolved⟩ :=
          ih lowered (capturesPreserve spec args _ inherited) inCallback
        refine ⟨ctx', origins', fs', ids', before', after', desc', args', outs', regions',
          site', ?_, invariant, resolved⟩
        rw [Block.storedInstructions]
        apply List.mem_flatMap.mpr
        refine ⟨.instruction desc args outs bodies s, member, ?_⟩
        simpa only [Instruction.storedInstructions, sameRegions, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, WireRegion.storedInstructions, List.mem_cons] using
          (Or.inr source : Instruction.instruction desc' args' outs' regions' site' =
            Instruction.instruction desc args outs [.region inputs outputs body] s ∨
            .instruction desc' args' outs' regions' site' ∈ body.storedInstructions)

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

/-- For a callback-free tree, preserve the original top-level instruction and
SSA-offset service witness. Recursive callbacks use the origin-environment
inversion below because captures can reorder their original formal inputs. -/
theorem lowerProtocol_application {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {headers : List ProtocolSignature} {function : Function}
    {caller signature : ProtocolSignature} {raw : RawRegion Ty ProtocolOp}
    {indices : List Nat} {site : String}
    (accepted : lowerProtocol snapshot domains summaries headers function caller = .ok raw)
    (occurs : .protocolApply signature indices site ∈ raw.operations)
    (flat : raw.operations.all (fun op => op.regions.isEmpty) = true) :
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
        results, regions, sourceSite, member, resolved⟩ :=
          lowerProtocolInstructionsWith_application_origin lowered occurs
      have direct : (resolveProtocolOp snapshot domains function headers interface caller.inputScopes
          context (List.replicate offset none ++ (List.range function.inputs.length).map some)
          facts identities descriptor operands results sourceSite) before =
            .ok (.protocolApply signature indices site, after) := by
        rcases resolved with direct | ⟨spec, repeatSite, inputs, outputs, body, callback,
          bodyBefore, bodyAfter, _, _, _, _, inTree⟩
        · exact direct
        · have impossible := List.all_eq_true.mp flat (.repeat spec repeatSite) inTree
          contradiction
      obtain ⟨name, roles, rfl, rfl, validSite, application, _, rfl, services⟩ :=
        resolveProtocolOp_application direct
      refine ⟨interface, instructions, terminal, offset, name, roles, operands, regions,
        rfl, rfl, member, validSite, application, ?_⟩
      intro type scope operand present service
      obtain ⟨input, origin, contract, singleton, owner⟩ := services type scope operand present service
      obtain ⟨position, bounded⟩ := formalInputOrigin origin
      exact ⟨input, position, bounded, contract, singleton, owner⟩


/-- Complete-tree inversion keeps the actual callback origin environment.
Captured services still name bounded inputs of the enclosing protocol, with
exact nominal contract and mapped singleton owner checked at the application. -/
theorem lowerProtocol_application_source {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {headers : List ProtocolSignature} {function : Function}
    {caller signature : ProtocolSignature} {raw : RawRegion Ty ProtocolOp}
    {indices : List Nat} {site : String}
    (accepted : lowerProtocol snapshot domains summaries headers function caller = .ok raw)
    (occurs : .protocolApply signature indices site ∈ raw.operations) :
    ∃ interface context, ∃ origins : List (Option Nat), ∃ name roles operands regions,
      .instruction (.protocolApply name roles) operands signature.outputs regions site ∈
        function.body.storedInstructions ∧
      function.interface = some interface ∧ validProtocolIdentifier site = true ∧
      resolveProtocolApplication snapshot headers interface name roles = .ok (signature, indices) ∧
      typesAt context operands = .ok signature.inputs ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (signature.inputs.zip signature.inputScopes).zip operands → type.isService = true →
        ∃ input, origins[operand]? = some (some input) ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => indices[role]?.getD 0)).length = 1 ∧
          caller.inputScopes[input]? = some (scope.map (fun role => indices[role]?.getD 0))) := by
  cases interfaceEq : function.interface with
  | none => simp [lowerProtocol, interfaceEq] at accepted
  | some interface =>
    simp only [lowerProtocol, interfaceEq] at accepted
    obtain ⟨final, lowered⟩ := lowerM_run'_ok accepted
    let P := fun origins : List (Option Nat) =>
      ∀ input, some input ∈ origins → input < function.inputs.length
    have resultPreserves : ∀ count origins, P origins → P (List.replicate count none ++ origins) := by
      intro count origins h input member
      rcases List.mem_append.mp member with fresh | old
      · simp at fresh
      · exact h input old
    have capturePreserves : ∀ spec operands origins, P origins → P (repeatOrigins spec operands origins) := by
      intro spec operands origins h input member
      have inherited := repeatOrigins_inherited spec operands origins member
      rcases List.mem_cons.mp inherited with impossible | old
      · contradiction
      · exact h input old
    have initial : P ((List.range function.inputs.length).map some) := by
      intro input member
      simpa using member
    obtain ⟨context, origins, facts, identities, before, after, descriptor, operands,
      results, regions, sourceSite, source, bounded, resolved⟩ :=
        lowerProtocolBlock_application_source P resultPreserves capturePreserves lowered initial occurs
    obtain ⟨name, roles, rfl, rfl, validSite, application, types, rfl, services⟩ :=
      resolveProtocolOp_application resolved
    refine ⟨interface, context, origins, name, roles, operands, regions, source, rfl, validSite, application, types, ?_⟩
    intro type scope operand present service
    obtain ⟨input, origin, contract, singleton, owner⟩ := services type scope operand present service
    exact ⟨input, origin, bounded input (List.mem_of_getElem? origin), contract, singleton, owner⟩

/-- A successful callback lowerer checks every stored region. -/
theorem lowerProtocolRegions_statementFree {child : ProtocolChild} {op : ProtocolOp}
    {operands : List Nat} {origins : List (Option Nat)} {facts : Facts} {identities : List Nat}
    {regions : List WireRegion} {initial final : LowerState} {bodies : RawRegions Ty ProtocolOp}
    (childrenFree : ∀ {inputs origins facts active body initial final raw},
      child inputs origins facts active body initial = .ok (raw, final) →
        body.storedInstructions.any Instruction.isStatement = false)
    (accepted : lowerProtocolRegions child op operands origins facts identities regions initial =
      .ok (bodies, final)) :
    (regions.flatMap WireRegion.storedInstructions).any Instruction.isStatement = false := by
  cases op <;> simp only [lowerProtocolRegions] at accepted
  all_goals
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure, Function.comp_apply] at accepted
    repeat' first | contradiction | split at accepted
  all_goals first
    | (cases accepted; simp_all)
    | skip
  obtain ⟨raw, middle, lowered, output⟩ := lowerM_bind_ok accepted
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WireRegion.storedInstructions]
    using childrenFree lowered

/-- Entry statements require the explicit top-level hypothesis; callbacks are
statement-free by their exit-mode placement check, independently of maximum. -/
theorem lowerProtocolInstructionsWith_statementFree
    {snapshot : Snapshot} {domains : List DomainSpec} {summaries : IdentitySummaries}
    {function : Function} {headers : List ProtocolSignature} {interface : ProtocolInterface}
    {scopes : List (List Nat)} {child : ProtocolChild} {exitKind : ProtocolExit}
    {active : List Nat} {terminal : Terminator} {context : List Ty}
    {origins : List (Option Nat)} {facts : Facts} {identities : List Nat}
    {instructions : List Instruction} {initial final : LowerState} {raw : RawRegion Ty ProtocolOp}
    (childrenFree : ∀ {inputs origins facts active body initial final raw},
      child inputs origins facts active body initial = .ok (raw, final) →
        body.storedInstructions.any Instruction.isStatement = false)
    (topFree : exitKind = .entryReturn → instructions.any Instruction.isStatement = false)
    (accepted : lowerProtocolInstructionsWith snapshot domains summaries function headers interface scopes
      child exitKind active terminal context origins facts identities instructions initial = .ok (raw, final)) :
    (instructions.flatMap Instruction.storedInstructions).any Instruction.isStatement = false := by
  induction instructions generalizing context origins facts identities initial final raw with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction with
    | instruction descriptor operands results regions site =>
      simp only [lowerProtocolInstructionsWith] at accepted
      obtain ⟨_, middle, placed, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨op, resolvedState, _, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨_, bodyState, _, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨bodies, nextState, loweredBodies, accepted⟩ := lowerM_bind_ok accepted
      obtain ⟨next, last, lowered, _⟩ := lowerM_bind_ok accepted
      have headFree : Instruction.isStatement (.instruction descriptor operands results regions site) = false := by
        cases exitKind with
        | entryReturn => exact (Bool.or_eq_false_iff.mp (topFree rfl)).1
        | repeatYield =>
          have placement := lowerM_lift_ok placed
          cases descriptor <;> first | rfl | (simp [checkProtocolPlacement] at placement)
      have tailFree := ih (fun h => (Bool.or_eq_false_iff.mp (topFree h)).2) lowered
      have regionsFree := lowerProtocolRegions_statementFree childrenFree loweredBodies
      simpa only [List.flatMap_cons, Instruction.storedInstructions, List.cons_append,
        List.any_cons, List.any_append, headFree, regionsFree, Bool.false_or] using tailFree

/-- Callback statement-freeness follows from recursive successful lowering. -/
theorem lowerProtocolBlock_statementFree {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {function : Function} {headers : List ProtocolSignature}
    {interface : ProtocolInterface} {scopes : List (List Nat)}
    {depth : Nat} {exitKind : ProtocolExit} {active : List Nat} {body : Block}
    {context : List Ty} {origins : List (Option Nat)} {facts : Facts}
    {initial final : LowerState} {raw : RawRegion Ty ProtocolOp}
    (accepted : lowerProtocolBlock snapshot domains summaries function headers interface scopes
      depth exitKind context origins facts active body initial = .ok (raw, final))
    (topFree : exitKind = .entryReturn →
      body.topLevelInstructions.any Instruction.isStatement = false) :
    body.storedInstructions.any Instruction.isStatement = false := by
  induction depth generalizing exitKind active body context origins facts initial final raw with
  | zero => contradiction
  | succ depth ih =>
    cases body with
    | block instructions terminal =>
      rw [Block.storedInstructions]
      apply lowerProtocolInstructionsWith_statementFree (topFree := topFree) (accepted := accepted)
      intro inputs origins facts active body initial final raw lowered
      exact ih lowered (by intro impossible; cases impossible)

/-- Full stored statement-freeness of a lowered protocol whose entry is
statement-free. Applications separately establish that entry hypothesis. -/
theorem lowerProtocol_statementFree {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {headers : List ProtocolSignature} {function : Function}
    {signature : ProtocolSignature} {raw : RawRegion Ty ProtocolOp}
    (accepted : lowerProtocol snapshot domains summaries headers function signature = .ok raw)
    (topFree : function.body.topLevelInstructions.any Instruction.isStatement = false) :
    function.body.storedInstructions.any Instruction.isStatement = false := by
  cases interfaceEq : function.interface with
  | none => simp [lowerProtocol, interfaceEq] at accepted
  | some interface =>
    simp only [lowerProtocol, interfaceEq, StateT.run', Functor.map,
      Except.map] at accepted
    split at accepted
    · contradiction
    · rename_i result lowered
      exact lowerProtocolBlock_statementFree lowered (fun _ => topFree)

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
