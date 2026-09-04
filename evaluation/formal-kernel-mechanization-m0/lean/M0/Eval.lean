import M0.Term

/-!
# Deterministic K1 evaluation and the finite Schnorr denotation

The evaluator is a total, fuelled function.  It follows the Section 7 strict
left-to-right order and carries the four deterministic charge coordinates.
Primitive semantics is an exact-reference-qualified deterministic function;
M2 instantiates `nat.lt`, the only primitive in the R1B check.  The function
`enforce` applies result-capacity preflight and componentwise limits to a fixed
core run.

The eight Section 8 noncompletion classes are represented explicitly.  K1
does not define a universal canonical byte encoding for them, so only
completed values acquire `completionDatum` bytes here.
-/

namespace M0

/-- The four deterministic K1 charge coordinates. -/
structure Charge where
  steps : Nat := 0
  iterationItems : Nat := 0
  primitiveWork : Nat := 0
  resultBytes : Nat := 0
  deriving Repr, DecidableEq

def Charge.add (left right : Charge) : Charge := {
  steps := left.steps + right.steps
  iterationItems := left.iterationItems + right.iterationItems
  primitiveWork := left.primitiveWork + right.primitiveWork
  resultBytes := left.resultBytes + right.resultBytes
}

def Charge.step (charge : Charge) : Charge := { charge with steps := charge.steps + 1 }

def Charge.iteration (charge : Charge) : Charge :=
  { charge with iterationItems := charge.iterationItems + 1 }

def Charge.primitive (charge : Charge) (work : Nat) : Charge :=
  { charge with primitiveWork := charge.primitiveWork + work }

/-- Per-request deterministic limits, in the Foundation page's fixed order. -/
structure Limits where
  maximumSteps : Nat
  maximumIterationItems : Nat
  maximumPrimitiveWork : Nat
  maximumResultBytes : Nat
  deriving Repr, DecidableEq

def Limits.ComponentwiseLE (small large : Limits) : Prop :=
  small.maximumSteps ≤ large.maximumSteps ∧
  small.maximumIterationItems ≤ large.maximumIterationItems ∧
  small.maximumPrimitiveWork ≤ large.maximumPrimitiveWork ∧
  small.maximumResultBytes ≤ large.maximumResultBytes

def Charge.Fits (charge : Charge) (limits : Limits) : Prop :=
  charge.steps ≤ limits.maximumSteps ∧
  charge.iterationItems ≤ limits.maximumIterationItems ∧
  charge.primitiveWork ≤ limits.maximumPrimitiveWork ∧
  charge.resultBytes ≤ limits.maximumResultBytes

instance (charge : Charge) (limits : Limits) : Decidable (charge.Fits limits) := by
  unfold Charge.Fits
  infer_instance

theorem Charge.fits_mono {charge : Charge} {small large : Limits}
    (fits : charge.Fits small) (larger : small.ComponentwiseLE large) :
    charge.Fits large := by
  exact ⟨Nat.le_trans fits.1 larger.1,
    Nat.le_trans fits.2.1 larger.2.1,
    Nat.le_trans fits.2.2.1 larger.2.2.1,
    Nat.le_trans fits.2.2.2 larger.2.2.2⟩

/-- The exact completion/noncompletion partition in Foundation Section 8. -/
inductive Outcome where
  | completed
  | unsupported
  | missingDependency
  | cannotAnswer
  | kindMismatch
  | malformed
  | refused
  | deterministicLimitExceeded
  | checkerFailure
  deriving Repr, DecidableEq

/-- A primitive either returns a typed value, completes with a typed domain
failure, or reports a checker defect.  Its work is charged atomically after
strict evaluation of all arguments. -/
inductive PrimitiveResult where
  | success (value : TypedValue) (work : Nat)
  | domainFailure (failure : FailureType) (payload : TypedValue) (work : Nat)
  | checkerFailure (code : String)
  deriving Repr

abbrev PrimitiveDenotation := Datum → List TypedValue → PrimitiveResult

/-- The semantic result before request limits and completion framing. -/
inductive CoreResult where
  | success (value : TypedValue) (charge : Charge)
  | domainFailure (failure : FailureType) (payload : TypedValue) (charge : Charge)
  | checkerFailure (code : String) (charge : Charge)
  deriving Repr

def CoreResult.addCharge (before : Charge) : CoreResult → CoreResult
  | .success value charge => .success value (before.add charge)
  | .domainFailure failure payload charge =>
      .domainFailure failure payload (before.add charge)
  | .checkerFailure code charge => .checkerFailure code (before.add charge)

def CoreResult.addStep (result : CoreResult) : CoreResult :=
  match result with
  | .success value charge => .success value charge.step
  | .domainFailure failure payload charge => .domainFailure failure payload charge.step
  | .checkerFailure code charge => .checkerFailure code charge.step

def evalTerms (evaluate : Term → CoreResult) (terms : List Term) : CoreResult :=
  terms.foldl (fun accumulated term =>
    match accumulated with
    | .success (.mk _ (.seq values)) charge =>
        match evaluate term with
        | .success value childCharge =>
            .success ⟨.mk .unit (.sequence (.mk .unit .unit) 0), .seq (values ++ [value.datum])⟩
              (charge.add childCharge)
        | result => result.addCharge charge
    | result => result) (.success ⟨.mk .unit (.sequence (.mk .unit .unit) 0), .seq []⟩ {})

def valuesOfTermResult : CoreResult → Option (List Datum × Charge)
  | .success ⟨_, .seq values⟩ charge => some (values, charge)
  | _ => none

def typedValuesOfTerms (evaluate : Term → CoreResult) (terms : List Term) :
    Except CoreResult (List TypedValue × Charge) :=
  terms.foldl (fun accumulated term => do
    let (values, charge) ← accumulated
    match evaluate term with
    | .success value childCharge => pure (values ++ [value], charge.add childCharge)
    | result => throw (result.addCharge charge)) (pure ([], {}))

def evalRecordValues (evaluate : Term → CoreResult) (fields : List (Nat × Term)) :
    Except CoreResult (List (Nat × TypedValue) × Charge) :=
  fields.foldl (fun accumulated field => do
    let (values, charge) ← accumulated
    match evaluate field.2 with
    | .success value childCharge => pure (values ++ [(field.1, value)], charge.add childCharge)
    | result => throw (result.addCharge charge)) (pure ([], {}))

def typeAt? (entries : List (Nat × ValueType)) (ordinal : Nat) : Option ValueType :=
  (entries.find? fun entry => entry.1 == ordinal).map Prod.snd

def datumAt? (entries : List (Nat × Datum)) (ordinal : Nat) : Option Datum :=
  (entries.find? fun entry => entry.1 == ordinal).map Prod.snd

/-- Fuel is a host-totality guard, not a fifth request limit.  Admitted K1
terms have depth at most 48; M2 runs with fuel 64. -/
def evalCore (primitive : PrimitiveDenotation) : Nat → Term → List TypedValue → CoreResult
  | 0, _, _ => .checkerFailure "M2-CHECKER-FUEL" {}
  | fuel + 1, term, env =>
      let evaluate := fun child => evalCore primitive fuel child env
      let body : CoreResult := match term with
        | .literal value => .success value {}
        | .variable index _ => match env[index]? with
            | some value => .success value {}
            | none => .checkerFailure "M2-CHECKER-VARIABLE" {}
        | .letE bound body => match evaluate bound with
            | .success value boundCharge =>
                (evalCore primitive fuel body (value :: env)).addCharge boundCharge
            | result => result
        | .recordConstruct fields => match evalRecordValues evaluate fields with
            | .error result => result
            | .ok (values, charge) =>
                let fieldTypes := values.map fun (field : Nat × TypedValue) =>
                  (field.1, field.2.valueType)
                let data := values.map fun (field : Nat × TypedValue) =>
                  (field.1, field.2.datum)
                .success ⟨.mk .unit (.record fieldTypes), .record data⟩ charge
        | .project source ordinal => match evaluate source with
            | .success ⟨.mk _ (.record fieldTypes), .record fields⟩ charge =>
                match typeAt? fieldTypes ordinal, datumAt? fields ordinal with
                | some valueType, some datum => .success ⟨valueType, datum⟩ charge
                | _, _ => .checkerFailure "M2-CHECKER-PROJECT" charge
            | .success _ charge => .checkerFailure "M2-CHECKER-PROJECT" charge
            | result => result
        | .inject case payload sumType => match evaluate payload with
            | .success value charge => .success ⟨sumType, .variant case value.datum⟩ charge
            | result => result
        | .caseE scrutinee branches => match evaluate scrutinee with
            | .success ⟨.mk _ (.variant cases), .variant case payload⟩ charge =>
                match typeAt? cases case,
                    (branches.find? fun (branch : Nat × Term) => branch.1 == case) with
                | some payloadType, some (_, branch) =>
                    (evalCore primitive fuel branch (⟨payloadType, payload⟩ :: env)).addCharge charge
                | _, _ => .checkerFailure "M2-CHECKER-CASE" charge
            | .success _ charge => .checkerFailure "M2-CHECKER-CASE" charge
            | result => result
        | .sequenceConstruct elementType elements maximum =>
            match typedValuesOfTerms evaluate elements with
            | .error result => result
            | .ok (values, charge) =>
                .success ⟨.mk .unit (.sequence elementType maximum),
                  .seq (values.map fun (value : TypedValue) => value.datum)⟩ charge
        | .sequenceLength source => match evaluate source with
            | .success ⟨.mk domain (.sequence _ maximum), .seq values⟩ charge =>
                .success ⟨.mk domain (.nat maximum), .nat values.length⟩ charge
            | .success _ charge => .checkerFailure "M2-CHECKER-SEQUENCE-LENGTH" charge
            | result => result
        | .fail failure payload _ => match evaluate payload with
            | .success value charge => .domainFailure failure value charge
            | result => result
        | .strictIndex source index failure => match evaluate source with
            | .success ⟨.mk _ (.sequence elementType _), .seq values⟩ sourceCharge =>
                match evaluate index with
                | .success indexValue@⟨_, .nat offset⟩ indexCharge =>
                    let charge := sourceCharge.add indexCharge
                    match values[offset]? with
                    | some value => .success ⟨elementType, value⟩ charge
                    | none => .domainFailure failure indexValue charge
                | .success _ indexCharge =>
                    .checkerFailure "M2-CHECKER-STRICT-INDEX" (sourceCharge.add indexCharge)
                | result => result.addCharge sourceCharge
            | .success _ charge => .checkerFailure "M2-CHECKER-STRICT-INDEX" charge
            | result => result
        | .boundedAppend source element failure => match evaluate source with
            | .success sourceValue@⟨.mk _ (.sequence elementType maximum), .seq values⟩ sourceCharge =>
                match evaluate element with
                | .success value elementCharge =>
                    let charge := sourceCharge.add elementCharge
                    if values.length < maximum then
                      .success ⟨sourceValue.valueType, .seq (values ++ [value.datum])⟩ charge
                    else .domainFailure failure ⟨failure.payloadType, .unit⟩ charge
                | result => result.addCharge sourceCharge
            | .success _ charge => .checkerFailure "M2-CHECKER-BOUNDED-APPEND" charge
            | result => result
        | .primitiveCall reference arguments =>
            match typedValuesOfTerms evaluate arguments with
            | .error result => result
            | .ok (values, charge) => match primitive reference values with
                | .success value work => .success value (charge.primitive work)
                | .domainFailure failure payload work =>
                    .domainFailure failure payload (charge.primitive work)
                | .checkerFailure code => .checkerFailure code charge
        | .boundedIterate source initialState body =>
            let sourceResult := match source with
              | .sequence term => evaluate term
              | .range term => evaluate term
            match sourceResult with
            | .success sourceValue sourceCharge => match evaluate initialState with
                | .success initial initialCharge =>
                    let initialAccumulation : CoreResult :=
                      .success initial (sourceCharge.add initialCharge)
                    let items : List (Nat × Datum) := match source, sourceValue.datum with
                      | .sequence _, .seq values => (List.range values.length).zip values
                      | .range _, .nat bound => (List.range bound).map fun index => (index, .nat index)
                      | _, _ => []
                    items.foldl (fun accumulated (item : Nat × Datum) => match accumulated with
                      | .success state charge =>
                          let indexValue : TypedValue := ⟨.mk .unit (.nat item.1), .nat item.1⟩
                          let elementValue : TypedValue := ⟨.mk .unit (.nat item.1), item.2⟩
                          match evalCore primitive fuel body (indexValue :: elementValue :: state :: env) with
                          | .success decision@⟨_, .variant 0 payload⟩ bodyCharge =>
                              .success ⟨state.valueType, payload⟩ ((charge.add bodyCharge).iteration)
                          | .success decision@⟨_, .variant _ _⟩ bodyCharge =>
                              .success decision ((charge.add bodyCharge).iteration)
                          | result => result.addCharge charge
                      | result => result) initialAccumulation
                | result => result.addCharge sourceCharge
            | result => result
        | .conditional condition whenTrue whenFalse => match evaluate condition with
            | .success ⟨_, .bool discriminator⟩ conditionCharge =>
                (evaluate (if discriminator then whenTrue else whenFalse)).addCharge conditionCharge
            | .success _ charge => .checkerFailure "M2-CHECKER-CONDITIONAL" charge
            | result => result
      body.addStep

/-- A successful or typed-failure completion is the K1 ABI variant: success is
case zero and failure ordinal `i` is case `i+1`. -/
def completionDatum (failureOrdinal : FailureType → Option Nat) : CoreResult → Option (Datum × Charge)
  | .success value charge => some (.variant 0 value.datum, charge)
  | .domainFailure failure payload charge => do
      some (.variant ((← failureOrdinal failure) + 1) payload.datum, charge)
  | .checkerFailure _ _ => none

/-- The externally visible result.  Noncompletion has no invented payload
encoding; code is diagnostic only. -/
inductive EvaluationResult where
  | completed (completion : Datum) (charge : Charge)
  | noncompletion (outcome : Outcome) (charge : Charge) (code : String)
  deriving Repr

/-- Apply the exact four-dimensional request envelope to a fixed core run. -/
def enforce (failureOrdinal : FailureType → Option Nat) (run : CoreResult)
    (maximumCompletionBytes : Nat) (limits : Limits) : EvaluationResult :=
  if maximumCompletionBytes ≤ limits.maximumResultBytes then
    match completionDatum failureOrdinal run with
    | some (completion, charge) =>
        let finished := { charge with resultBytes := (encode completion).length }
        if finished.Fits limits then .completed completion finished
        else .noncompletion .deterministicLimitExceeded charge "K1-LIMIT"
    | none => match run with
        | .checkerFailure code charge => .noncompletion .checkerFailure charge code
        | _ => .noncompletion .checkerFailure {} "M2-CHECKER-COMPLETION"
  else .noncompletion .deterministicLimitExceeded {} "K1-LIMIT-RESULT-PREFLIGHT"

def evaluate (primitive : PrimitiveDenotation) (failureOrdinal : FailureType → Option Nat)
    (fuel : Nat) (term : Term) (env : List TypedValue)
    (maximumCompletionBytes : Nat) (limits : Limits) : EvaluationResult :=
  enforce failureOrdinal (evalCore primitive fuel term env) maximumCompletionBytes limits

/-- Evaluation is a function once primitive semantics, request data, and
limits are fixed. -/
theorem evaluation_deterministic (primitive : PrimitiveDenotation)
    (failureOrdinal : FailureType → Option Nat) (fuel : Nat) (term : Term)
    (env : List TypedValue) (maximumCompletionBytes : Nat) (limits : Limits)
    (left right : EvaluationResult)
    (hleft : evaluate primitive failureOrdinal fuel term env maximumCompletionBytes limits = left)
    (hright : evaluate primitive failureOrdinal fuel term env maximumCompletionBytes limits = right) :
    left = right := by
  exact hleft.symm.trans hright

theorem enforce_completed_mono (failureOrdinal : FailureType → Option Nat)
    (run : CoreResult) (maximumCompletionBytes : Nat) {small large : Limits}
    (larger : small.ComponentwiseLE large) (completion : Datum) (charge : Charge)
    (completed : enforce failureOrdinal run maximumCompletionBytes small =
      .completed completion charge) :
    enforce failureOrdinal run maximumCompletionBytes large = .completed completion charge := by
  unfold enforce at completed ⊢
  by_cases preflight : maximumCompletionBytes ≤ small.maximumResultBytes
  · have largerPreflight : maximumCompletionBytes ≤ large.maximumResultBytes :=
      Nat.le_trans preflight larger.2.2.2
    simp [preflight, largerPreflight] at completed ⊢
    cases completionRun : completionDatum failureOrdinal run with
    | none =>
      cases run with
      | success value coreCharge => simp [completionDatum] at completionRun
      | checkerFailure code coreCharge => simp [completionDatum] at completed
      | domainFailure failure payload coreCharge =>
        cases failureCase : failureOrdinal failure with
        | none => simp [completionDatum, failureCase] at completed
        | some ordinal => simp [completionDatum, failureCase] at completionRun
    | some pair =>
      rcases pair with ⟨produced, coreCharge⟩
      simp [completionRun] at completed ⊢
      let finished : Charge := { coreCharge with resultBytes := (encode produced).length }
      by_cases fits : finished.Fits small
      · have largerFits := Charge.fits_mono fits larger
        simp [finished, fits, largerFits] at completed ⊢
        exact completed
      · simp [finished, fits] at completed
  · simp [preflight] at completed

/-- Replay monotonicity used by the page: a completed evaluation under `small`
has the same completion and charge under every componentwise larger envelope. -/
theorem evaluation_completed_mono (primitive : PrimitiveDenotation)
    (failureOrdinal : FailureType → Option Nat) (fuel : Nat) (term : Term)
    (env : List TypedValue) (maximumCompletionBytes : Nat) {small large : Limits}
    (larger : small.ComponentwiseLE large) (completion : Datum) (charge : Charge)
    (completed : evaluate primitive failureOrdinal fuel term env maximumCompletionBytes small =
      .completed completion charge) :
    evaluate primitive failureOrdinal fuel term env maximumCompletionBytes large =
      .completed completion charge := by
  exact enforce_completed_mono failureOrdinal (evalCore primitive fuel term env)
    maximumCompletionBytes larger completion charge completed

def noFailureOrdinal : FailureType → Option Nat := fun _ => none

/-- Exact-reference implementation of the only primitive used by R1B. -/
def natLtPrimitive (natLtReference : Datum) (boolean : ValueType) : PrimitiveDenotation :=
    fun reference values =>
  if beq reference natLtReference then
    match values with
    | [⟨.mk _ (.nat _), .nat left⟩, ⟨.mk _ (.nat _), .nat right⟩] =>
        .success ⟨boolean, .bool (left < right)⟩ 1
    | _ => .checkerFailure "M2-CHECKER-NAT-LT-ABI"
  else .checkerFailure "M2-CHECKER-PRIMITIVE-REFERENCE"

def z3Literal (z3 : ValueType) (value : Nat) : Term := .literal ⟨z3, .nat value⟩
def boolLiteral (boolean : ValueType) (value : Bool) : Term := .literal ⟨boolean, .bool value⟩

def switch3 (z3 : ValueType) (natLtReference : Datum) (selector : Term)
    (branches : List Term) : Term :=
  .conditional (.primitiveCall natLtReference [selector, z3Literal z3 1])
    (branches.getD 0 (z3Literal z3 0))
    (.conditional (.primitiveCall natLtReference [selector, z3Literal z3 2])
      (branches.getD 1 (z3Literal z3 0)) (branches.getD 2 (z3Literal z3 0)))

def responseTest (z3 boolean : ValueType) (natLtReference : Datum)
    (response : Term) (y commitment challenge : Nat) : Term :=
  let expected := (commitment + challenge * y) % 3
  switch3 z3 natLtReference response [
    boolLiteral boolean (0 == expected),
    boolLiteral boolean (1 == expected),
    boolLiteral boolean (2 == expected)]

/-- The term-shaped denotation decoded from the R1B preimage. -/
def finiteSchnorrTerm (z3 boolean : ValueType) (natLtReference : Datum) : Term :=
  let y := Term.variable 0 z3
  let commitment := Term.variable 1 z3
  let challenge := Term.variable 2 z3
  let response := Term.variable 3 z3
  switch3 z3 natLtReference y [
    switch3 z3 natLtReference commitment [
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 0 0 0,
        responseTest z3 boolean natLtReference response 0 0 1,
        responseTest z3 boolean natLtReference response 0 0 2],
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 0 1 0,
        responseTest z3 boolean natLtReference response 0 1 1,
        responseTest z3 boolean natLtReference response 0 1 2],
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 0 2 0,
        responseTest z3 boolean natLtReference response 0 2 1,
        responseTest z3 boolean natLtReference response 0 2 2]],
    switch3 z3 natLtReference commitment [
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 1 0 0,
        responseTest z3 boolean natLtReference response 1 0 1,
        responseTest z3 boolean natLtReference response 1 0 2],
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 1 1 0,
        responseTest z3 boolean natLtReference response 1 1 1,
        responseTest z3 boolean natLtReference response 1 1 2],
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 1 2 0,
        responseTest z3 boolean natLtReference response 1 2 1,
        responseTest z3 boolean natLtReference response 1 2 2]],
    switch3 z3 natLtReference commitment [
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 2 0 0,
        responseTest z3 boolean natLtReference response 2 0 1,
        responseTest z3 boolean natLtReference response 2 0 2],
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 2 1 0,
        responseTest z3 boolean natLtReference response 2 1 1,
        responseTest z3 boolean natLtReference response 2 1 2],
      switch3 z3 natLtReference challenge [
        responseTest z3 boolean natLtReference response 2 2 0,
        responseTest z3 boolean natLtReference response 2 2 1,
        responseTest z3 boolean natLtReference response 2 2 2]]]

def abstractZ3 : ValueType := .mk .unit (.nat 2)
def abstractBool : ValueType := .mk .unit .bool
def abstractNatLt : Datum := .unit

/-- Denotation obtained by evaluating the portable term, with the exact
primitive coordinate abstracted to `abstractNatLt`. -/
def schnorrDenotation (y commitment challenge response : Fin 3) : Bool :=
  let env : List TypedValue := [
    ⟨abstractZ3, .nat y.val⟩,
    ⟨abstractZ3, .nat commitment.val⟩,
    ⟨abstractZ3, .nat challenge.val⟩,
    ⟨abstractZ3, .nat response.val⟩]
  match evalCore (natLtPrimitive abstractNatLt abstractBool) 64
      (finiteSchnorrTerm abstractZ3 abstractBool abstractNatLt) env with
  | .success ⟨_, .bool answer⟩ _ => answer
  | _ => false

/-- The R1B term denotation is the closed finite Schnorr equation. -/
theorem schnorr_denotation_eq_closed_form :
    ∀ y commitment challenge response : Fin 3,
      schnorrDenotation y commitment challenge response =
        decide (response.val = (commitment.val + challenge.val * y.val) % 3) := by
  rintro ⟨y, hy⟩ ⟨commitment, hc⟩ ⟨challenge, hh⟩ ⟨response, hr⟩
  have yCases : y = 0 ∨ y = 1 ∨ y = 2 := by omega
  have cCases : commitment = 0 ∨ commitment = 1 ∨ commitment = 2 := by omega
  have hCases : challenge = 0 ∨ challenge = 1 ∨ challenge = 2 := by omega
  have rCases : response = 0 ∨ response = 1 ∨ response = 2 := by omega
  rcases yCases with rfl | rfl | rfl <;>
    rcases cCases with rfl | rfl | rfl <;>
    rcases hCases with rfl | rfl | rfl <;>
    rcases rCases with rfl | rfl | rfl <;> rfl

end M0
