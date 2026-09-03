import M0.Decode

/-!
# K1 portable terms and typing

This file transcribes the closed first-order term carrier from Executable
Foundations Section 5.  A value type retains its exact domain coordinate while
making the nine finite root-schema forms explicit.  `termDatum` is the K1
preimage grammar; `termOfDatum` is deliberately strict about every record and
sequence shape.  The M2 runner first uses `M0.decode`, so elaboration starts
only after constitutional canonical decoding has succeeded.

`HasType` is a relation, not an inference shortcut.  It records the K1 rules
for literals, annotated de Bruijn variables, call-by-value binders and
branches, structural constructors, typed failures, primitives, and bounded
iteration.  Primitive ABIs remain exact-reference-qualified through the
`PrimitiveTyping` parameter: syntax never turns a diagnostic primitive name
into authority.
-/

namespace M0

mutual
  /-- An exact value-domain coordinate paired with one finite schema. -/
  inductive ValueType where
    | mk (domain : Datum) (schema : ValueSchema)
    deriving Repr

  /-- The nine K1 finite root-schema forms. -/
  inductive ValueSchema where
    | unit
    | bool
    | nat (maximum : Nat)
    | int (minimum maximum : Int)
    | bytes (minimumLength maximumLength : Nat)
    | symbol (maximumLength : Nat)
    | sequence (element : ValueType) (maximumLength : Nat)
    | record (fields : List (Nat × ValueType))
    | variant (cases : List (Nat × ValueType))
    deriving Repr
end

namespace ValueType

def domain : ValueType → Datum | .mk d _ => d
def schema : ValueType → ValueSchema | .mk _ s => s

end ValueType

/-- The exact semantic-failure declaration carrier plus its payload type. -/
structure FailureType where
  declaration : Datum
  payloadType : ValueType
  deriving Repr

/-- A typed semantic value. -/
structure TypedValue where
  valueType : ValueType
  datum : Datum
  deriving Repr

mutual
  /-- Sequence or natural-range iteration source. -/
  inductive IterationSource where
    | sequence (source : Term)
    | range (exclusiveBound : Term)
    deriving Repr

  /-- The exact fifteen-constructor K1 portable term carrier. -/
  inductive Term where
    | literal (value : TypedValue)
    | variable (index : Nat) (valueType : ValueType)
    | letE (bound body : Term)
    | recordConstruct (fields : List (Nat × Term))
    | project (record : Term) (ordinal : Nat)
    | inject (case : Nat) (payload : Term) (sumType : ValueType)
    | caseE (scrutinee : Term) (branches : List (Nat × Term))
    | sequenceConstruct (elementType : ValueType) (elements : List Term)
        (maximumLength : Nat)
    | sequenceLength (source : Term)
    | fail (failureType : FailureType) (payload : Term) (successType : ValueType)
    | strictIndex (source index : Term) (failureType : FailureType)
    | boundedAppend (source element : Term) (failureType : FailureType)
    | primitiveCall (primitive : Datum) (arguments : List Term)
    | boundedIterate (source : IterationSource) (initialState body : Term)
    | conditional (condition whenTrue whenFalse : Term)
    deriving Repr
end

/-- A canonical algorithm preimage after elaboration. -/
structure Algorithm where
  algorithmKind : Datum
  inputs : List ValueType
  term : Term
  directPrimitives : List Datum
  deriving Repr

def field? (fields : List (Nat × Datum)) (ordinal : Nat) : Option Datum :=
  (fields.find? fun field => field.1 == ordinal).map Prod.snd

def exactFields (datum : Datum) (ordinals : List Nat) : Option (List (Nat × Datum)) :=
  match datum with
  | .record fields => if fields.map Prod.fst == ordinals then some fields else none
  | _ => none

mutual
  /-- Elaborate one exact K1 value-type datum.  The domain coordinate is kept
  byte-for-byte as a datum; owner resolution remains outside this syntax pass. -/
  partial def valueTypeOfDatum (datum : Datum) : Option ValueType := do
    let fields ← exactFields datum [0, 1]
    let domain ← field? fields 0
    let schema ← schemaOfDatum (← field? fields 1)
    pure (.mk domain schema)

  partial def schemaOfDatum : Datum → Option ValueSchema
    | .variant 0 .unit => some .unit
    | .variant 1 .unit => some .bool
    | .variant 2 (.nat maximum) => some (.nat maximum)
    | .variant 3 (.record [(0, .int minimum), (1, .int maximum)]) =>
        some (.int minimum maximum)
    | .variant 4 (.record [(0, .nat minimum), (1, .nat maximum)]) =>
        some (.bytes minimum maximum)
    | .variant 5 (.nat maximum) => some (.symbol maximum)
    | .variant 6 (.record [(0, element), (1, .nat maximum)]) => do
        pure (.sequence (← valueTypeOfDatum element) maximum)
    | .variant 7 (.seq fields) => do
        pure (.record (← typeEntriesOfDatum fields))
    | .variant 8 (.seq cases) => do
        pure (.variant (← typeEntriesOfDatum cases))
    | _ => none

  partial def typeEntriesOfDatum : List Datum → Option (List (Nat × ValueType))
    | [] => some []
    | .record [(0, .nat ordinal), (1, valueType)] :: rest => do
        pure ((ordinal, ← valueTypeOfDatum valueType) :: (← typeEntriesOfDatum rest))
    | _ => none
end

mutual
  partial def valueTypeDatum : ValueType → Datum
    | .mk domain schema => .record [(0, domain), (1, schemaDatum' schema)]

  partial def schemaDatum' : ValueSchema → Datum
    | .unit => .variant 0 .unit
    | .bool => .variant 1 .unit
    | .nat maximum => .variant 2 (.nat maximum)
    | .int minimum maximum => .variant 3 (.record [(0, .int minimum), (1, .int maximum)])
    | .bytes minimum maximum =>
        .variant 4 (.record [(0, .nat minimum), (1, .nat maximum)])
    | .symbol maximum => .variant 5 (.nat maximum)
    | .sequence element maximum =>
        .variant 6 (.record [(0, valueTypeDatum element), (1, .nat maximum)])
    | .record fields => .variant 7 (.seq (typeEntriesDatum fields))
    | .variant cases => .variant 8 (.seq (typeEntriesDatum cases))

  partial def typeEntriesDatum (entries : List (Nat × ValueType)) : List Datum :=
    entries.map fun (ordinal, valueType) =>
      .record [(0, .nat ordinal), (1, valueTypeDatum valueType)]
end

def failureTypeOfDatum (datum : Datum) : Option FailureType := do
  let fields ← exactFields datum [0, 1]
  pure { declaration := ← field? fields 0, payloadType := ← valueTypeOfDatum (← field? fields 1) }

def failureTypeDatum (failure : FailureType) : Datum :=
  .record [(0, failure.declaration), (1, valueTypeDatum failure.payloadType)]

mutual
  /-- Strict elaboration of all fifteen term tags. -/
  partial def termOfDatum : Datum → Option Term
    | .variant 0 (.record [(0, valueType), (1, value)]) => do
        pure (.literal { valueType := ← valueTypeOfDatum valueType, datum := value })
    | .variant 1 (.record [(0, .nat index), (1, valueType)]) => do
        pure (.variable index (← valueTypeOfDatum valueType))
    | .variant 2 (.record [(0, bound), (1, body)]) => do
        pure (.letE (← termOfDatum bound) (← termOfDatum body))
    | .variant 3 (.seq fields) => .recordConstruct <$> termEntriesOfDatum fields
    | .variant 4 (.record [(0, record), (1, .nat ordinal)]) => do
        pure (.project (← termOfDatum record) ordinal)
    | .variant 5 (.record [(0, .nat case), (1, payload), (2, sumType)]) => do
        pure (.inject case (← termOfDatum payload) (← valueTypeOfDatum sumType))
    | .variant 6 (.record [(0, scrutinee), (1, .seq branches)]) => do
        pure (.caseE (← termOfDatum scrutinee) (← termEntriesOfDatum branches))
    | .variant 7 (.record [(0, elementType), (1, .seq elements), (2, .nat maximum)]) => do
        pure (.sequenceConstruct (← valueTypeOfDatum elementType)
          (← termsOfDatum elements) maximum)
    | .variant 8 source => .sequenceLength <$> termOfDatum source
    | .variant 9 (.record [(0, failureType), (1, payload), (2, successType)]) => do
        pure (.fail (← failureTypeOfDatum failureType) (← termOfDatum payload)
          (← valueTypeOfDatum successType))
    | .variant 10 (.record [(0, source), (1, index), (2, failureType)]) => do
        pure (.strictIndex (← termOfDatum source) (← termOfDatum index)
          (← failureTypeOfDatum failureType))
    | .variant 11 (.record [(0, source), (1, element), (2, failureType)]) => do
        pure (.boundedAppend (← termOfDatum source) (← termOfDatum element)
          (← failureTypeOfDatum failureType))
    | .variant 12 (.record [(0, primitive), (1, .seq arguments)]) => do
        pure (.primitiveCall primitive (← termsOfDatum arguments))
    | .variant 13 (.record [(0, source), (1, initialState), (2, body)]) => do
        let elaboratedSource ← match source with
          | .variant 0 sequence => .sequence <$> termOfDatum sequence
          | .variant 1 bound => .range <$> termOfDatum bound
          | _ => none
        pure (.boundedIterate elaboratedSource (← termOfDatum initialState) (← termOfDatum body))
    | .variant 14 (.record [(0, condition), (1, whenTrue), (2, whenFalse)]) => do
        pure (.conditional (← termOfDatum condition) (← termOfDatum whenTrue)
          (← termOfDatum whenFalse))
    | _ => none

  partial def termsOfDatum : List Datum → Option (List Term)
    | [] => some []
    | term :: rest => do pure ((← termOfDatum term) :: (← termsOfDatum rest))

  partial def termEntriesOfDatum : List Datum → Option (List (Nat × Term))
    | [] => some []
    | .record [(0, .nat ordinal), (1, term)] :: rest => do
        pure ((ordinal, ← termOfDatum term) :: (← termEntriesOfDatum rest))
    | _ => none
end

mutual
  partial def termDatum : Term → Datum
    | .literal value =>
        .variant 0 (.record [(0, valueTypeDatum value.valueType), (1, value.datum)])
    | .variable index valueType =>
        .variant 1 (.record [(0, .nat index), (1, valueTypeDatum valueType)])
    | .letE bound body => .variant 2 (.record [(0, termDatum bound), (1, termDatum body)])
    | .recordConstruct fields => .variant 3 (.seq (termEntriesDatum fields))
    | .project record ordinal =>
        .variant 4 (.record [(0, termDatum record), (1, .nat ordinal)])
    | .inject case payload sumType =>
        .variant 5 (.record [(0, .nat case), (1, termDatum payload),
          (2, valueTypeDatum sumType)])
    | .caseE scrutinee branches =>
        .variant 6 (.record [(0, termDatum scrutinee), (1, .seq (termEntriesDatum branches))])
    | .sequenceConstruct elementType elements maximum =>
        .variant 7 (.record [(0, valueTypeDatum elementType),
          (1, .seq (elements.map termDatum)), (2, .nat maximum)])
    | .sequenceLength source => .variant 8 (termDatum source)
    | .fail failureType payload successType =>
        .variant 9 (.record [(0, failureTypeDatum failureType), (1, termDatum payload),
          (2, valueTypeDatum successType)])
    | .strictIndex source index failureType =>
        .variant 10 (.record [(0, termDatum source), (1, termDatum index),
          (2, failureTypeDatum failureType)])
    | .boundedAppend source element failureType =>
        .variant 11 (.record [(0, termDatum source), (1, termDatum element),
          (2, failureTypeDatum failureType)])
    | .primitiveCall primitive arguments =>
        .variant 12 (.record [(0, primitive), (1, .seq (arguments.map termDatum))])
    | .boundedIterate source initialState body =>
        let sourceDatum := match source with
          | .sequence sequence => .variant 0 (termDatum sequence)
          | .range bound => .variant 1 (termDatum bound)
        .variant 13 (.record [(0, sourceDatum), (1, termDatum initialState),
          (2, termDatum body)])
    | .conditional condition whenTrue whenFalse =>
        .variant 14 (.record [(0, termDatum condition), (1, termDatum whenTrue),
          (2, termDatum whenFalse)])

  partial def termEntriesDatum (entries : List (Nat × Term)) : List Datum :=
    entries.map fun (ordinal, term) => .record [(0, .nat ordinal), (1, termDatum term)]
end

def algorithmOfDatum (datum : Datum) : Option Algorithm := do
  let fields ← exactFields datum [0, 1, 2, 3]
  let .seq inputData ← field? fields 1 | none
  let .seq primitives ← field? fields 3 | none
  let inputs ← inputData.mapM valueTypeOfDatum
  pure {
    algorithmKind := ← field? fields 0
    inputs
    term := ← termOfDatum (← field? fields 2)
    directPrimitives := primitives
  }

def algorithmDatum (algorithm : Algorithm) : Datum :=
  .record [
    (0, algorithm.algorithmKind),
    (1, .seq (algorithm.inputs.map valueTypeDatum)),
    (2, termDatum algorithm.term),
    (3, .seq algorithm.directPrimitives)
  ]

/-- The nine primitive ABI/type-rule families declared by the K1 fixture
module.  Concrete references are resolved before selecting one of these rules. -/
inductive PrimitiveRule where
  | sha2_256 | bytesConcat | u64ToBE | bytesFirstU64BE | natLt
  | natModPositive | bytesTake | fixtureReverse | fixturePrefix27
  deriving Repr, DecidableEq

def declaredPrimitiveABIs : List (String × Nat × PrimitiveRule) := [
  ("sha2-256", 1, .sha2_256),
  ("bytes.concat", 1, .bytesConcat),
  ("u64.to-be", 1, .u64ToBE),
  ("bytes.first-u64-be", 1, .bytesFirstU64BE),
  ("nat.lt", 1, .natLt),
  ("nat.mod-positive", 1, .natModPositive),
  ("bytes.take", 1, .bytesTake),
  ("fixture.bytes.reverse", 1, .fixtureReverse),
  ("fixture.bytes.prefix-27", 1, .fixturePrefix27)
]

/-- An exact-reference-qualified primitive ABI judgment. -/
abbrev PrimitiveTyping := Datum → List ValueType → ValueType → List FailureType → Prop

/-- The domain carrier has the root-value-domain ordinal fixed by its schema
constructor.  The exact owner bytes are intentionally retained, not inferred. -/
def IsRootDomain : Datum → Nat → Prop
  | .variant 0 (.record [(0, .bytes _), (1, .symbol name), (2, .nat actual)]), expected =>
      name = [102, 111, 117, 110, 100, 97, 116, 105, 111, 110, 46, 114, 111, 111,
        116, 45, 118, 97, 108, 117, 101, 45, 100, 111, 109, 97, 105, 110] ∧
      actual = expected
  | _, _ => False

mutual
  /-- The relational K1 typing judgment.  Lists in the conclusion preserve
  left-to-right child failures; the owner model canonicalizes that list by exact
  failure encoding after inference. -/
  inductive HasType (primitive : PrimitiveTyping) :
      List ValueType → Term → ValueType → List FailureType → Prop where
    | literal : HasType primitive env (.literal ⟨ty, value⟩) ty []
    | variable (lookup : env[index]? = some ty) :
        HasType primitive env (.variable index ty) ty []
    | letE (bound : HasType primitive env b boundTy boundFailures)
        (body : HasType primitive (boundTy :: env) t bodyTy bodyFailures) :
        HasType primitive env (.letE b t) bodyTy (boundFailures ++ bodyFailures)
    | recordConstruct (root : IsRootDomain domain 7)
        (children : FieldsHaveType primitive env fields fieldTypes failures) :
        HasType primitive env (.recordConstruct fields) (.mk domain (.record fieldTypes)) failures
    | project (record : HasType primitive env source (.mk domain (.record fields)) failures)
        (present : fields.find? (fun field => field.1 == ordinal) = some (ordinal, output)) :
        HasType primitive env (.project source ordinal) output failures
    | inject (payload : HasType primitive env term payloadTy failures)
        (present : cases.find? (fun entry => entry.1 == case) = some (case, payloadTy)) :
        HasType primitive env (.inject case term (.mk domain (.variant cases)))
          (.mk domain (.variant cases)) failures
    | caseE (scrutinee : HasType primitive env term (.mk domain (.variant cases)) scrutineeFailures)
        (branches : BranchesHaveType primitive env branchTerms cases output branchFailures) :
        HasType primitive env (.caseE term branchTerms) output
          (scrutineeFailures ++ branchFailures)
    | sequenceConstruct (root : IsRootDomain domain 6)
        (length : terms.length ≤ maximum)
        (elements : TermsHaveType primitive env terms
          (List.replicate terms.length elementTy) failures) :
        HasType primitive env (.sequenceConstruct elementTy terms maximum)
          (.mk domain (.sequence elementTy maximum)) failures
    | sequenceLength (source : HasType primitive env term
        (.mk sequenceDomain (.sequence elementTy maximum)) failures)
        (naturalDomain : IsRootDomain natDomain 2) :
        HasType primitive env (.sequenceLength term) (.mk natDomain (.nat maximum)) failures
    | fail (failure : FailureType)
        (payload : HasType primitive env term failure.payloadType failures) :
        HasType primitive env (.fail failure term successTy) successTy (failures ++ [failure])
    | strictIndex (failure : FailureType) (source : HasType primitive env sourceTerm
          (.mk sequenceDomain (.sequence elementTy maximum)) sourceFailures)
        (index : HasType primitive env indexTerm indexTy indexFailures)
        (natural : indexTy.schema = .nat indexMaximum)
        (payload : failure.payloadType = indexTy) :
        HasType primitive env (.strictIndex sourceTerm indexTerm failure) elementTy
          (sourceFailures ++ indexFailures ++ [failure])
    | boundedAppend (failure : FailureType) (source : HasType primitive env sourceTerm
          (.mk sequenceDomain (.sequence elementTy maximum)) sourceFailures)
        (element : HasType primitive env elementTerm elementTy elementFailures) :
        HasType primitive env (.boundedAppend sourceTerm elementTerm failure)
          (.mk sequenceDomain (.sequence elementTy maximum))
          (sourceFailures ++ elementFailures ++ [failure])
    | primitiveCall
        (arguments : TermsHaveType primitive env terms argumentTypes argumentFailures)
        (abi : primitive reference argumentTypes output primitiveFailures) :
        HasType primitive env (.primitiveCall reference terms) output
          (argumentFailures ++ primitiveFailures)
    | boundedIterateSequence
        (source : HasType primitive env sourceTerm
          (.mk sequenceDomain (.sequence elementTy maximum)) sourceFailures)
        (initial : HasType primitive env initialTerm stateTy initialFailures)
        (body : HasType primitive (indexTy :: elementTy :: stateTy :: env)
          bodyTerm resultTy bodyFailures) :
        HasType primitive env (.boundedIterate (.sequence sourceTerm) initialTerm bodyTerm)
          resultTy (sourceFailures ++ initialFailures ++ bodyFailures)
    | boundedIterateRange
        (source : HasType primitive env sourceTerm (.mk natDomain (.nat maximum)) sourceFailures)
        (initial : HasType primitive env initialTerm stateTy initialFailures)
        (body : HasType primitive (indexTy :: indexTy :: stateTy :: env)
          bodyTerm resultTy bodyFailures) :
        HasType primitive env (.boundedIterate (.range sourceTerm) initialTerm bodyTerm)
          resultTy (sourceFailures ++ initialFailures ++ bodyFailures)
    | conditional (condition : HasType primitive env conditionTerm
          (.mk boolDomain .bool) conditionFailures)
        (whenTrue : HasType primitive env trueTerm output trueFailures)
        (whenFalse : HasType primitive env falseTerm output falseFailures) :
        HasType primitive env (.conditional conditionTerm trueTerm falseTerm) output
          (conditionFailures ++ trueFailures ++ falseFailures)

  inductive TermsHaveType (primitive : PrimitiveTyping) :
      List ValueType → List Term → List ValueType → List FailureType → Prop where
    | nil : TermsHaveType primitive env [] [] []
    | cons (head : HasType primitive env term ty headFailures)
        (tail : TermsHaveType primitive env terms types tailFailures) :
        TermsHaveType primitive env (term :: terms) (ty :: types)
          (headFailures ++ tailFailures)

  inductive FieldsHaveType (primitive : PrimitiveTyping) :
      List ValueType → List (Nat × Term) → List (Nat × ValueType) → List FailureType → Prop where
    | nil : FieldsHaveType primitive env [] [] []
    | cons (head : HasType primitive env term ty headFailures)
        (tail : FieldsHaveType primitive env fields types tailFailures) :
        FieldsHaveType primitive env ((ordinal, term) :: fields) ((ordinal, ty) :: types)
          (headFailures ++ tailFailures)

  inductive BranchesHaveType (primitive : PrimitiveTyping) :
      List ValueType → List (Nat × Term) → List (Nat × ValueType) →
        ValueType → List FailureType → Prop where
    | one (branch : HasType primitive (payloadTy :: env) term output failures) :
        BranchesHaveType primitive env [(case, term)] [(case, payloadTy)] output failures
    | cons (head : HasType primitive (payloadTy :: env) term output headFailures)
        (tail : BranchesHaveType primitive env branches cases output tailFailures) :
        BranchesHaveType primitive env ((case, term) :: branches) ((case, payloadTy) :: cases)
          output (headFailures ++ tailFailures)
end

end M0
