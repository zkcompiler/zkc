import M0.Decode

/-!
# The admitted D1 Core fragment used by graph construction

This module decodes the fourteen tables of the exact D1 Core-domain body and
the dependency-bearing parts of its used semantic-module declarations.  It
deliberately retains only coordinates that Section 11 consumes.  Opaque type,
algorithm, contract, and declaration-reference bodies are still required to
occupy their exact fields, but are not reinterpreted here: D1 admission has
already authenticated them.

Nothing in this file is normative.  The five canonical Core bodies are inputs
to a bounded differential experiment.
-/

namespace M0

def recordValues : Datum → Option (List Datum)
  | .record fs => go 0 fs
  | _ => none
where
  go : Nat → List (Nat × Datum) → Option (List Datum)
    | _, [] => some []
    | expected, (ordinal, value) :: rest => do
      if ordinal != expected then none else
      pure (value :: (← go (expected + 1) rest))

def seqValues : Datum → Option (List Datum)
  | .seq xs => some xs
  | _ => none

def natValue : Datum → Option Nat
  | .nat n => some n
  | _ => none

def bytesValue : Datum → Option (List Octet)
  | .bytes bs => some bs
  | _ => none

def variantValue : Datum → Option (Nat × Datum)
  | .variant tag payload => some (tag, payload)
  | _ => none

def unitPayload : Datum → Bool
  | .unit => true
  | _ => false

def mapOption (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do pure ((← f x) :: (← mapOption f xs))

def natsOfSeq (d : Datum) : Option (List Nat) := do
  mapOption natValue (← seqValues d)

inductive ValueRef where
  | publicInput (ordinal : Nat)
  | verifierPrivateInput (ordinal : Nat)
  | constant (ordinal : Nat)
  | derived (ordinal : Nat)
  | occurrenceOutput (occurrence output : Nat)
  deriving DecidableEq, Repr

def valueRefOfDatum : Datum → Option ValueRef
  | .variant 0 (.nat n) => some (.publicInput n)
  | .variant 1 (.nat n) => some (.verifierPrivateInput n)
  | .variant 2 (.nat n) => some (.constant n)
  | .variant 3 (.nat n) => some (.derived n)
  | .variant 4 body => do
      match ← recordValues body with
      | [.nat occurrence, .nat output] => pure (.occurrenceOutput occurrence output)
      | _ => none
  | _ => none

def valueRefsOfSeq (d : Datum) : Option (List ValueRef) := do
  mapOption valueRefOfDatum (← seqValues d)

structure DerivedDecl where
  inputs : List ValueRef
  deriving Repr

def derivedDeclOfDatum (d : Datum) : Option DerivedDecl := do
  match ← recordValues d with
  | [.bytes _, .bytes _, inputs, _] => pure { inputs := ← valueRefsOfSeq inputs }
  | _ => none

structure ScopeDecl where
  parent : Option Nat
  deriving Repr

def optionalNat : Datum → Option (Option Nat)
  | .variant 0 payload => if unitPayload payload then some none else none
  | .variant 1 (.nat n) => some (some n)
  | _ => none

def scopeDeclOfDatum (d : Datum) : Option ScopeDecl := do
  match ← recordValues d with
  | [parent, opening] =>
      let parent ← optionalNat parent
      let _ ← optionalNat opening
      pure { parent }
  | _ => none

structure BindingDecl where
  scope : Nat
  value : ValueRef
  deriving Repr

def bindingDeclOfDatum (d : Datum) : Option BindingDecl := do
  match ← recordValues d with
  | [.nat scope, .variant _ _, value] => pure { scope, value := ← valueRefOfDatum value }
  | _ => none

structure ChallengeDecl where
  conditions : List ValueRef
  priors : List Nat
  deriving Repr

def challengeDeclOfDatum (d : Datum) : Option ChallengeDecl := do
  match ← recordValues d with
  | [.nat _, _, _, _, correlation, .variant _ _, conditions] =>
      let priors ← match correlation with
        | .variant 0 payload => if unitPayload payload then some [] else none
        | .variant 1 joint => do
            match ← recordValues joint with
            | [_, .nat _, priorRows] => natsOfSeq priorRows
            | _ => none
        | _ => none
      pure { conditions := ← valueRefsOfSeq conditions, priors }
  | _ => none

inductive OracleOrigin where
  | initial
  | prover
  deriving DecidableEq, Repr

inductive OracleMode where
  | fullCanonical
  | publicBinding
  | logicalAccess
  deriving DecidableEq, Repr

structure OracleDecl where
  origin : OracleOrigin
  mode : OracleMode
  deriving Repr

def oracleDeclOfDatum (d : Datum) : Option OracleDecl := do
  match ← recordValues d with
  | [.nat _, .variant originTag originPayload, _, _, .nat _, .variant modeTag _] =>
      if !unitPayload originPayload then none else
      let origin ← match originTag with
        | 0 => some .initial
        | 1 => some .prover
        | _ => none
      let mode ← match modeTag with
        | 0 => some .fullCanonical
        | 1 => some .publicBinding
        | 2 => some .logicalAccess
        | _ => none
      pure { origin, mode }
  | _ => none

structure CheckDecl where
  inputs : List ValueRef
  deriving Repr

def checkDeclOfDatum (d : Datum) : Option CheckDecl := do
  match ← recordValues d with
  | [.bytes _, .bytes _, inputs] => pure { inputs := ← valueRefsOfSeq inputs }
  | _ => none

inductive ClaimSource where
  | initialBinding (binding : Nat)
  | reductionOutput (reduction output : Nat)
  deriving DecidableEq, Repr

structure ClaimDecl where
  source : ClaimSource
  deriving Repr

def claimDeclOfDatum (d : Datum) : Option ClaimDecl := do
  match ← recordValues d with
  | [_, .nat _, .variant _ _, source] =>
      let source ← match source with
        | .variant 0 (.nat binding) => some (.initialBinding binding)
        | .variant 1 body => do
            match ← recordValues body with
            | [.nat reduction, .nat output] => pure (.reductionOutput reduction output)
            | _ => none
        | _ => none
      pure { source }
  | _ => none

structure ReductionDecl where
  claims : List Nat
  sideInputs : List ValueRef
  challenges : List Nat
  publications : List Nat
  deriving Repr

def publicationRefOfDatum (d : Datum) : Option Nat := do
  match ← recordValues d with
  | [.nat publication, optionalChallenge] =>
      let _ ← optionalNat optionalChallenge
      pure publication
  | _ => none

def reductionDeclOfDatum (d : Datum) : Option ReductionDecl := do
  match ← recordValues d with
  | [_, .nat _, claims, sideInputs, challenges, publications, outputContracts] =>
      let _ ← seqValues outputContracts
      pure {
        claims := ← natsOfSeq claims
        sideInputs := ← valueRefsOfSeq sideInputs
        challenges := ← natsOfSeq challenges
        publications := ← mapOption publicationRefOfDatum (← seqValues publications)
      }
  | _ => none

inductive Verdict where
  | accept
  | reject
  | abort
  deriving DecidableEq, Repr

structure TerminalDecl where
  verdict : Verdict
  publicOutputs : List ValueRef
  checks : List Nat
  reductions : List Nat
  claims : List Nat
  deriving Repr

def terminalDeclOfDatum (d : Datum) : Option TerminalDecl := do
  match ← recordValues d with
  | [.variant verdictTag payload, outputs, checks, reductions, claims] =>
      if !unitPayload payload then none else
      let verdict ← match verdictTag with
        | 0 => some .accept
        | 1 => some .reject
        | 2 => some .abort
        | _ => none
      pure {
        verdict
        publicOutputs := ← valueRefsOfSeq outputs
        checks := ← natsOfSeq checks
        reductions := ← natsOfSeq reductions
        claims := ← natsOfSeq claims
      }
  | _ => none

inductive Guard where
  | always
  | evaluate (inputs : List ValueRef)
  deriving Repr

def guardOfDatum : Datum → Option Guard
  | .variant 0 payload => if unitPayload payload then some .always else none
  | .variant 1 body => do
      match ← recordValues body with
      | [.bytes _, .bytes _, inputs] => pure (.evaluate (← valueRefsOfSeq inputs))
      | _ => none
  | _ => none

inductive OracleVisibility where
  | publicView
  | verifierOnlyView
  deriving DecidableEq, Repr

inductive Effect where
  | proverMessage
  | verifierMessage (inputs : List ValueRef)
  | challenge (reference : Nat)
  | check (reference : Nat)
  | reduction (reference : Nat)
  | terminal (reference : Nat)
  | oraclePublish (oracle : Nat)
  | oracleQuery (oracle : Nat) (index : ValueRef) (visibility : OracleVisibility)
  | oracleAnswer (query : Nat)
  | module (moduleRef : List Octet) (declaration : Nat) (payloadInputs : List ValueRef)
  deriving Repr

def moduleDeclarationCoordinate (d : Datum) : Option (List Octet × Nat) := do
  match d with
  | .variant 1 body =>
      match ← recordValues body with
      | [.bytes moduleRef, .symbol _, .nat ordinal] => pure (moduleRef, ordinal)
      | _ => none
  | _ => none

def effectOfDatum : Datum → Option Effect
  | .variant 0 body => do
      match ← recordValues body with
      | [_, _] => pure .proverMessage
      | _ => none
  | .variant 1 body => do
      match ← recordValues body with
      | [_, .bytes _, .bytes _, inputs, _] => pure (.verifierMessage (← valueRefsOfSeq inputs))
      | _ => none
  | .variant 2 (.nat reference) => some (.challenge reference)
  | .variant 3 (.nat reference) => some (.check reference)
  | .variant 4 (.nat reference) => some (.reduction reference)
  | .variant 5 (.nat reference) => some (.terminal reference)
  | .variant 6 (.variant 0 (.nat oracle)) => some (.oraclePublish oracle)
  | .variant 6 (.variant 1 body) => do
      match ← recordValues body with
      | [.nat oracle, index, .variant visibilityTag payload] =>
          if !unitPayload payload then none else
          let visibility ← match visibilityTag with
            | 0 => some .publicView
            | 1 => some .verifierOnlyView
            | _ => none
          pure (.oracleQuery oracle (← valueRefOfDatum index) visibility)
      | _ => none
  | .variant 6 (.variant 2 (.nat query)) => some (.oracleAnswer query)
  | .variant 7 body => do
      match ← recordValues body with
      | [.bytes moduleRef, declaration, payload] =>
          let (declModule, ordinal) ← moduleDeclarationCoordinate declaration
          if declModule != moduleRef then none else
          match ← recordValues payload with
          | [inputs] => pure (.module moduleRef ordinal (← valueRefsOfSeq inputs))
          | _ => none
      | _ => none
  | _ => none

structure OccurrenceDecl where
  scope : Nat
  guard : Guard
  effect : Effect
  deriving Repr

def occurrenceDeclOfDatum (d : Datum) : Option OccurrenceDecl := do
  match ← recordValues d with
  | [.nat scope, guard, effect] => pure {
      scope, guard := ← guardOfDatum guard, effect := ← effectOfDatum effect
    }
  | _ => none

structure Core where
  usedModules : List (List Octet)
  publicInputCount : Nat
  verifierPrivateInputCount : Nat
  constantCount : Nat
  derived : List DerivedDecl
  scopes : List ScopeDecl
  bindings : List BindingDecl
  challenges : List ChallengeDecl
  oracles : List OracleDecl
  checks : List CheckDecl
  claims : List ClaimDecl
  reductions : List ReductionDecl
  terminals : List TerminalDecl
  occurrences : List OccurrenceDecl
  deriving Repr

def opaqueRows (arity : Nat) (d : Datum) : Option Nat := do
  let rows ← seqValues d
  if rows.all fun row => (recordValues row).any fun values => values.length = arity then
    pure rows.length
  else none

def coreOfDatum (d : Datum) : Option Core := do
  match ← recordValues d with
  | [usedModules, publicInputs, privateInputs, constants, derived, scopes, bindings,
      challenges, oracles, checks, claims, reductions, terminals, occurrences] =>
      pure {
        usedModules := ← mapOption bytesValue (← seqValues usedModules)
        publicInputCount := ← opaqueRows 1 publicInputs
        verifierPrivateInputCount := ← opaqueRows 1 privateInputs
        constantCount := ← opaqueRows 2 constants
        derived := ← mapOption derivedDeclOfDatum (← seqValues derived)
        scopes := ← mapOption scopeDeclOfDatum (← seqValues scopes)
        bindings := ← mapOption bindingDeclOfDatum (← seqValues bindings)
        challenges := ← mapOption challengeDeclOfDatum (← seqValues challenges)
        oracles := ← mapOption oracleDeclOfDatum (← seqValues oracles)
        checks := ← mapOption checkDeclOfDatum (← seqValues checks)
        claims := ← mapOption claimDeclOfDatum (← seqValues claims)
        reductions := ← mapOption reductionDeclOfDatum (← seqValues reductions)
        terminals := ← mapOption terminalDeclOfDatum (← seqValues terminals)
        occurrences := ← mapOption occurrenceDeclOfDatum (← seqValues occurrences)
      }
  | _ => none

inductive ModuleDecision where
  | noDecision
  | proverDecision
  | proverPublication
  deriving DecidableEq, Repr

inductive ModuleVisibility where
  | internal
  | proverOnly
  | verifierOnly
  | publicView
  deriving DecidableEq, Repr

inductive ModuleOutputTransfer where
  | deterministic
  | proverPublication
  | proverInternal
  deriving DecidableEq, Repr

inductive ModuleDependency where
  | activity
  | effect
  | payloadInput (ordinal : Nat)
  | priorOutput (ordinal : Nat)
  deriving DecidableEq, Repr

structure ModuleOutput where
  visibility : ModuleVisibility
  transfer : ModuleOutputTransfer
  dependencies : List ModuleDependency
  acceptanceRelevant : Bool
  deriving Repr

structure ModuleControl where
  dependencies : List ModuleDependency
  acceptanceRelevant : Bool
  deriving Repr

structure ModuleDecl where
  moduleRef : List Octet
  ordinal : Nat
  decision : ModuleDecision
  outputs : List ModuleOutput
  controls : List ModuleControl
  deriving Repr

def moduleBool : Datum → Option Bool
  | .variant 0 payload => if unitPayload payload then some false else none
  | .variant 1 payload => if unitPayload payload then some true else none
  | _ => none

def moduleDependencyOfDatum : Datum → Option ModuleDependency
  | .variant 0 payload => if unitPayload payload then some .activity else none
  | .variant 1 payload => if unitPayload payload then some .effect else none
  | .variant 2 (.nat ordinal) => some (.payloadInput ordinal)
  | .variant 3 (.nat ordinal) => some (.priorOutput ordinal)
  | _ => none

def moduleDependenciesOfSeq (d : Datum) : Option (List ModuleDependency) := do
  mapOption moduleDependencyOfDatum (← seqValues d)

def moduleOutputOfDatum (d : Datum) : Option ModuleOutput := do
  match ← recordValues d with
  | [_, .variant visibilityTag _, transfer, dependencies, acceptance] =>
      let visibility ← match visibilityTag with
        | 0 => some .internal
        | 1 => some .proverOnly
        | 2 => some .verifierOnly
        | 3 => some .publicView
        | _ => none
      let transfer ← match transfer with
        | .variant 0 body => do
            match ← recordValues body with
            | [.bytes _, .bytes _] => pure .deterministic
            | _ => none
        | .variant 1 payload => if unitPayload payload then some .proverPublication else none
        | .variant 2 payload => if unitPayload payload then some .proverInternal else none
        | _ => none
      pure {
        visibility, transfer
        dependencies := ← moduleDependenciesOfSeq dependencies
        acceptanceRelevant := ← moduleBool acceptance
      }
  | _ => none

def moduleControlOfDatum (d : Datum) : Option ModuleControl := do
  match ← recordValues d with
  | [dependencies, acceptance] => pure {
      dependencies := ← moduleDependenciesOfSeq dependencies
      acceptanceRelevant := ← moduleBool acceptance
    }
  | _ => none

def moduleDeclOfDatum (moduleRef : List Octet) (ordinal : Nat) (d : Datum) : Option ModuleDecl := do
  match ← recordValues d with
  | [.symbol _, .symbol _, .variant decisionTag _, payloadTypes, outputs, controls,
      _, .symbol _, .symbol _, .symbol _, .nat _] =>
      let _ ← seqValues payloadTypes
      let decision ← match decisionTag with
        | 0 => some .noDecision
        | 1 => some .proverDecision
        | 2 => some .proverPublication
        | _ => none
      pure {
        moduleRef, ordinal, decision
        outputs := ← mapOption moduleOutputOfDatum (← seqValues outputs)
        controls := ← mapOption moduleControlOfDatum (← seqValues controls)
      }
  | _ => none

end M0
