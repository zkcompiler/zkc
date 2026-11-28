module

public import Zkc.Frontend.Environment.Basic
public import Zkc.Frontend.Basic.CompileM
public import Zkc.Frontend.Static.Basic
public import Zkc.Frontend.Emit.Bindings
public import Zkc.Vocabulary.Standard

@[expose] public section
set_option autoImplicit false

/-!
# Scheme deployment planning (`Zkc.Frontend.Deploy.SuitePlan`)

Resolves a frontend `SchemeEntry` (or an explicit protocol instance + `SuiteSpec`) into a
validated `SchemePlan` capturing:
- the construction kind (`interactive`, `authored`, or `derived` with either a catalogue suite
  or the pure Core IR source suite `zkc::suites::HashChain<H, F>`),
- any `context` statement extensions (`context name: Type`),
- layout selection (`zkc::layout::canonical`) with `carry` and `recover` site directives,
- derived private-sample functions (`samples derived by`),
- retry bounds and target attempt sites (`retry N from sites.<name>`), and
- optional session tags and application context bytes.
-/

namespace Zkc.Frontend.Deploy

open Zkc.Vocabulary
open Zkc.Vocabulary.Project

/-- Concrete cryptographic suite resolved for a `.derived` scheme. -/
inductive SuiteSpec where
  | merlin3
  | poseidon2
  | schnorrSignature
  | cfrgShake128 (raw : Bool := false)
  | cfrgTurboShake128 (raw : Bool := false)
  | hashChain (hash : Zkc.Vocabulary.Hash) (field : Zkc.Vocabulary.Field)
  deriving DecidableEq, Repr

/-- Human-readable label for a resolved `SuiteSpec`. -/
def SuiteSpec.describe : SuiteSpec → String
  | .merlin3 => "suite.merlin3.bls12-381.fr64be/0"
  | .poseidon2 => "suite.poseidon2-duplex.koala-bear/0"
  | .schnorrSignature => "suite.schnorr-signature"
  | .cfrgShake128 false => "suite.cfrg.shake128"
  | .cfrgShake128 true => "suite.cfrg.shake128.raw"
  | .cfrgTurboShake128 false => "suite.cfrg.turboshake128"
  | .cfrgTurboShake128 true => "suite.cfrg.turboshake128.raw"
  | .hashChain hash field =>
      let hName := match hash with
        | .sha256 => "Sha256"
        | .keccak256 => "Keccak256"
        | .shake128 n => s!"Shake128<{n}>"
        | .shake256 n => s!"Shake256<{n}>"
      let fName := match field with
        | .koalaBear => "KoalaBear"
        | .koalaBear4 => "KoalaBear4"
        | .bls12381Fr => "Fr"
      s!"zkc::suites::HashChain<{hName}, {fName}>"

/-- Construction strategy for a planned scheme. -/
inductive ConstructionPlan where
  | interactive
  | authored
  | derived (suite : SuiteSpec) (sessionTag : Option (List Nat) := none)
  deriving DecidableEq, Repr

/-- A compact-layout recovery directive (`recover sites.<name> by <path>`). -/
structure RecoveryPlan where
  siteNames : List String
  recoveryPath : List String
  deriving DecidableEq, Repr

/-- Proof wire layout plan (`layout canonical: carry / recover`). -/
structure LayoutPlan where
  layoutName : String := "zkc::layout::canonical"
  carry : List (List String) := []
  recover : List RecoveryPlan := []
  deriving DecidableEq, Repr

/-- Complete frontend deployment plan lowered to `Core.Declaration` and helper IR definitions. -/
structure SchemePlan where
  name : String
  protocol : InstanceId
  construction : ConstructionPlan
  proverRole : Option String := none
  contexts : List (String × LinkedType) := []
  layout : Option LayoutPlan := none
  samplesPath : Option (List String) := none
  retry : Option (Nat × List String) := none
  application : List Nat := []

/-- Extract raw segment names from a syntax `Path`. -/
def pathSegmentNames : Syntax.Path → List String
  | .path _ segs => segs.toList.map fun (.segment _ name _) => name.text

/-- Extract static argument expressions from the last segment of a syntax `Path`. -/
def pathLastStaticArgs : Syntax.Path → List Syntax.StaticArg
  | .path _ segs =>
      match segs.back? with
      | some (.segment _ _ (some (.staticArgs _ args))) => args.toList
      | _ => []

/-- Evaluate a constant natural expression appearing in scheme lines (`retry`, `[T; N]`, `index<N>`). -/
partial def evalSyntaxNat : Syntax.Expr → Except String Nat
  | .number n => .ok n.value
  | .paren _ inner => evalSyntaxNat inner
  | .sum _ .add l r => return (← evalSyntaxNat l) + (← evalSyntaxNat r)
  | .sum _ .subtract l r => return (← evalSyntaxNat l) - (← evalSyntaxNat r)
  | .product _ .multiply l r => return (← evalSyntaxNat l) * (← evalSyntaxNat r)
  | .product _ .divide l r => do
      let b ← evalSyntaxNat r
      if b == 0 then .error "division by zero in scheme static size"
      else return (← evalSyntaxNat l) / b
  | .power _ b e => return (← evalSyntaxNat b) ^ (← evalSyntaxNat e)
  | _ => .error "unsupported non-constant expression in scheme line"

def resolveStdFieldName (names : List String) : Option Field :=
  match names.getLast? with
  | some "Fr" | some "Scalar" => some .bls12381Fr
  | some "KoalaBear" => some .koalaBear
  | some "KoalaBear4" => some .koalaBear4
  | _ => none

def resolveStdHashName (names : List String) : Option Zkc.Vocabulary.Hash :=
  match names.getLast? with
  | some "Sha256" => some .sha256
  | some "Keccak256" => some .keccak256
  | some "Shake128" => some (.shake128 32)
  | some "Shake256" => some (.shake256 64)
  | _ => none

/-- Evaluate a `Syntax.TypeExpr` occurring in a `scheme` `context` line into a `LinkedType`. -/
partial def evalSyntaxType : Syntax.TypeExpr → Except String LinkedType
  | .bool _ => .ok .bool
  | .nat _ => .ok .nat
  | .rational _ => .error "rational type is not permitted in deployed scheme context"
  | .index _ sizeExpr => return .fin (← evalSyntaxNat sizeExpr)
  | .nonzero _ inner => do
      match ← evalSyntaxType inner with
      | .nominal (.inl (.field f)) => .ok (.nominal (.inl (.nonzero f)))
      | _ => .error "unsupported nonzero type in scheme context"
  | .sequence _ elem size? => do
      let item ← evalSyntaxType elem
      match size? with
      | none => .ok (.seq item none)
      | some s => return .seq item (some (← evalSyntaxNat s))
  | .tuple _ fields => do
      let ts ← fields.toList.mapM fun (.tupleField _ _ t) => evalSyntaxType t
      .ok (.tuple (ts.foldr Core.Tys.cons .nil))
  | .path _ p =>
      let names := pathSegmentNames p
      match names.getLast? with
      | some "byte" => .ok (.fin 256)
      | some "bool" => .ok .bool
      | some "nat" => .ok .nat
      | some "G1" => .ok (.nominal (.inl (.group .g1)))
      | some "G2" => .ok (.nominal (.inl (.group .g2)))
      | some "GT" => .ok (.nominal (.inl (.group .gt)))
      | _ =>
          match resolveStdFieldName names with
          | some f => .ok (.nominal (.inl (.field f)))
          | none => .error s!"unsupported context type `{"::".intercalate names}`"

/-- Resolve a catalogue suite row string into a `SuiteSpec`. -/
def suiteSpecOfCatalogueRow (rowName : String) : Except String SuiteSpec :=
  match rowName with
  | "suite.merlin3.bls12-381.fr64be/0" => .ok .merlin3
  | "suite.poseidon2-duplex.koala-bear/0" => .ok .poseidon2
  | "suite.schnorr-signature" => .ok .schnorrSignature
  | "suite.cfrg.shake128" => .ok (.cfrgShake128 false)
  | "suite.cfrg.shake128.raw" => .ok (.cfrgShake128 true)
  | "suite.cfrg.turboshake128" => .ok (.cfrgTurboShake128 false)
  | "suite.cfrg.turboshake128.raw" => .ok (.cfrgTurboShake128 true)
  | other => .error s!"unknown catalogue suite row `{other}`"

def staticArgPathNames : Syntax.StaticArg → Except String (List String)
  | .term _ _ (.path _ p) => .ok (pathSegmentNames p)
  | _ => .error "expected path static argument in suite instantiation"

/-- Resolve the `SuiteSpec` of a `construction derived(S)` line, supporting both catalogue
suites and the pure Core IR source suite `zkc::suites::HashChain<H, F>`. -/
def resolveSuiteSpec (scheme : SchemeEntry) (path : Syntax.Path) : Except String SuiteSpec :=
  match scheme.suite with
  | .ok rowName => suiteSpecOfCatalogueRow rowName
  | .error _ =>
      let names := pathSegmentNames path
      match names.getLast? with
      | some "HashChain" =>
          match pathLastStaticArgs path with
          | [hArg, fArg] => do
              let hNames ← staticArgPathNames hArg
              let fNames ← staticArgPathNames fArg
              let some hash := resolveStdHashName hNames
                | .error s!"unsupported HashChain hash `{"::".intercalate hNames}`"
              let some field := resolveStdFieldName fNames
                | .error s!"unsupported HashChain field `{"::".intercalate fNames}`"
              .ok (.hashChain hash field)
          | _ => .error "HashChain requires two static arguments `<H, F>`"
      | some "Merlin3Bls12381" => .ok .merlin3
      | some "Poseidon2KoalaBear" => .ok .poseidon2
      | some "Suite" =>
          if names.contains "signature" then .ok .schnorrSignature
          else .error s!"unsupported suite `{"::".intercalate names}`"
      | _ => .error s!"unsupported source suite `{"::".intercalate names}`"

/-- Find a `SchemeEntry` in `state.results.schemes` by short name, qualified name, or (if empty
and unique) the sole scheme in the compiled package. -/
def findSchemeEntry (state : Compile.State) (schemeName : String) : Except String SchemeEntry := do
  let schemes := state.results.schemes
  if schemeName.isEmpty then
    match schemes.toList with
    | [only] => .ok only
    | [] => .error "no schemes declared in compiled files"
    | many =>
        let names := many.map (·.name)
        .error s!"multiple schemes declared ({", ".intercalate names}); specify one with --scheme"
  else
    let matches_ := schemes.filter fun entry =>
      let qual := Static.qualifiedName state.program entry.declaration
      entry.name == schemeName || qual == schemeName
    match matches_.toList with
    | [found] => .ok found
    | [] =>
        let avail := schemes.toList.map (·.name)
        .error s!"scheme `{schemeName}` not found (available: {", ".intercalate avail})"
    | many =>
        let quals := many.map fun e => Static.qualifiedName state.program e.declaration
        .error s!"ambiguous scheme `{schemeName}` ({", ".intercalate quals})"

/-- Build a validated `SchemePlan` from a frontend `SchemeEntry`. Fails closed on unsupported
scheme lines (`commit`, `pin`, `grind`, `offline`, `ideal`) or non-canonical layouts. -/
def planScheme (scheme : SchemeEntry) (sessionTag : Option (List Nat) := none)
    (application : List Nat := []) : Except String SchemePlan := do
  let mut construction? : Option ConstructionPlan := none
  let mut proverRole : Option String := none
  let mut contexts : List (String × LinkedType) := []
  let mut layout? : Option LayoutPlan := none
  let mut samplesPath : Option (List String) := none
  let mut retry? : Option (Nat × List String) := none
  for line in scheme.lines do
    match line with
    | .construction _ (.interactive _) =>
        if construction?.isSome then throw s!"scheme `{scheme.name}` has multiple construction lines"
        construction? := some .interactive
    | .construction _ (.authored _) =>
        if construction?.isSome then throw s!"scheme `{scheme.name}` has multiple construction lines"
        construction? := some .authored
    | .construction _ (.derived _ path) =>
        if construction?.isSome then throw s!"scheme `{scheme.name}` has multiple construction lines"
        let spec ← resolveSuiteSpec scheme path
        construction? := some (.derived spec sessionTag)
    | .prover _ roleName =>
        proverRole := some roleName.text
    | .context _ name tyExpr =>
        let ty ← evalSyntaxType tyExpr
        contexts := contexts ++ [(name.text, ty)]
    | .samples _ path =>
        samplesPath := some (pathSegmentNames path)
    | .retry _ countExpr siteRef =>
        let bound ← evalSyntaxNat countExpr
        retry? := some (bound, siteRef.names.toList.map (·.text))
    | .layout _ path adjusts? =>
        let lname := "::".intercalate (pathSegmentNames path)
        if !(lname == "canonical" || lname == "zkc::layout::canonical") then
          throw s!"unsupported layout `{lname}` (only `zkc::layout::canonical` is supported)"
        let mut carries : List (List String) := []
        let mut recovers : List RecoveryPlan := []
        for adj in adjusts?.getD #[] do
          match adj with
          | .carry _ siteRef =>
              carries := carries ++ [siteRef.names.toList.map (·.text)]
          | .recover _ siteRef recPath =>
              recovers := recovers ++ [{
                siteNames := siteRef.names.toList.map (·.text)
                recoveryPath := pathSegmentNames recPath
              }]
        layout? := some { layoutName := "zkc::layout::canonical", carry := carries, recover := recovers }
    | .offline .. => throw s!"scheme `{scheme.name}`: `offline` roles are not supported yet"
    | .ideal .. => throw s!"scheme `{scheme.name}`: `ideal` roles are not supported yet"
    | .commit .. => throw s!"scheme `{scheme.name}`: `commit` lines are not supported yet"
    | .pin .. => throw s!"scheme `{scheme.name}`: `pin` lines are not supported yet"
    | .grind .. => throw s!"scheme `{scheme.name}`: `grind` lines are not supported yet"
  let some construction := construction?
    | throw s!"scheme `{scheme.name}` has no `construction` line"
  let finalLayout :=
    match construction, layout? with
    | .interactive, some _ => layout?
    | .interactive, none => none
    | _, some l => some l
    | _, none => some { layoutName := "zkc::layout::canonical" }
  return {
    name := scheme.name
    protocol := scheme.protocol
    construction
    proverRole
    contexts
    layout := finalLayout
    samplesPath
    retry := retry?
    application
  }

end Zkc.Frontend.Deploy
