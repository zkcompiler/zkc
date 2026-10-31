import Lean

/-! Kernel assumption and declaration dependency checks for package-owned code.
Module ownership, rather than declaration spelling, also covers private helpers,
generated declarations and declarations added to an existing namespace.
Each stored module version is inspected: Lean can realize equivalent equation
proofs lazily in several modules, so merged ownership and proof bodies alone
do not reliably identify dependency provenance.
-/

set_option autoImplicit false

/-! Statement facts, shared with the declaration-record emitter
(`checks/DeclarationRecords.lean`).

- Two statement hashes. The structural hash of an elaborated type ignores binder
  names, binder information and metadata, and does not unfold definitions, so a
  statement keeps its hash when only the bodies of the definitions it mentions
  change. The explicit hash also omits the implicit and instance arguments of
  applied constants, as a statement's text does: a declaration whose structural
  hash changes while its explicit hash stays has the same text, and only an
  inferred argument of a constant it mentions changed. Binder types of the
  statement itself are always hashed in full. Equal hashes are regression
  evidence, not semantic preservation.
- The premise telescope of a statement: every leading binder, with its binder
  information, whether it is a proof of a proposition, and the head constant of
  that proposition after its own leading binders.
- Proposition-valued constants: definitions, inductive types and classes whose
  type ends in `Prop` after its leading binders. -/

namespace ZkcTools.Statements
open Lean Meta

/-- Structural hash of an expression, ignoring binder names, binder
information and metadata. Constants are hashed by name and universe levels. -/
partial def structuralHash : Expr → UInt64
  | .bvar index => mixHash 1 (hash index)
  | .fvar id => mixHash 2 (hash id.name)
  | .mvar id => mixHash 3 (hash id.name)
  | .sort level => mixHash 4 (hash level)
  | .const name levels => mixHash 5 (mixHash (hash name) (hash levels))
  | .app function argument => mixHash 6 (mixHash (structuralHash function) (structuralHash argument))
  | .lam _ type body _ => mixHash 7 (mixHash (structuralHash type) (structuralHash body))
  | .forallE _ type body _ => mixHash 8 (mixHash (structuralHash type) (structuralHash body))
  | .letE _ type value body _ =>
      mixHash 9 (mixHash (structuralHash type) (mixHash (structuralHash value) (structuralHash body)))
  | .lit (.natVal value) => mixHash 10 (hash value)
  | .lit (.strVal value) => mixHash 11 (hash value)
  | .mdata _ inner => structuralHash inner
  | .proj owner index inner => mixHash 12 (mixHash (hash owner) (mixHash (hash index) (structuralHash inner)))

/-- Binder information of the leading binders of a constant's type. -/
def binderInfos (env : Environment) (name : Name) : Array BinderInfo := Id.run do
  let some info := env.find? name | return #[]
  let mut type := info.type
  let mut found := #[]
  while true do
    match type with
    | .forallE _ _ body binder => found := found.push binder; type := body
    | .mdata _ inner => type := inner
    | _ => break
  return found

/-- Structural hash that skips the implicit, strict-implicit and instance
arguments of applied constants. -/
partial def explicitHash (env : Environment) (expression : Expr) : UInt64 :=
  match expression with
  | .app .. =>
    let function := expression.getAppFn
    let arguments := expression.getAppArgs
    match function with
    | .const name levels =>
      let binders := binderInfos env name
      let kept := arguments.zipIdx.filterMap fun (argument, position) =>
        if (binders[position]?.getD .default).isExplicit then some argument else none
      kept.foldl (fun state argument => mixHash 6 (mixHash state (explicitHash env argument)))
        (mixHash 5 (mixHash (hash name) (hash levels)))
    | _ => arguments.foldl (fun state argument => mixHash 6 (mixHash state (explicitHash env argument)))
        (explicitHash env function)
  | .lam _ type body _ => mixHash 7 (mixHash (explicitHash env type) (explicitHash env body))
  | .forallE _ type body _ => mixHash 8 (mixHash (explicitHash env type) (explicitHash env body))
  | .letE _ type value body _ =>
      mixHash 9 (mixHash (explicitHash env type) (mixHash (explicitHash env value) (explicitHash env body)))
  | .mdata _ inner => explicitHash env inner
  | .proj owner index inner => mixHash 12 (mixHash (hash owner) (mixHash (hash index) (explicitHash env inner)))
  | other => structuralHash other

/-- A hash as sixteen lowercase hexadecimal digits. -/
def hex (value : UInt64) : String :=
  let digits := String.ofList (Nat.toDigits 16 value.toNat)
  "".pushn '0' (16 - digits.length) ++ digits

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- The body of a type after its leading binders, ignoring metadata. -/
partial def afterBinders : Expr → Expr
  | .forallE _ _ body _ => afterBinders body
  | .mdata _ inner => afterBinders inner
  | other => other

/-- Whether a type ends in `Prop` after its leading binders. -/
def endsInProp (type : Expr) : Bool :=
  match afterBinders type with
  | .sort level => level.isZero
  | _ => false

/-- Whether a constant is a proposition-valued definition, inductive type or
class: its type ends in `Prop`. Theorems, axioms and constructors are proofs,
not propositions, and are excluded. -/
def propositionValued (info : ConstantInfo) : Bool :=
  match info with
  | .defnInfo _ | .opaqueInfo _ | .inductInfo _ => endsInProp info.type
  | _ => false

/-- The head constant of a proposition after its own leading binders, if the
head is a constant: `∀ x, A x → P x y` has head `P`. -/
def headConstant? (proposition : Expr) : Option Name :=
  match (afterBinders proposition).getAppFn.consumeMData with
  | .const name _ => some name
  | _ => none

def binderName : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict-implicit"
  | .instImplicit => "instance"

/-- One leading binder of a statement. `proof` holds when the binder is a proof
of a proposition (a premise); `head` is that proposition's head constant. -/
structure Premise where
  position : Nat
  binder : BinderInfo
  proof : Bool
  head : Option Name
  deriving Inhabited

/-- The premise telescope of a type: every leading binder, in order, with the
binder's sort decided by type inference in its local context. Implicit and
instance arguments are included. -/
def premises (type : Expr) : MetaM (Array Premise) :=
  forallTelescope type fun binders _ => do
    let mut found := #[]
    for binder in binders, position in [:binders.size] do
      let declaration ← binder.fvarId!.getDecl
      let proof ← isProp declaration.type
      found := found.push
        { position, binder := declaration.binderInfo, proof,
          head := if proof then headConstant? declaration.type else none }
    return found

/-- Proposition-valued constants that head a premise of a statement. -/
def premiseHeads (type : Expr) : MetaM (Array Name) := do
  let found ← premises type
  return found.filterMap fun premise => if premise.proof then premise.head else none

end ZkcTools.Statements

namespace ZkcTools.DeclarationAudit
open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  (env.header.modules[index.toNat]?).map (·.module)

def below (base name : Name) : Bool := base.isPrefixOf name

/-- Shared architecture policy. Python reads this exact JSON literal; Lean
compiles it with this module, so changing the policy invalidates audit builds.
Exceptions name exact reachable module pairs and remember whether each edge
was direct. Only the source graph audit checks freshness of the complete list;
a declaration audit may intentionally select just one client module. -/
-- BEGIN DEPENDENCY POLICY
private def dependencyPolicyJson : String := r##"
{
  "layers": [
    [
      "TestsArkLib",
      "tests"
    ],
    [
      "TestsSecurity",
      "tests"
    ],
    [
      "TestsClean",
      "tests"
    ],
    [
      "Tests",
      "tests"
    ],
    [
      "CleanExamplesAudit",
      "tests"
    ],
    [
      "CleanExamples",
      "clean-subjects"
    ],
    [
      "ZkcArkLibExamples",
      "optional-subjects"
    ],
    [
      "ZkcArkLib",
      "adapters"
    ],
    [
      "ZkcSecurityExamples",
      "security-subjects"
    ],
    [
      "ZkcSecurityTools",
      "security-tools"
    ],
    [
      "ZkcExamples",
      "subjects"
    ],
    [
      "ZkcTools.ConstructionBindings.Admission",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Diagnostics",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.ViewSyntax",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Root",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Inputs",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.LibraryBuilder",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.LibraryPlan",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Alignment",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.TargetPlacement",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Syntax",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Family",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Interface",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.LayoutLookup",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.StructuralFacts",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.TargetEquality",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.Readback",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.Presentation.Syntax",
      "proof-tools"
    ],
    [
      "ZkcTools.Companions",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.ReferenceLaws",
      "proof-tools"
    ],
    [
      "ZkcTools.ProcessView",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.ReferenceInstallation",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.InferReferenceInstallation",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.NormalizedRoot",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.PropertyInstallation",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.CountedShape",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.Association",
      "proof-tools"
    ],
    [
      "ZkcTools.StructuredSource.Composition",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.ArtifactBindingTactic",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.ProcessViewTactic",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.TransportReduction",
      "proof-tools"
    ],
    [
      "ZkcTools.ConstructionBindings.ScalarConnection",
      "proof-tools"
    ],
    [
      "ZkcTools",
      "tools"
    ],
    [
      "Zkc.Protocols",
      "families"
    ],
    [
      "ZkcSecurity.Mathematics.Probability",
      "probability"
    ],
    [
      "ZkcSecurity.Mathematics",
      "security-mathematics"
    ],
    [
      "ZkcSecurity.ProgramLogic",
      "security-logic"
    ],
    [
      "ZkcSecurity.Families",
      "security-families"
    ],
    [
      "ZkcSecurity.Transformations",
      "security-transformations"
    ],
    [
      "ZkcSecurity.Bindings",
      "security-bindings"
    ],
    [
      "ZkcSecurity.Claims.Methods",
      "security-methods"
    ],
    [
      "ZkcSecurity.Claims",
      "security-claims"
    ],
    [
      "ZkcSecurity",
      "security"
    ],
    [
      "ZkcClean",
      "clean"
    ],
    [
      "Zkc",
      "core"
    ],
    [
      "ArkLib",
      "arklib-upstream"
    ],
    [
      "VCVio",
      "security-upstream"
    ],
    [
      "Examples",
      "security-upstream"
    ],
    [
      "ToMathlib",
      "security-upstream"
    ],
    [
      "PolyFun",
      "security-upstream"
    ],
    [
      "Clean",
      "clean-upstream"
    ],
    [
      "CompPoly",
      "algebra-upstream"
    ]
  ],
  "allowed": [
    [
      "tests",
      [
        "tests",
        "clean-subjects",
        "optional-subjects",
        "adapters",
        "security-subjects",
        "security-tools",
        "subjects",
        "proof-tools",
        "tools",
        "families",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-methods",
        "security-claims",
        "security",
        "clean",
        "core",
        "arklib-upstream",
        "security-upstream",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "clean-subjects",
      [
        "core",
        "families",
        "clean",
        "clean-subjects",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "optional-subjects",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools",
        "subjects",
        "security-subjects",
        "adapters",
        "optional-subjects",
        "arklib-upstream"
      ]
    ],
    [
      "adapters",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools",
        "adapters",
        "arklib-upstream"
      ]
    ],
    [
      "security-subjects",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools",
        "subjects",
        "security-subjects",
        "tools"
      ]
    ],
    [
      "security-tools",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools",
        "tools"
      ]
    ],
    [
      "subjects",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "subjects"
      ]
    ],
    [
      "proof-tools",
      [
        "core",
        "proof-tools",
        "upstream"
      ]
    ],
    [
      "tools",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "tools"
      ]
    ],
    [
      "families",
      [
        "core",
        "families",
        "upstream",
        "proof-tools"
      ]
    ],
    [
      "probability",
      [
        "core",
        "probability",
        "upstream"
      ]
    ],
    [
      "security-mathematics",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-upstream",
        "algebra-upstream"
      ]
    ],
    [
      "security-logic",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-transformations",
        "security-upstream",
        "algebra-upstream"
      ]
    ],
    [
      "security-families",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-upstream",
        "algebra-upstream"
      ]
    ],
    [
      "security-transformations",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-claims",
        "security-upstream",
        "algebra-upstream"
      ]
    ],
    [
      "security-bindings",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools"
      ]
    ],
    [
      "security-methods",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools"
      ]
    ],
    [
      "security-claims",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools"
      ]
    ],
    [
      "security",
      [
        "core",
        "families",
        "proof-tools",
        "upstream",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-claims",
        "security-methods",
        "security",
        "security-upstream",
        "algebra-upstream",
        "security-tools"
      ]
    ],
    [
      "clean",
      [
        "core",
        "families",
        "clean",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "core",
      [
        "core",
        "upstream"
      ]
    ],
    [
      "arklib-upstream",
      [
        "tests",
        "clean-subjects",
        "optional-subjects",
        "adapters",
        "security-subjects",
        "security-tools",
        "subjects",
        "proof-tools",
        "tools",
        "families",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-methods",
        "security-claims",
        "security",
        "clean",
        "core",
        "arklib-upstream",
        "security-upstream",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "security-upstream",
      [
        "tests",
        "clean-subjects",
        "optional-subjects",
        "adapters",
        "security-subjects",
        "security-tools",
        "subjects",
        "proof-tools",
        "tools",
        "families",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-methods",
        "security-claims",
        "security",
        "clean",
        "core",
        "arklib-upstream",
        "security-upstream",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "clean-upstream",
      [
        "tests",
        "clean-subjects",
        "optional-subjects",
        "adapters",
        "security-subjects",
        "security-tools",
        "subjects",
        "proof-tools",
        "tools",
        "families",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-methods",
        "security-claims",
        "security",
        "clean",
        "core",
        "arklib-upstream",
        "security-upstream",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "algebra-upstream",
      [
        "tests",
        "clean-subjects",
        "optional-subjects",
        "adapters",
        "security-subjects",
        "security-tools",
        "subjects",
        "proof-tools",
        "tools",
        "families",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-methods",
        "security-claims",
        "security",
        "clean",
        "core",
        "arklib-upstream",
        "security-upstream",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ],
    [
      "upstream",
      [
        "tests",
        "clean-subjects",
        "optional-subjects",
        "adapters",
        "security-subjects",
        "security-tools",
        "subjects",
        "proof-tools",
        "tools",
        "families",
        "probability",
        "security-mathematics",
        "security-logic",
        "security-families",
        "security-transformations",
        "security-bindings",
        "security-methods",
        "security-claims",
        "security",
        "clean",
        "core",
        "arklib-upstream",
        "security-upstream",
        "clean-upstream",
        "algebra-upstream",
        "upstream"
      ]
    ]
  ],
  "guards": [
    {
      "name": "generic-execution",
      "owners": [
        "ZkcSecurity.ProgramLogic.Oracle.Execution"
      ],
      "exact": true,
      "dependencies": [
        "ZkcArkLib",
        "ArkLib",
        "ZkcSecurityExamples",
        "Zkc.Protocols",
        "Zkc.Source",
        "ZkcArkLibExamples"
      ]
    },
    {
      "name": "causal-source-independence",
      "owners": [
        "ZkcArkLib.Sumcheck.Multilinear.Causal"
      ],
      "exact": false,
      "dependencies": [
        "ZkcSecurityExamples",
        "Zkc.Source",
        "ZkcArkLibExamples"
      ]
    },
    {
      "name": "source-before-compiler",
      "owners": [
        "Zkc.Modules",
        "Zkc.Source"
      ],
      "exact": false,
      "dependencies": [
        "Zkc.Compiler"
      ]
    },
    {
      "name": "probability-without-source",
      "owners": [
        "ZkcSecurity.Mathematics.Probability"
      ],
      "exact": false,
      "dependencies": [
        "Zkc.Source",
        "Zkc.Compiler"
      ]
    },
    {
      "name": "generic-certificates",
      "owners": [
        "ZkcSecurity.ProgramLogic.Transcript.Interface",
        "ZkcSecurity.ProgramLogic.Transcript.Keyed",
        "ZkcSecurity.ProgramLogic.Transcript.Typed",
        "ZkcSecurity.Transformations.FiatShamir.Sampling",
        "ZkcSecurity.Transformations.FiatShamir.Decoding",
        "ZkcSecurity.Transformations.FiatShamir.Obligations",
        "ZkcSecurity.Transformations.FiatShamir.Grinding",
        "ZkcSecurity.Transformations.FiatShamir.Laws",
        "ZkcSecurity.ProgramLogic.Transcript.Lifting",
        "ZkcSecurity.ProgramLogic.Transcript.Reduction"
      ],
      "exact": true,
      "dependencies": [
        "Zkc.Construction",
        "ZkcSecurity.Transformations.FiatShamir.Soundness",
        "ZkcSecurity.ProgramLogic.Transcript.Composition"
      ]
    },
    {
      "name": "fixed-knowledge-before-method",
      "owners": [
        "ZkcSecurity.Claims.Knowledge",
        "ZkcSecurity.Claims.Subject",
        "ZkcSecurity.Claims.Extractor",
        "ZkcSecurity.Bindings.Extraction"
      ],
      "exact": false,
      "dependencies": [
        "ZkcSecurity.Claims.Methods"
      ]
    }
  ],
  "exceptions": []
}
"##
-- END DEPENDENCY POLICY

private structure DependencyGuard where
  name : String
  owners : List Name
  exact : Bool
  dependencies : List Name
  deriving FromJson

private structure DependencyEdge where
  owner : Name
  dependency : Name
  direct : Bool

private instance : FromJson DependencyEdge where
  fromJson? json := do
    let fields ← json.getArr?
    unless fields.size == 3 do throw "dependency edge must have three fields"
    let owner ← fromJson? fields[0]!
    let dependency ← fromJson? fields[1]!
    let direct ← fromJson? fields[2]!
    return { owner, dependency, direct }

private structure DependencyException where
  name : String
  reason : String
  edges : List DependencyEdge
  deriving FromJson

private structure DependencyPolicy where
  layers : List (Name × String)
  allowed : List (String × List String)
  guards : List DependencyGuard
  exceptions : List DependencyException
  deriving FromJson

-- Materialize ordinary data at elaboration time. JSON parsing is partial and
-- cannot appear in a policy that existing clients evaluate in the kernel.
-- Lists also retain the axiom-free computation used by the existing policy tests.
-- The same literal is still the sole source of the table in both audits.
private def dependencyPolicy : DependencyPolicy := by
  run_tac
    let .ok policy := Json.parse dependencyPolicyJson >>= (fromJson? (α := DependencyPolicy))
      | throwError "invalid dependency policy"
    let guards := policy.guards.map fun guard =>
      mkAppN (mkConst ``DependencyGuard.mk) #[toExpr guard.name, toExpr guard.owners,
        toExpr guard.exact, toExpr guard.dependencies]
    let exceptions ← policy.exceptions.mapM fun exception => do
      let edges := exception.edges.map fun edge =>
        mkAppN (mkConst ``DependencyEdge.mk) #[toExpr edge.owner, toExpr edge.dependency,
          toExpr edge.direct]
      let edges ← Lean.Meta.mkListLit (mkConst ``DependencyEdge) edges
      return mkAppN (mkConst ``DependencyException.mk) #[toExpr exception.name,
        toExpr exception.reason, edges]
    let guards ← Lean.Meta.mkListLit (mkConst ``DependencyGuard) guards
    let exceptions ← Lean.Meta.mkListLit (mkConst ``DependencyException) exceptions
    let value := mkAppN (mkConst ``DependencyPolicy.mk) #[toExpr policy.layers,
      toExpr policy.allowed, guards, exceptions]
    (← Lean.Elab.Tactic.getMainGoal).assign value
    Lean.Elab.Tactic.replaceMainGoal []

private def within (name root : Name) : Bool := root.isPrefixOf name

private def layer (policy : DependencyPolicy) (name : Name) : String :=
  ((policy.layers.find? fun entry => within name entry.1).map (·.2)).getD "upstream"

/-- Exact legacy reachability exceptions are shared with the source audit.
They never override the more specific generic-execution/source boundaries. -/
def permitted (owner dependency : Name) : Bool := Id.run do
  let policy := dependencyPolicy
  if policy.guards.any (fun guard =>
      guard.owners.any (fun root => if guard.exact then owner == root else within owner root) &&
      guard.dependencies.any (within dependency)) then return false
  let targets := (policy.allowed.find? fun entry => entry.1 == layer policy owner).map (·.2)
  if targets.any (·.contains (layer policy dependency)) then return true
  return policy.exceptions.any fun exception =>
    exception.edges.any fun edge => edge.owner == owner && edge.dependency == dependency

abbrev Graph := Std.HashMap Name (Array Name)

/-- Compute the finite closure, including cycles between mutually defined
declarations. Edges conservatively combine all declarations of each module. -/
partial def closure (graph : Graph) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then closure graph rest seen
      else closure graph ((graph[name]?.getD #[]).toList ++ rest) (seen.insert name)

/-- Recover the stored owners of a lazily realized equation in the consumer's
actual import closure. A merged environment can select a duplicate stored in an
unrelated test module; that module is not the provenance of this consumer's edge.
Every reachable stored version remains subject to the ordinary dependency rule. -/
def importedOwners (env : Environment) (imports : Graph) (consumer dependency : Name) : Array Name := Id.run do
  let reachable := closure imports (imports[consumer]?.getD #[]).toList
  let mut owners := #[]
  for index in [:env.header.moduleData.size] do
    let owner := env.header.modules[index]!.module
    if reachable.contains owner && env.header.moduleData[index]!.constNames.contains dependency then
      owners := owners.push owner
  return owners

/-- Audit every declaration owned by the selected imported module families.
Types and proof/definition bodies are inspected separately. The dependency
closure is conservative at module granularity; axiom collection is Lean's
transitive declaration-level check, including opaque proof bodies.
`exactModules` selects individual modules instead of families; `marker` identifies
the validation scope in build receipts.

A family is a module name, never a namespace: selection compares against the
module a declaration came from. A module is also not in its own environment
while it elaborates, so a file cannot audit itself -- what it owns is covered
by an audit run from a module that imports it. A family matching nothing is an
error rather than a pass with a smaller count, because six invocations here
named a namespace or their own module and reported a pass over nothing. -/
def check (families : List Name) (marker : String := "AUDIT-PASS")
    (exactModules : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut graph : Graph := {}
  let mut imports : Graph := {}
  for index in [:env.header.moduleData.size] do
    imports := imports.insert env.header.modules[index]!.module
      (env.header.moduleData[index]!.imports.map (·.module))
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut typeReferences : Nat := 0
  let mut valueReferences : Nat := 0
  let mut audited : Std.HashSet Name := {}
  let mut names : Std.HashSet Name := {}
  let mut matched : Std.HashSet Name := {}
  for index in [:env.header.moduleData.size] do
    let owner := env.header.modules[index]!.module
    let selected := families.filter (fun family =>
      if exactModules then family == owner else below family owner)
    if selected.isEmpty then continue
    for family in selected do
      matched := matched.insert family
    let data := env.header.moduleData[index]!
    let localNames : Std.HashSet Name := Std.HashSet.ofArray data.constNames
    for info in data.constants do
      let name := info.name
      names := names.insert name
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      if info matches .axiomInfo _ then
        unless allowedAxioms.contains name do
          throwError "unexpected owned axiom: {name} in {owner}"
      let types := info.type.getUsedConstants
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      typeReferences := typeReferences + types.size
      valueReferences := valueReferences + values.size
      -- Inspect every stored version of a lazily realized equation theorem.
      -- A merged Environment can retain one module's owner index and another
      -- module's equivalent proof body. ModuleData keeps their provenance paired.
      for reference in (types ++ values).push name do
        if !audited.contains reference then
          audited := audited.insert reference
          for axiomName in ← Lean.collectAxioms reference do
            unless allowedAxioms.contains axiomName do
              throwError "unexpected axiom: {name} uses {reference}, which depends on {axiomName}"
      for (kind, references) in [("type", types), ("body", values)] do
        for dependency in references do
          let dependencyOwner? :=
            if localNames.contains dependency then some owner else moduleOf env dependency
          let some dependencyOwner := dependencyOwner? | continue
          let mut owners := #[dependencyOwner]
          if !permitted owner dependencyOwner && !localNames.contains dependency then
            let stored := importedOwners env imports owner dependency
            if !stored.isEmpty then owners := stored
          for dependencyOwner in owners do
            unless permitted owner dependencyOwner do
              throwError "forbidden {kind} dependency: {name} in {owner} uses {dependency} from {dependencyOwner}"
            let edges := graph[owner]?.getD #[]
            if !edges.contains dependencyOwner then
              graph := graph.insert owner (edges.push dependencyOwner)
  for (owner, edges) in graph.toList do
    for dependency in (closure graph edges.toList).toList do
      unless permitted owner dependency do
        throwError "forbidden transitive declaration dependency: {owner} reaches {dependency}"
  -- A family that selected no module audits nothing and would still report a
  -- pass, so the count would name a scope wider than the one examined. The
  -- usual cause is a namespace where a module name belongs.
  for family in families do
    unless matched.contains family do
      throwError "{family} selected no module: audits name modules, not namespaces"
  logInfo m!"{marker} declarations={declarations} theorems={theorems}"
  logInfo m!"DECLARATION-VERSIONS total={declarations} distinct-names={names.size}"
  logInfo m!"DEPENDENCY-AUDIT-PASS modules={graph.size} type-references={typeReferences} body-references={valueReferences}"

/-- Audit the axiom closure of every declaration the current module has added
so far, private and generated declarations included. This replaces lists of
selected theorem names: placed at the end of a file, it covers every theorem of
the file, so a renamed theorem cannot leave a stale entry and a new theorem
cannot be left out. A module with no theorem is an error rather than a pass over
nothing. The whole-library audit run from an importing module also covers these
declarations, together with the dependency rules. -/
def checkCurrent (marker : String) : CommandElabM Unit := do
  let env ← getEnv
  let added := env.constants.map₂.toList.map (·.1) |>.toArray.qsort Name.lt
  let mut theorems : Nat := 0
  for name in added do
    let some info := env.find? name | continue
    if info.isTheorem then theorems := theorems + 1
    for axiomName in ← Lean.collectAxioms name do
      unless allowedAxioms.contains axiomName do
        throwError "unexpected axiom: {name} depends on {axiomName}"
  if theorems == 0 then
    throwError "{marker}: the current module declares no theorem"
  logInfo m!"{marker} declarations={added.size} theorems={theorems}"

/-- Audit the upstream boundary of the selected module families: every
declaration of a module below one of the `upstream` roots that the type or body
of a declaration owned by `families` names directly, and every declaration in
`named`, exists and has an axiom closure within `propext`, `Classical.choice`
and `Quot.sound`. The boundary is computed, not listed: it is the set of library
declarations the package consumes directly. `named` selects upstream
declarations whose status is reported although no owned declaration uses them.
An empty boundary is an error rather than a pass over nothing. -/
def checkBoundary (families upstream : List Name) (named : List Name := [])
    (marker : String := "BOUNDARY-AUDIT-PASS") : CommandElabM Unit := do
  let env ← getEnv
  let mut boundary : Std.HashSet Name := {}
  for index in [:env.header.moduleData.size] do
    let owner := env.header.modules[index]!.module
    unless families.any (below · owner) do continue
    for info in env.header.moduleData[index]!.constants do
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      for dependency in info.type.getUsedConstants ++ values do
        let some module := moduleOf env dependency | continue
        if upstream.any (below · module) then boundary := boundary.insert dependency
  for name in named do
    unless env.contains name do throwError "named upstream declaration is missing: {name}"
    boundary := boundary.insert name
  if boundary.isEmpty then
    throwError "{marker}: the selected families name no declaration below {upstream}"
  let selected := boundary.toArray.qsort Name.lt
  for name in selected do
    for axiomName in ← Lean.collectAxioms name do
      unless allowedAxioms.contains axiomName do
        throwError "unexpected axiom: upstream {name} depends on {axiomName}"
  logInfo m!"{marker} boundary={selected.size} named={named.length}"
  logInfo m!"UPSTREAM-BOUNDARY {selected.toList}"

/-- One registry entry as the audit sees it: its identifier, the constant of
its proposition schema if it has one, and whether that schema must be a
proposition-valued declaration. -/
abbrev RegistryEntry := String × Option Name × Bool

/-- Audit a registry of named hypotheses, models and trusted links.

* Identifiers are nonempty and distinct.
* Every schema constant exists, and a schema the entry declares
  proposition-valued is a definition, inductive type or class whose type ends in
  `Prop`.
* Coverage. A *named-hypothesis use* is a proposition-valued declaration owned
  by the selected module families that is the head constant of a premise of a
  theorem owned by those families: a leading binder of the theorem's
  elaborated statement, whatever its binder information (explicit, implicit,
  strict-implicit or instance), whose type is a proposition, read after that
  proposition's own leading binders (`∀ x, A x → D y` is headed by `D`). Every
  such declaration must be the schema of a registry entry. Uses under `¬`, as
  arguments of other constants, or inside conclusions are not premises and are
  not counted; neither are proposition-valued structure fields, nor the
  premises of structure projections, of auxiliary recursors and of theorems
  Lean generates with internal names.

The log line reports the counts that define the coverage. -/
def checkRegistry (entries : List RegistryEntry) (families : List Name)
    (marker : String := "REGISTRY-AUDIT-PASS") : CommandElabM Unit := do
  let env ← getEnv
  let mut identifiers : Std.HashSet String := {}
  let mut schemas : Std.HashSet Name := {}
  for (identifier, schema?, proposition) in entries do
    if identifier.isEmpty then throwError "registry entry with an empty identifier"
    if identifiers.contains identifier then throwError "duplicate registry identifier: {identifier}"
    identifiers := identifiers.insert identifier
    if let some schema := schema? then
      let some info := env.find? schema
        | throwError "registry entry {identifier} names a missing constant: {schema}"
      if proposition && !ZkcTools.Statements.propositionValued info then
        throwError "registry entry {identifier} names {schema}, which is not proposition-valued"
      schemas := schemas.insert schema
  let mut propositions : Std.HashSet Name := {}
  let mut theorems : Array ConstantInfo := #[]
  let mut matched : Std.HashSet Name := {}
  for index in [:env.header.moduleData.size] do
    let owner := env.header.modules[index]!.module
    let selected := families.filter (below · owner)
    if selected.isEmpty then continue
    for family in selected do
      matched := matched.insert family
    for info in env.header.moduleData[index]!.constants do
      -- A proposition-valued field of a structure is part of the data the
      -- structure carries, not a named hypothesis of its own.
      if ZkcTools.Statements.propositionValued info && !(env.isProjectionFn info.name) then
        propositions := propositions.insert info.name
      -- A structure projection has its own structure as a premise, and a
      -- recursor that Lean generates has its motive's; neither is a use.
      if info.isTheorem && !info.name.isInternal && !(env.isProjectionFn info.name) &&
          !isAuxRecursor env info.name then
        theorems := theorems.push info
  for family in families do
    unless matched.contains family do
      throwError "{family} selected no module: audits name modules, not namespaces"
  let uses ← liftTermElabM do
    let mut uses : Std.HashMap Name Name := {}
    -- Name the first theorem, in name order, that uses each head.
    for info in theorems.qsort (·.name.lt ·.name) do
      for head in ← ZkcTools.Statements.premiseHeads info.type do
        if propositions.contains head && !uses.contains head then
          uses := uses.insert head info.name
    return uses
  let missing := uses.toArray.filter (!schemas.contains ·.1) |>.qsort (·.1.lt ·.1)
  unless missing.isEmpty do
    let lines := missing.toList.map fun (head, user) => m!"{head} (a premise of {user})"
    throwError "unregistered named hypotheses:{indentD (MessageData.joinSep lines Format.line)}"
  let covered := uses.toArray.filter (schemas.contains ·.1) |>.size
  logInfo m!"{marker} entries={entries.length} schemas={schemas.size} \
    proposition-valued={propositions.size} premise-heads={uses.size} registered-premise-heads={covered} \
    theorems={theorems.size}"

end ZkcTools.DeclarationAudit
