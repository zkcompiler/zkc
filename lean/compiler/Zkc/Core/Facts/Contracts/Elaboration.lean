module

public import Zkc.Core.Facts.Contracts.Expressions

@[expose] public section

namespace Zkc.Core.BodyAnalysis

/-- Signature lookup for the operations allowed in assertions. A dialect may distinguish
several located types with the same payload. The Boolean test belongs to that dialect. -/
structure AssertionTypes (T Raw : Type) where
  signature : Raw → List T → Option (List T)
  boolean : T → Bool

namespace AssertionTypes

variable {T Raw : Type} (types : AssertionTypes T Raw)

mutual
  /-- Infer one expression, including the result port of a multi-result operation. -/
  def infer (context : List T) : Expr Raw → Option T
    | .arg position => context[position]?
    | .apply op operands result => do
        let actual ← inferAll context operands
        let outs ← types.signature op actual
        outs[result]?
  def inferAll (context : List T) : Exprs Raw → Option (List T)
    | .nil => some []
    | .cons first rest => return (← infer context first) :: (← inferAll context rest)
end

def isAssertion (context : List T) (expr : Expr Raw) : Bool :=
  ((types.infer context expr).map types.boolean).getD false

end AssertionTypes

variable {D : Dialect} {Raw : Type}

/-- The types of names in a context, when each is in scope. -/
def typesOf (Γ : Ctx D.Ty) (names : List Name) : Option (List D.Ty) :=
  names.mapM Γ.find?


def Instr.invariantTypes {Γ : Ctx D.Ty} {mid : List D.Ty} :
    Instr D Γ mid → Option (List D.Ty)
  | .loop (carried := carried) w .. => some (D.index w :: carried)
  | _ => none

variable [DecidableEq D.Ty] (types : AssertionTypes D.Ty Raw) (lemmas : List (Lemma D.Ty Raw))

/-- Check an annotation in the incoming context. Invariants additionally bind the loop index
and carried values, in that order. A registered lemma's expressions are checked at its signature. -/
def Annotation.check (Γ : Ctx D.Ty) (invariantTypes : Option (List D.Ty)) : Annotation Raw → Bool
  | .step number names =>
      match Lemma.resolve? lemmas Γ number names with
      | none => false
      | some l => l.premises.all (types.isAssertion l.parameters) && types.isAssertion l.parameters l.conclusion
  | .fact names expr =>
      ((typesOf (D := D) Γ names).map fun ts => types.isAssertion ts expr).getD false
  | .invariant names assertions =>
      (do
        let extra ← invariantTypes
        let named ← typesOf (D := D) Γ names
        return assertions.all (types.isAssertion (named ++ extra))).getD false

/-- Elaboration uses the lexical context before the instruction binds its results. -/
structure AnnotationContext (T : Type) where
  site : AnnotationSite
  names : Ctx T
  invariantTypes : Option (List T)

mutual
  /-- Enumerate real entries using the same cursor as the walk, including empty blocks. -/
  def Term.annotationContexts (cursor : StaticCursor) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List (AnnotationContext D.Ty)
    | _, _, .ret _ => []
    | Γ, _, .step key i _ rest => ⟨Instr.site cursor key i, Γ, Instr.invariantTypes i⟩ ::
        (Instr.regionContexts cursor key i ++ Term.annotationContexts cursor.next rest)
  def Instr.regionContexts (cursor : StaticCursor) (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List (AnnotationContext D.Ty)
    | _, _, .op .. | _, _, .guard .. => []
    | _, _, .choose _ _ _ _ t f =>
        Term.annotationContexts (cursor.region key) t ++ Term.annotationContexts (cursor.otherwise key) f
    | _, _, .cases _ _ _ _ arms => Arms.annotationContexts (cursor.region key) arms
    | _, _, .loop _ _ _ _ _ body => Term.annotationContexts (cursor.region key) body
    | _, _, .block n body => Term.annotationContexts (cursor.block key n) body
    | _, _, .attempt _ _ _ body => Term.annotationContexts (cursor.region key) body
  def Arms.annotationContexts (cursor : StaticCursor) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List (AnnotationContext D.Ty)
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest =>
        Term.annotationContexts cursor.arm arm ++ Arms.annotationContexts cursor.next rest
end

/-- Annotations must refer to real occurrences and type-check at each occurrence. -/
def checkAnnotations {Γ : Ctx D.Ty} {outs : List D.Ty} (body : Term D Γ outs)
    (notes : Annotations Raw) : Bool :=
  if notes.isEmpty then true else
    let entries := Term.annotationContexts .root body
    notes.all (fun n => entries.any (fun e => decide (e.site = n.1))) &&
      entries.all (fun e => (notes.at_ e.site).all (Annotation.check (D := D) types lemmas e.names e.invariantTypes))

/-- An optional bound query must itself be an expression that the dialect can type. -/
def ContractClause.boundTyped (clause : ContractClause Raw) (context : List D.Ty) : Bool :=
  clause.staticBound.all (fun expr => (types.infer context expr).isSome)

/-- Preconditions use the inputs, while postconditions can also refer to returned values. -/
def Contract.check (summary : Contract Raw) (ins outs : List D.Ty) : Bool :=
  (summary.requires.all (types.isAssertion ins) && summary.ensures.all (types.isAssertion (ins ++ outs))) &&
    (summary.preconditions.all (fun c => c.boundTyped (D := D) types ins) &&
     summary.postconditions.all (fun c => c.boundTyped (D := D) types (ins ++ outs)))

inductive DefinitionCheckError where
  | registry
  | annotations
  | contract
  deriving DecidableEq


/-- All registered statements are well scoped and Boolean over their formal parameters. -/
def Lemma.check {T : Type} (types : AssertionTypes T Raw) (lemma : Lemma T Raw) : Bool :=
  lemma.premises.all (types.isAssertion lemma.parameters) && types.isAssertion lemma.parameters lemma.conclusion

/-- Elaborate the registry, annotations and contract before issuing a verdict. -/
def checkDefinition {ins outs : List D.Ty} (inputs : Names ins) (body : Term D (Ctx.empty.extend inputs) outs)
    (notes : Annotations Raw) (summary : Contract Raw)
    (contractOK : {b : Bool // b = Contract.check (D := D) types summary ins outs} := ⟨_, rfl⟩) :
    Except DefinitionCheckError Unit :=
  if !lemmas.all (Lemma.check types) then .error .registry
  else if !checkAnnotations types lemmas body notes then .error .annotations
  else if !contractOK.val then .error .contract
  else .ok ()

end Zkc.Core.BodyAnalysis
