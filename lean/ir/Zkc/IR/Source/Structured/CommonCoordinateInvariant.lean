module

public import Zkc.IR.Source.Structured.CommonCoordinateReadback
public import Zkc.IR.Source.Structured.CommonCoordinateCertificate

@[expose] public section

/-! Local preservation laws for the checked coordinate environment. Unknown entries make
no assertion about runtime presence, contents, or successful execution. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm
variable {model : DomainModel} {scope : Scope}

theorem get_map {α : Type} {V W : α → Type} (f : {a : α} → V a → W a)
    {types : List α} (values : Values V types) {a : α} (position : Var types a) :
    (mapValues f values).get position = f (values.get position) := by
  induction values with
  | nil => cases position
  | cons head tail ih => cases position with
    | here => rfl
    | there position => exact ih position

theorem matches_operands {inputs types : List Ty} (symbols : Symbols scope inputs)
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) inputs)
    (matched : Matches symbols observations values) (args : Operands inputs types) :
    Matches (args.eval symbols.get) observations (args.eval values.get) := by
  intro ty position term known
  rw [Operands.get_eval] at known ⊢
  exact matched (args.get position) term known

theorem matches_append {left right : List Ty} (symbols : Symbols scope left)
    (rest : Symbols scope right) (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) left)
    (tail : Values (Component (ProtocolValue model.toCarriers)) right)
    (first : Matches symbols observations values) (second : Matches rest observations tail) :
    Matches (symbols.append rest) observations (values.append tail) := by
  induction symbols with
  | nil => cases values; exact second
  | cons head symbols ih =>
    cases values with | cons value values =>
      intro ty position term known
      cases position with
      | here => exact first .here term known
      | there position =>
        exact ih values (fun position term known ↦ first (.there position) term known)
          position term known

theorem get_concrete {types : List Ty}
    (values : Values (Component (ProtocolValue model.toCarriers)) types)
    {type : Ty} (position : Var types type) :
    (ProtocolValue.concreteComponents values).get position =
      (values.get position).bind ProtocolValue.toConcrete := by
  induction values with
  | nil => cases position
  | cons head tail ih => cases position with
    | here => rfl
    | there position => exact ih position

theorem collected_readback {types : List Ty} (symbols : Symbols scope types)
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) types)
    (matched : Matches symbols observations values) (terms : Terms [] scope types)
    (collected : collect symbols = some terms) :
    RoleFamily.sequence (ProtocolValue.concreteComponents values) = observeTerms model terms observations := by
  induction symbols with
  | nil => cases values; cases Option.some.inj collected; rfl
  | cons head tail ih =>
    cases values with | cons value values =>
      cases head with
      | none => simp [collect] at collected
      | some head =>
        cases rest : collect tail with
        | none => simp [collect, rest] at collected
        | some terms' =>
          have same : terms = .cons head terms' := by simpa [collect, rest] using collected.symm
          subst terms
          have first := matched .here head rfl
          change value.bind ProtocolValue.toConcrete = observe model head observations at first
          have next := ih values (fun position term known ↦ matched (.there position) term known) terms' rest
          simp only [ProtocolValue.concreteComponents, RoleFamily.sequence, observeTerms, first, next]

theorem concrete_embed_get {types : List Ty} (values : Values (Component model.Value) types)
    {type : Ty} (position : Var types type) :
    ((ProtocolValue.embedComponents values).get position).bind ProtocolValue.toConcrete =
      values.get position := by
  rw [← get_concrete, ProtocolValue.concreteComponents_embedComponents]

theorem get_identity {types : List Ty} {type : Ty} (position : Var types type) :
    (Operands.identity types).get position = position := by
  induction position with
  | here => rfl
  | there position ih =>
    simp only [Operands.identity, Values.get, Operands.get_rename, ih]

theorem calculated_readback (op : Op) (allowed : scalar op = true)
    (terms : Terms [] scope op.arguments) (observations : Observations model scope)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (read : RoleFamily.sequence (ProtocolValue.concreteComponents args) = observeTerms model terms observations) :
    Matches (calculated op allowed terms) observations
      (ProtocolValue.embedComponents (scalarValues model op allowed (ProtocolValue.concreteComponents args))) := by
  intro ty position term known
  simp only [calculated, get_map, get_identity, Option.some.injEq] at known
  subst term
  rw [concrete_embed_get]
  simp only [scalarValues, read, observe]
  cases observed : observeTerms model terms observations with
  | none => exact Values.get_absent position
  | some values => exact Values.get_present (op.evalTotal model (scalar_total allowed) values) position

mutual
  theorem observe_rename {target : Scope} (rename : Rename scope target)
      {ty : Ty} (term : Expression scope ty) (before : Observations model scope)
      (after : Observations model target)
      (same : ∀ {slot} (position : Var scope slot), after.get (rename position) = before.get position) :
      observe model (term.rename rename) after = observe model term before := by
    cases term with
    | var position => exact same position
    | result position field => simp only [Term.rename, observe, same]
    | capability | index | bool | field | groupZero => rfl
    | law entry => exact Fin.elim0 entry
    | «calc» op total args position =>
      exact congrArg (Option.map (fun values ↦ (op.evalTotal model total values).get position))
        (observeTerms_rename rename args before after same)

  theorem observeTerms_rename {target : Scope} (rename : Rename scope target)
      {types : List Ty} (terms : Terms [] scope types) (before : Observations model scope)
      (after : Observations model target)
      (same : ∀ {slot} (position : Var scope slot), after.get (rename position) = before.get position) :
      observeTerms model (terms.rename rename) after = observeTerms model terms before := by
    cases terms with
    | nil => rfl
    | cons head tail =>
      simp only [Terms.rename, observeTerms, observe_rename rename head before after same,
        observeTerms_rename rename tail before after same]
end

/-- The repeat counter is a fresh observation, while captures keep their actual source
identities. No equality of iteration counts or carried values is used here. -/
theorem matches_weaken {types : List Ty} (symbols : Symbols scope types)
    (observations : Observations model scope) (counter : Option Nat)
    (values : Values (Component (ProtocolValue model.toCarriers)) types)
    (matched : Matches symbols observations values) :
    Matches (weakenSymbols symbols) (.cons counter observations) values := by
  intro ty position term known
  simp only [weakenSymbols, get_map] at known
  cases found : symbols.get position with
  | none => simp [found] at known
  | some original =>
    have same : term = original.rename (fun position ↦ .there position) := by
      simpa only [found, Option.map_some, Option.some.injEq] using known.symm
    subst term
    exact (matched position original found).trans
      (observe_rename (model := model) (fun position ↦ .there position) original observations
        (show Observations model (.value .index :: scope) from .cons counter observations)
        (fun _ ↦ rfl)).symm

end Zkc.Source.Structured.CommonCoordinate
