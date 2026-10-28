module

public import Zkc.Construction.ConnectionInputSchema
public import Zkc.Construction.ConnectionMasking

@[expose] public section

/-! Finite root input assembly. The actual source signature fixes visibility;
its ABI fixes all optional values and service identities. The profile fixes the
initial transcript slot. Runtime callers supply only the physical input row.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionInputs
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

/-- The existing participant ABI appends the transcript after its data inputs. -/
def historySlot (context : Context) (sorts : List ValueSort) : Option Nat :=
  match context.profile with
  | .plain => none
  | .fiatShamir _ => some (sorts.length - 1)

def historySorts (context : Context) (sorts : List ValueSort) : Bool :=
  match historySlot context sorts with
  | none => true
  | some reference => sorts[reference]? == some (.transcript context.suite)

/-- This default is observed only on malformed rows, which refuse before any
source action. Sorted rows recover the exact supplied transcript. -/
def inputHistory {carriers : Carriers} (context : Context) (sorts : List ValueSort)
    (physical : Domain.Environment carriers) : Domain.History carriers :=
  match historySlot context sorts with
  | none => []
  | some reference =>
    match physical[reference]? with
    | some (.transcript _ history) => history
    | _ => []

theorem inputHistory_read {carriers : Carriers} (context : Context) (sorts : List ValueSort)
    (valid : historySorts context sorts = true) (physical : Domain.Environment carriers)
    (matched : Domain.sortsMatch sorts physical = true)
    (reference : Nat) (selected : historySlot context sorts = some reference) :
    physical[reference]? = some (.transcript context.suite (inputHistory context sorts physical)) := by
  have declared : sorts[reference]? = some (.transcript context.suite) := by
    simpa only [historySorts, selected, beq_iff_eq] using valid
  have schema : physical.map Domain.Value.sort = sorts := by
    simpa only [Domain.sortsMatch, beq_iff_eq] using matched
  rw [← schema, List.getElem?_map] at declared
  cases found : physical[reference]? with
  | none => simp only [found, Option.map_none, reduceCtorEq] at declared
  | some value =>
    have nominal : value.sort = .transcript context.suite := by
      simpa only [found, Option.map_some, Option.some.injEq] using declared
    cases value with
    | data _ => cases nominal
    | indices _ => cases nominal
    | transcript suite history =>
      cases nominal
      simp only [inputHistory, selected, found]

/-- All instance fields are finite syntax, positions or finite equalities.
No input value, whole-source equation or semantic model law is supplied here. -/
structure InputLayout (signature : ProtocolSignature) (context : Context) (role : Nat)
    (sorts : List ValueSort) where
  locations : List Original.Location
  pattern : InputPattern signature.inputs
  shape : Shape pattern locations
  sorted : shape.sortsValid sorts = true
  visible : inputScopes role signature.inputScopes locations = true
  layout : Layout pattern.scope
  cells : InitialLayout pattern locations context.suite (historySlot context sorts) 0 layout
  length : layout.length = sorts.length
  history : historySorts context sorts = true

namespace InputLayout
variable {signature : ProtocolSignature} {context : Context} {role : Nat} {sorts : List ValueSort}

def abi (inputs : InputLayout signature context role sorts) : Original.InputABI :=
  ⟨sorts, inputs.locations⟩

def initial {carriers : Carriers} (_inputs : InputLayout signature context role sorts)
    (physical : Domain.Environment carriers) : Original.State carriers :=
  ⟨[], inputHistory context sorts physical⟩

/-- Physical decoding produces the symbolic binders and the complete invariant
in one place. Service handles remain exactly those fixed by the source ABI. -/
theorem prepare (inputs : InputLayout signature context role sorts) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) (matched : Domain.sortsMatch sorts physical = true) :
    ∃ binders : Binders model inputs.pattern.scope,
      Original.ValuesHolds physical inputs.locations (inputs.pattern.environment model binders) ∧
      Holds model binders (inputs.initial physical).history inputs.layout physical := by
  obtain ⟨binders, decoded⟩ := inputs.shape.binders_of_sorts inputs.sorted physical matched
  refine ⟨binders, decoded, inputs.cells.sound binders _ physical ?_ decoded ?_⟩
  · have schema : physical.map Domain.Value.sort = sorts := by
      simpa only [Domain.sortsMatch, beq_iff_eq] using matched
    simpa only [List.length_map] using inputs.length.trans (congrArg List.length schema).symm
  · exact inputHistory_read context sorts inputs.history physical matched

end InputLayout
/-- The sorted physical FS ABI reads its actual last transcript, including
arbitrary nonempty history. This follows from the participant input layout. -/
theorem inputHistory_inputFrame {carriers : Carriers} (context : Context)
    (replacement : Replacement) (profile : context.profile = .fiatShamir replacement)
    (sorts : List ValueSort) (data : Domain.Environment carriers) (initial : Domain.History carriers)
    (sorted : Domain.sortsMatch sorts (Domain.inputFrame context data initial) = true) :
    inputHistory context sorts (Domain.inputFrame context data initial) = initial := by
  have schema : (Domain.inputFrame context data initial).map Domain.Value.sort = sorts := by
    simpa only [Domain.sortsMatch, beq_iff_eq] using sorted
  have length : sorts.length = data.length + 1 := by
    simpa only [List.length_map, Domain.inputFrame, profile, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] using (congrArg List.length schema).symm
  simp [inputHistory, historySlot, profile, length, Domain.inputFrame]


end Zkc.Construction.ConnectionInputs
