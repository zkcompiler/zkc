module

public import Zkc.Construction.DomainView
public import Zkc.Construction.DomainExecutionLaws
public import Zkc.Source.KernelRfl

@[expose] public section

/-! Kernel-checked rules for whole constructed Process views. The equations
quantify every environment and typed reply, without success or honesty premises. -/
set_option autoImplicit false
set_option smartUnfolding false
namespace Zkc.Construction.Domain.Correspondence
open Zkc.Source
variable {model : Structured.DomainModel} {program : Structured.Program} {context : Context}

abbrev Block (instructions : List Instruction) (view : View.Block model.toCarriers) : Prop :=
  ∀ env, evaluate model program context instructions env = view env
abbrev Step (instruction : Instruction) (view : View.Block model.toCarriers) : Prop :=
  ∀ env, step model program context instruction env = view env

theorem empty : Block (model := model) (program := program) (context := context) [] View.empty :=
  fun _ => rfl

/-- The public recursion equation avoids downstream unfolding of private matchers. -/
theorem evaluate_cons (instruction : Instruction) (rest : List Instruction)
    (env : Environment model.toCarriers) :
    evaluate model program context (instruction :: rest) env =
      .call (.checkpoint env) (fun _ =>
        (step model program context instruction env).bind fun next =>
          .call (.checkpoint next) fun _ => evaluate model program context rest next) := by
  kernel_rfl

theorem sequence {instruction : Instruction} {rest : List Instruction}
    {first next : View.Block model.toCarriers}
    (head : Step (program := program) (context := context) instruction first)
    (tail : Block (program := program) (context := context) rest next) :
    Block (program := program) (context := context) (instruction :: rest)
      (View.sequence first next) := by
  have hs : step model program context instruction = first := funext head
  have ht : evaluate model program context rest = next := funext tail
  intro env
  simp only [evaluate_cons, hs, ht, View.sequence]

theorem receive (site schema peer : String) (ty : Structured.Ty) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.receive site schema peer ty, [], declared, []⟩
      (View.receive site schema peer ty declared) := by
  intro env
  kernel_rfl

theorem send (site schema peer : String) (reference : Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.send site schema peer, [reference], declared, []⟩
      (View.send site schema peer reference declared) := by
  intro env
  kernel_rfl

theorem indicesEmpty (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.indicesEmpty, [], declared, []⟩ (View.indicesEmpty declared) := by
  intro env
  kernel_rfl

theorem indicesAppend (coordinates index : Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.indicesAppend, [coordinates, index], declared, []⟩
      (View.indicesAppend coordinates index declared) := by
  intro env
  kernel_rfl

theorem observe (suite : String) (template : Template) (state value coordinates : Nat)
    (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.observe suite template, [state, value, coordinates], declared, []⟩
      (View.observe context suite template state value coordinates declared) := by
  intro env
  kernel_rfl

theorem challenge (suite field : String) (template : Template) (state coordinates : Nat)
    (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.challenge suite field template, [state, coordinates], declared, []⟩
      (View.challenge context suite field template state coordinates declared) := by
  intro env
  kernel_rfl

theorem indexChallenge (suite : String) (bound : Nat) (template : Template)
    (state boundReference coordinates : Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.indexChallenge suite bound template, [state, boundReference, coordinates], declared, []⟩
      (View.indexChallenge context suite bound template state boundReference coordinates declared) := by
  intro env
  kernel_rfl

theorem blockChallenge (suite : String) (bound count : Nat) (template : Template)
    (state coordinates : Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.blockChallenge suite bound count template, [state, coordinates], declared, []⟩
      (View.blockChallenge context suite bound count template state coordinates declared) := by
  intro env
  kernel_rfl

theorem localService (port : ServicePort) (request : Request) (template : Template)
    (coordinates references : List Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.localService port request template coordinates, references, declared, []⟩
      (View.localService context port request template coordinates references declared) := by
  intro env
  kernel_rfl

theorem calculation (operation : Calculation) (references : List Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.calculate operation, references, declared, []⟩
      (View.calculation model operation references declared) := by
  intro env
  kernel_rfl

theorem helper (name : String) (references : List Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.call name, references, declared, []⟩
      (View.helper model program name references declared) := by
  intro env
  kernel_rfl

theorem finiteFold (domain helper predicate : String) (references : List Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.finiteFold domain helper predicate, references, declared, []⟩
      (View.finiteFold model program domain helper predicate references declared) := by
  intro env
  kernel_rfl

/-- One rule binds an embedded Math body for every frame and return tuple. -/
theorem mathCompute (references : List Nat) (declared : List ValueSort)
    (region : InstructionRegion) {view : View.Block model.toCarriers}
    (same : Block (program := program) (context := context) region.instructions view) :
    Step (program := program) (context := context)
      ⟨.mathCompute, references, declared, [region]⟩
      (View.mathCompute program references declared region view) := by
  have bodyMeaning : evaluate model program context region.instructions = view := funext same
  intro env
  rcases region with ⟨inputs, body, yielded⟩
  change compute program references declared _ (evaluate model program context body) env = _
  rw [bodyMeaning]
  rfl

theorem guard (site : String) (condition : Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.guard site, [condition], declared, []⟩ (View.guard condition declared) := by
  intro env
  kernel_rfl

theorem require (site : String) (condition : Nat) (declared : List ValueSort) :
    Step (model := model) (program := program) (context := context)
      ⟨.require site, [condition], declared, []⟩ (View.require condition declared) := by
  intro env
  kernel_rfl

/-- One selected-region rule works for arbitrary closed arms, captures and
result tuples. Both body correspondences are required, including dormant arms. -/
theorem mathBranch (selector : Nat) (captures : List Nat) (declared : List ValueSort)
    (yes no : InstructionRegion) {yesView noView : View.Block model.toCarriers}
    (yesSame : Block (program := program) (context := context) yes.instructions yesView)
    (noSame : Block (program := program) (context := context) no.instructions noView) :
    Step (program := program) (context := context)
      ⟨.mathBranch, selector :: captures, declared, [yes, no]⟩
      (View.mathBranch program selector captures declared yes no yesView noView) := by
  have yesMeaning : evaluate model program context yes.instructions = yesView := funext yesSame
  have noMeaning : evaluate model program context no.instructions = noView := funext noSame
  intro env
  rcases yes with ⟨yesInputs, yesBody, yesYielded⟩
  rcases no with ⟨noInputs, noBody, noYielded⟩
  change selectClosed .math program selector captures declared _ _
    (evaluate model program context yesBody) (evaluate model program context noBody) env = _
  rw [yesMeaning, noMeaning]
  rfl

/-- The same all-arm correspondence rule applies to closed local selection. -/
theorem localBranch (selector : Nat) (captures : List Nat) (declared : List ValueSort)
    (yes no : InstructionRegion) {yesView noView : View.Block model.toCarriers}
    (yesSame : Block (program := program) (context := context) yes.instructions yesView)
    (noSame : Block (program := program) (context := context) no.instructions noView) :
    Step (program := program) (context := context)
      ⟨.localBranch, selector :: captures, declared, [yes, no]⟩
      (View.localBranch program selector captures declared yes no yesView noView) := by
  have yesMeaning : evaluate model program context yes.instructions = yesView := funext yesSame
  have noMeaning : evaluate model program context no.instructions = noView := funext noSame
  intro env
  rcases yes with ⟨yesInputs, yesBody, yesYielded⟩
  rcases no with ⟨noInputs, noBody, noYielded⟩
  change selectClosed .local program selector captures declared _ _
    (evaluate model program context yesBody) (evaluate model program context noBody) env = _
  rw [yesMeaning, noMeaning]
  rfl

/-- Closed range correspondence retains all iterations, early completion and stops. -/
theorem localRange (conditional : Bool) (lower upper : Nat) (values : List Nat)
    (declared : List ValueSort) (region : InstructionRegion) {view : View.Block model.toCarriers}
    (same : Block (program := program) (context := context) region.instructions view) :
    Step (program := program) (context := context)
      ⟨.localRange conditional, lower :: upper :: values, declared, [region]⟩
      (View.localRange program conditional lower upper values declared region view) := by
  have bodyMeaning : evaluate model program context region.instructions = view := funext same
  intro env
  rcases region with ⟨inputs, body, yielded⟩
  change executeRange program conditional lower upper values declared _
    (evaluate model program context body) env = _
  rw [bodyMeaning]
  rfl

theorem loop (site : String) (maximum : Nat) (yielded : List Nat) (count : Nat)
    (initial : List Nat) (declared : List ValueSort) {body : List Instruction}
    {view : View.Block model.toCarriers}
    (same : Block (program := program) (context := context) body view) :
    Step (program := program) (context := context)
      ⟨.loop site maximum, count :: initial, declared, [⟨(.data .index :: declared), body, yielded⟩]⟩
      (View.loop maximum yielded count initial declared view) := by
  have bodies : evaluate model program context body = view := funext same
  intro env
  have raw : step model program context
      ⟨.loop site maximum, count :: initial, declared, [⟨(.data .index :: declared), body, yielded⟩]⟩ env =
      View.loop maximum yielded count initial declared
        (evaluate model program context body) env := by
          change executeLoop (.data .index :: declared) maximum yielded count initial declared
            (evaluate model program context body) env = _
          simp only [executeLoop, View.loop, true_and]
          rfl
  rw [raw, bodies]

theorem participant (artifact : Participant) {view : View.Block model.toCarriers}
    (body : Block (program := program) (context := context) artifact.instructions view)
    (env : Environment model.toCarriers) :
    Domain.participant model program context artifact env =
      View.participant artifact.inputs artifact.outputs artifact.returned view env := by
  have bodies : evaluate model program context artifact.instructions = view := funext body
  have raw : Domain.participant model program context artifact env =
      View.participant artifact.inputs artifact.outputs artifact.returned
        (evaluate model program context artifact.instructions) env := by kernel_rfl
  rw [raw, bodies]

end Zkc.Construction.Domain.Correspondence
