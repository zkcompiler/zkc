import Zkc.Executable.DomainCompleteness
import Zkc.Executable.DomainNormalization
import Zkc.Executable.Normalization

/-! Budget/failure-order controls for canonical Code, including a checked
counterexample to unscoped raw normalization. -/
set_option autoImplicit false
namespace Tests.DomainCode
open Zkc Zkc.Source Zkc.Construction Zkc.Executable
open Zkc.Executable.DomainVM
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (program : Structured.Program) (context : Context) (key : Origin → Origin)
  (initial : History F G) (challenge : History F G → m F) (proof : Proof F G)

private def oneRound : Lowered := ⟨[.loop "round" 1 [] [0] [] [.charge 2]], [], []⟩

-- Entry costs one, body two, yield one, final return one. The yield and return
-- each exhaust at their own boundary, after the preceding work.
example : metered program context key initial challenge (fun _ _ => 0) 3 oneRound
    [.data (.index 1)] proof = pure (.stopped .exhausted, proof) := by
  simp [metered, oneRound, meteredK, meteredStep, meteredIterate, Domain.read,
    Domain.sortsMatch, List.range_succ]

example : metered program context key initial challenge (fun _ _ => 0) 4 oneRound
    [.data (.index 1)] proof = pure (.stopped .exhausted, proof) := by
  simp [metered, oneRound, meteredK, meteredStep, meteredIterate, Domain.read,
    Domain.sortsMatch, List.range_succ]

example : metered program context key initial challenge (fun _ _ => 0) 5 oneRound
    [.data (.index 1)] proof = pure (.returned [], proof) := by
  simp [metered, oneRound, meteredK, meteredStep, meteredIterate, Domain.read,
    Domain.sortsMatch, List.range_succ]

-- Dynamic helper work is charged before invoking the actual admitted helper.
example : meteredStep program context key initial challenge (fun _ _ => 2) 2
    (.helper ⟨.call "helper", [], [], []⟩) [] proof 0
    (fun _ unread _ => pure (.returned (), unread)) = pure (.stopped .exhausted, proof) := by
  simp [meteredStep, Domain.read, arguments]

-- A wrong scalar sort preserves the entire malformed unread proof head.
example : meteredStep program context key initial challenge (fun _ _ => 0) 1
    (.step ⟨.receive "m" "m" "P" (.field "fr"), [], [.data (.field "fr")], []⟩ 1)
    [] (.boolean false :: proof) 0
    (fun _ unread _ => pure (.returned (), unread)) =
      pure (.stopped .refused, .boolean false :: proof) := by
  simp [meteredStep, Domain.step, Domain.dataType, Structured.Ty.isService,
    Uniform.DomainAdapter.runK, Value.decode]

-- Raw metadata is semantically relevant to Domain, even for an unused pure
-- result. The old normalizer accepts this pair; canonical outcomes differ.
private def malformed : Instruction := ⟨.indicesEmpty, [], [], []⟩

example : (checkNormalized [] [malformed] [] [] []).toOption.isSome = true := by decide +kernel

example : DomainVM.observation (F := F) (G := G) program context [malformed] [] [] = .halt .refused := by
  simp [DomainVM.observation, outcome, malformed, Domain.evaluate, Domain.step,
    Domain.sortsMatch, Domain.Value.sort, PIR.Process.bind,
    PIR.Process.interpret, Original.forgetCheckpoints]

example : DomainVM.observation (F := F) (G := G) program context [] [] [] = .done [] := by
  simp [DomainVM.observation, outcome, readback, Domain.evaluate, Domain.read,
    PIR.Process.bind, PIR.Process.interpret]

private def queryContext : Context :=
  Context.fiatShamir "entry" ["P", "V"] 0 1 2 "random.fr/0" (some (.draw "fr")) "suite" []

private def queryTemplate : Template :=
  ⟨"entry", [], ["query", "entry", "q", "input_2", "random.fr/0", "draw", "V"]⟩

private def queryThenFalse : Lowered := ⟨[
  .step ⟨.challenge "suite" "fr" queryTemplate, [0, 1],
    [.data (.field "fr"), .transcript "suite"], []⟩ 1,
  .step ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩ 1], [4], []⟩

private def counted (_ : History F G) : StateM Nat F := fun count => (0, count + 1)

-- The actual Code invokes the oracle even though its eventual Boolean is
-- false. A stop at the final return also retains that action.
example : (metered program queryContext id [] (counted (F := F) (G := G)) (fun _ _ => 0) 3
    queryThenFalse [.transcript "suite" [], .indices []] proof).run 0 =
      ((.returned [.data (.boolean false)], proof), 1) := by
  simp [metered, meteredK, meteredStep, queryThenFalse, queryContext, queryTemplate,
    Domain.step, Domain.queryOrigin, Domain.templateOrigin, Domain.atCoordinates,
    Domain.sortsMatch, Domain.Value.sort, Domain.read, Template.origin, Template.repeats,
    Template.qualify, Template.applicationPrefix, Context.fiatShamir, Context.suite,
    Context.contract, Context.request, Context.replacement?, Context.query, Context.service,
    Context.role, Origin.query, Uniform.DomainAdapter.runK, Uniform.DomainAdapter.query, Domain.drawRequest, Request.draw,
    Uniform.DomainAdapter.readbackHistory, StateT.run]
  rfl

example : (metered program queryContext id [] (counted (F := F) (G := G)) (fun _ _ => 0) 2
    queryThenFalse [.transcript "suite" [], .indices []] proof).run 0 =
      ((.stopped .exhausted, proof), 1) := by
  simp [metered, meteredK, meteredStep, queryThenFalse, queryContext, queryTemplate,
    Domain.step, Domain.queryOrigin, Domain.templateOrigin, Domain.atCoordinates,
    Domain.sortsMatch, Domain.Value.sort, Domain.read, Template.origin, Template.repeats,
    Template.qualify, Template.applicationPrefix, Context.fiatShamir, Context.suite,
    Context.contract, Context.request, Context.replacement?, Context.query, Context.service,
    Context.role, Origin.query, Uniform.DomainAdapter.runK, Uniform.DomainAdapter.query, Domain.drawRequest, Request.draw,
    Uniform.DomainAdapter.readbackHistory, StateT.run]
  rfl

end Tests.DomainCode
