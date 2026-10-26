module

public import Zkc.Executable.DomainOrigins
public import Zkc.Construction.DomainViewLaws

@[expose] public section

/-! Native transcript-operation boundaries. These equations use the actual
Domain step and scalar handler and retain the nominal environment in their
continuations. Static origin eligibility and reached coordinate depth are
explicit structural facts, independent of a protocol relation or an honest
proof. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

theorem step_challenge_native [LawfulMonad m] {R : Type} (program : Structured.Program) (context : Context)
    (initial : History F G) (challenge : History F G → m F) (suite field : String)
    (template : Template) (state coordinates : Nat) (env : Environment F G)
    (history : Domain.History (Structured.uniformCarriers F G)) (path : List Nat)
    (localEntry site port contract owner : String) (suffix : History F G)
    (proof : Proof F G) (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G))
    (stateEq : env[state]? = some (.transcript suite history))
    (coordinatesEq : env[coordinates]? = some (.indices path))
    (entry : template.entry = context.entry) (depth : template.repeats = path.length)
    (kinds : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true)
    (suiteEq : suite = context.suite) (contractEq : context.contract = "random." ++ field ++ "/0")
    (request : context.request = some (.draw field))
    (event : template.event = ["query", localEntry, site, port, contract, "draw", owner])
    (mapped : DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix) :
    DomainAdapter.runK Origin.withoutCoordinates initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.challenge suite field template, [state, coordinates],
          [.data (.field field), .transcript suite], []⟩ env) proof next = (do
      let answer ← challenge (initial ++ suffix ++ [.challenge (context.query (template.qualify site) (.draw field))])
      next (env ++ [.data (.field field answer),
        .transcript suite (history ++ [.challenge
          (Domain.atCoordinates (context.query (template.qualify site) (.draw field)) path)])]) proof) := by
  have resolved := queryOrigin_scoped context suite field template path localEntry site port contract owner
    entry depth kinds suiteEq contractEq request event
  have asked : (Domain.atCoordinates (context.query (template.qualify site) (.draw field)) path).request =
      some (.draw field) := by simp only [Domain.atCoordinates]; split <;> rfl
  rw [Domain.Correspondence.challenge (model := Structured.ringModel F G)
    (program := program) (context := context) suite field template state coordinates _ env]
  rw [Domain.View.challenge_eq context suite field template state coordinates env history path _
    stateEq coordinatesEq resolved asked]
  simp only [DomainAdapter.runK, DomainAdapter.drawRequest_of_draw _ field asked, ite_true]
  rw [query_native initial challenge history (context.query (template.qualify site) (.draw field))
    path field suffix rfl rfl mapped]
  simp only [bind_assoc, pure_bind, Domain.View.append, Domain.sortsMatch, List.map_cons,
    List.map_nil, Domain.Value.sort, beq_self_eq_true, ite_true, DomainAdapter.runK]
  congr 1
  funext answer
  congr 4
  congr 1
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- The native operation invokes the same scalar challenge at that static
key. In particular the operation itself does not inspect coordinate values. -/
theorem resolved_challenge_native (context : Context) (challenge : History F G → m F)
    (live : History F G) (suite field : String) (template : Template) (path : List Nat)
    (localEntry site port contract owner : String) (request : context.request = some (.draw field))
    (event : template.event = ["query", localEntry, site, port, contract, "draw", owner]) :
    Resolved.apply context challenge live (.challenge suite field template) [.transcript live, .indices path] =
      (fun answer => .returned ([.data (.field field answer),
        .transcript (live ++ [.challenge (context.query (template.qualify site) (.draw field))])],
        live ++ [.challenge (context.query (template.qualify site) (.draw field))], 1)) <$>
        challenge (live ++ [.challenge (context.query (template.qualify site) (.draw field))]) := by
  simp only [Resolved.apply, Template.origin, event, request, Option.map_some, ite_true]

/-- Observation updates the reached nominal transcript; its handler consumes
no proof message. The scalar image is supplied by mapped_message. -/
theorem step_observe_native {R : Type} (program : Structured.Program) (context : Context)
    (initial : History F G) (challenge : History F G → m F) (template : Template)
    (state value coordinates : Nat) (env : Environment F G)
    (history : Domain.History (Structured.uniformCarriers F G)) (path : List Nat) (payload : Payload F G)
    (localEntry site sender receiver : String) (proof : Proof F G)
    (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G))
    (stateEq : env[state]? = some (.transcript context.suite history))
    (valueEq : env[value]? = some (.data (DomainAdapter.embedPayload payload)))
    (coordinatesEq : env[coordinates]? = some (.indices path))
    (entry : template.entry = context.entry) (depth : template.repeats = path.length)
    (kinds : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true)
    (event : template.event = ["message", localEntry, site, site, sender, receiver]) :
    DomainAdapter.runK Origin.withoutCoordinates initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.observe context.suite template, [state, value, coordinates], [.transcript context.suite], []⟩ env)
      proof next = next
        (env ++ [.transcript context.suite (history ++ [.message
          (Domain.atCoordinates (Origin.message context.entry (template.qualify site) sender receiver) path)
          (DomainAdapter.embedPayload payload)])]) proof := by
  have resolved := messageOrigin_scoped context template path localEntry site sender receiver entry depth kinds event
  have message : (Domain.atCoordinates
      (Origin.message context.entry (template.qualify site) sender receiver) path).request = none := by
    simp only [Domain.atCoordinates]; split <;> rfl
  rw [Domain.Correspondence.observe (model := Structured.ringModel F G)
    (program := program) (context := context) context.suite template state value coordinates _ env]
  rw [Domain.View.observe_eq context template state value coordinates env history
    (DomainAdapter.embedPayload payload) path _ stateEq valueEq coordinatesEq resolved message]
  simp only [DomainAdapter.runK, Domain.View.append, Domain.sortsMatch, List.map_cons,
    List.map_nil, Domain.Value.sort, beq_self_eq_true, ite_true]

/-- The native observation has the identical scalar payload and static key.
Malformed payload sorts are excluded only by this explicit leaf argument. -/
theorem resolved_observe_native (context : Context) (challenge : History F G → m F)
    (live : History F G) (suite : String) (template : Template) (path : List Nat) (payload : Payload F G)
    (localEntry site sender receiver : String)
    (event : template.event = ["message", localEntry, site, site, sender, receiver]) :
    Resolved.apply context challenge live (.observe suite (payloadType payload) template)
      [.transcript live, .data payload, .indices path] =
      pure (.returned ([.transcript (live ++ [.message
        (Origin.message context.entry (template.qualify site) sender receiver) payload])],
        live ++ [.message (Origin.message context.entry (template.qualify site) sender receiver) payload], 1)) := by
  simp only [Resolved.apply, Template.origin, event, and_self, ite_true]

end Zkc.Executable.DomainVM
