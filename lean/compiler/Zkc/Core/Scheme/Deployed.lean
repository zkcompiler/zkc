module

public import Zkc.Core.Scheme.Roles
public import Zkc.Core.Admission.Admission
public import Zkc.Core.World.Stack

@[expose] public section

/-!
A deployed scheme and the run of a role under its handlers, with what deployment decides
about scopes and keys.
-/

namespace Zkc.Core

/-! ## Deployment -/

/-- A deployed scheme: the admitted program, the declaration, the entry, and each role's
handlers in order, the nearest to its program first. -/
structure Deployed (V : Vocabulary) where
  admitted : Admitted V
  declaration : Declaration
  entry : ProtocolHeader V
  callee : Member admitted.program.headers.protocols entry
  stack : (r : Role) → List (Layer V admitted.program.headers r entry.ins)

section
variable {V : Vocabulary}

/-- The attempts of a deployment: the bound and the site of the attempt. -/
def Deployed.retry (d : Deployed V) : Option (Nat × Site) :=
  d.declaration.retry

/-- The prover and the verifier of a deployment. -/
def Deployed.roles (d : Deployed V) : Option (Role × Role) :=
  proverAndVerifier d.entry d.declaration

/-- The definitions of a module. -/
def ModuleRef.definitions (m : ModuleRef) : List Key := m.members.map (·.2)

/-- The definitions that a declaration names: those of its suite, of its layout and of its
commitments, those that recover values, and the one that derives the samples. -/
def Declaration.definitions (declaration : Declaration) : List Key :=
  (match declaration.construction with
    | .interactive => []
    | .derived suite => suite.definitions) ++
  (match declaration.layout with
    | none => []
    | some layout => layout.module.definitions ++ layout.recover.map (·.2)) ++
  declaration.samples.toList ++ declaration.commits.flatMap (·.scheme.definitions)

/-- The keys of the definitions that a deployment reaches: by calls and applications from its
entry and from the definitions that its declaration names. -/
def Deployed.closure (d : Deployed V) : List Key :=
  (d.declaration.entry :: d.declaration.definitions).flatMap d.admitted.program.defs.closureOf

/-- The run of a role of a deployed scheme: each layer's `start` on its part of what the
layers take and on the inputs that the role holds, the nearest to the program first; then the
role's program under its handlers, with its attempts; then each layer's `finish`. A stop at
any of these is the stop of the run. -/
def Deployed.run (d : Deployed V) (M : Model V) (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r))) :
    Process (RSig M) Stop (HList (RV M r) d.entry.outs × HList M.Val (Stack.Gives (d.stack r))) :=
  (Stack.start M (Defs.fnTable M d.admitted.program.defs) (d.stack r) ins taken).bind fun first =>
    (((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
        (Defs.rTable M d.admitted.program.defs) (d.stack r)).run (retryOf M d.retry)
        (roleMeaning M d.admitted.program d.callee r [] ins) first).mapHalt Prod.fst).bind fun out =>
      (Stack.finish M (Defs.fnTable M d.admitted.program.defs) (d.stack r) out.2).map
        fun gives => (out.1, gives)

end

/-! ## What deployment decides about scopes and keys -/

mutual
  /-- The sites of the attempts of a shape, through its applications. -/
  def Shape.attemptSites {V : Vocabulary} (through : List Key) : Shape V → List Site
    | .nil => []
    | .event _ _ _ rest => Shape.attemptSites through rest
    | .choice _ _ arms rest => Shapes.attemptSites through arms ++ Shape.attemptSites through rest
    | .loop _ _ body rest => Shape.attemptSites through body ++ Shape.attemptSites through rest
    | .apply key _ _ inner rest =>
        Shape.attemptSites (through ++ [key]) inner ++ Shape.attemptSites through rest
    | .block _ _ body rest => Shape.attemptSites through body ++ Shape.attemptSites through rest
    | .guard _ _ _ rest => Shape.attemptSites through rest
    | .attempt key _ body rest =>
        ⟨through, key⟩ :: (Shape.attemptSites through body ++ Shape.attemptSites through rest)
  def Shapes.attemptSites {V : Vocabulary} (through : List Key) : Shapes V → List Site
    | .nil => []
    | .cons arm rest => Shape.attemptSites through arm ++ Shapes.attemptSites through rest
end

mutual
  /-- The sites of the guards with `abort` of a shape that are not inside an attempt, through
  its applications; `inside` says whether the shape is inside one. -/
  def Shape.abortsOutside {V : Vocabulary} (through : List Key) (inside : Bool) :
      Shape V → List Site
    | .nil => []
    | .event _ _ _ rest => Shape.abortsOutside through inside rest
    | .choice _ _ arms rest =>
        Shapes.abortsOutside through inside arms ++ Shape.abortsOutside through inside rest
    | .loop _ _ body rest =>
        Shape.abortsOutside through inside body ++ Shape.abortsOutside through inside rest
    | .apply key _ _ inner rest =>
        Shape.abortsOutside (through ++ [key]) inside inner ++ Shape.abortsOutside through inside rest
    | .block _ _ body rest =>
        Shape.abortsOutside through inside body ++ Shape.abortsOutside through inside rest
    | .guard key _ why rest =>
        (if why = .abort ∧ inside = false then [⟨through, key⟩] else []) ++
          Shape.abortsOutside through inside rest
    | .attempt _ _ body rest =>
        Shape.abortsOutside through true body ++ Shape.abortsOutside through inside rest
  def Shapes.abortsOutside {V : Vocabulary} (through : List Key) (inside : Bool) :
      Shapes V → List Site
    | .nil => []
    | .cons arm rest => Shape.abortsOutside through inside arm ++ Shapes.abortsOutside through inside rest
end

mutual
  /-- The keys of the events that a term performs itself, by its operations. -/
  def Term.eventKeys {D : Dialect} (isEvent : ∀ {ins res : List D.Ty}, D.Op ins res → Bool) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Key
    | _, _, .ret _ => []
    | _, _, .op key o _ _ rest => (if isEvent o then [key] else []) ++ Term.eventKeys isEvent rest
    | _, _, .guard _ _ _ _ _ rest => Term.eventKeys isEvent rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        Term.eventKeys isEvent onTrue ++ Term.eventKeys isEvent onFalse ++ Term.eventKeys isEvent rest
    | _, _, .cases _ _ _ _ _ arms _ rest => Arms.eventKeys isEvent arms ++ Term.eventKeys isEvent rest
    | _, _, .loop _ _ _ _ _ _ body _ rest => Term.eventKeys isEvent body ++ Term.eventKeys isEvent rest
    | _, _, .block _ _ body _ rest => Term.eventKeys isEvent body ++ Term.eventKeys isEvent rest
    | _, _, .attempt _ _ _ _ body _ rest => Term.eventKeys isEvent body ++ Term.eventKeys isEvent rest
  def Arms.eventKeys {D : Dialect} (isEvent : ∀ {ins res : List D.Ty}, D.Op ins res → Bool) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List Key
    | _, _, _, .nil => []
    | _, _, _, .cons _ arm rest => Term.eventKeys isEvent arm ++ Arms.eventKeys isEvent rest
end

/-- Whether an operation of a role is its part of an event. -/
def RoleOp.isEvent {V : Vocabulary} {hs : Headers V} {r : Role} {ins res : List (LTy V)} :
    RoleOp V hs r ins res → Bool
  | .give .. => true
  | .get .. => true
  | .own .. => true
  | .hear .. => true
  | _ => false

section
variable {V : Vocabulary}

/-- The scope of a deployment's retry: a declared retry is at an attempt of the entry's shape,
and every guard with `abort` of the shape is inside an attempt. -/
def Deployed.Scoped (d : Deployed V) : Prop :=
  (∀ bound site, d.declaration.retry = some (bound, site) → site ∈ d.entry.shape.attemptSites []) ∧
    d.entry.shape.abortsOutside [] false = []

/-- The keys of what the clauses of a deployment do: an event that a clause performs, other
than performing again the event that it answers, has a key that is no key of an event of the
entry. A lower layer matches effects by their sites, so no such event is taken for one of the
entry's. -/
def Deployed.Fresh (d : Deployed V) : Prop :=
  ∀ r, ∀ l, l ∈ d.stack r → ∀ c, c ∈ l.clauses →
    ∀ key, key ∈ Term.eventKeys (fun o => RoleOp.isEvent o) c.code → key ≠ c.site.site.key →
      key ∉ (d.entry.shape.events [] id).map (·.site.key)

end

end Zkc.Core
