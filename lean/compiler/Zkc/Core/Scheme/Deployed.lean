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

/-- A deployed scheme: the admitted program, the declaration, that the declaration's entry is a
protocol of the program, and each role's handlers in order, the nearest to its program first.
The entry and its reference are found from the declaration (`Deployed.entry`,
`Deployed.callee`). -/
structure Deployed (V : Vocabulary) where
  admitted : Admitted V
  declaration : Declaration
  found : (admitted.program.findProtocol declaration.entry).isSome
  stack : (r : Role) →
    List (Layer V admitted.program.headers r
      ((admitted.program.findProtocol declaration.entry).get found).1.ins)

section
variable {V : Vocabulary}

/-- The entry of a deployment: the protocol of the program that its declaration names. -/
def Deployed.entry (d : Deployed V) : ProtocolHeader V :=
  ((d.admitted.program.findProtocol d.declaration.entry).get d.found).1

/-- The reference of the entry among the protocols of the program. -/
def Deployed.callee (d : Deployed V) : Member d.admitted.program.headers.protocols d.entry :=
  ((d.admitted.program.findProtocol d.declaration.entry).get d.found).2

/-- The entry of a deployment has the key that its declaration names. -/
theorem Deployed.entry_key (d : Deployed V) : d.entry.key = d.declaration.entry :=
  Typed.findProtocol_key (Option.some_get d.found).symm

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
    | .derived suite _ => suite.definitions
    | .authored => []) ++
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
  /-- Whether `target` never occurs inside the body of an `.attempt` at `target`.
  Holds for every standard scheme (including attempts inside loops, choices, and sub-protocols). -/
  def Shape.noNestedAttempt {V : Vocabulary} (target : Site) (through : List Key) : Shape V → Bool
    | .nil => true
    | .event _ _ _ rest => Shape.noNestedAttempt target through rest
    | .choice _ _ arms rest =>
        Shapes.noNestedAttempt target through arms && Shape.noNestedAttempt target through rest
    | .loop _ _ body rest =>
        Shape.noNestedAttempt target through body && Shape.noNestedAttempt target through rest
    | .apply key _ _ inner rest =>
        Shape.noNestedAttempt target (through ++ [key]) inner && Shape.noNestedAttempt target through rest
    | .block _ _ body rest =>
        Shape.noNestedAttempt target through body && Shape.noNestedAttempt target through rest
    | .guard _ _ _ rest => Shape.noNestedAttempt target through rest
    | .attempt key _ body rest =>
        (if ⟨through, key⟩ = target then !decide (target ∈ body.attemptSites through) else true) &&
        Shape.noNestedAttempt target through body &&
        Shape.noNestedAttempt target through rest

  def Shapes.noNestedAttempt {V : Vocabulary} (target : Site) (through : List Key) : Shapes V → Bool
    | .nil => true
    | .cons arm rest =>
        Shape.noNestedAttempt target through arm && Shapes.noNestedAttempt target through rest
end

/-- Whether a protocol shape is straight-line (contains no `.choice` or `.loop`), so every wire
site in `events` executes at most once in fixed order and can be pre-parsed by a compact layout. -/
def Shape.isStraightLine {V : Vocabulary} : Shape V → Bool
  | .nil => true
  | .event _ _ _ rest => rest.isStraightLine
  | .choice _ _ _ _ => false
  | .loop _ _ _ _ => false
  | .apply _ _ _ inner rest => inner.isStraightLine && rest.isStraightLine
  | .block _ _ body rest => body.isStraightLine && rest.isStraightLine
  | .guard _ _ _ rest => rest.isStraightLine
  | .attempt _ _ body rest => body.isStraightLine && rest.isStraightLine

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

/-! ## Coverage and semantic laws of deployed suite and layout modules -/

/-- A role process asks the world only its own private coins (`hearers = []`), requests to
services, and local attempt marks: no peer flows (`.give`, `.get`), no heard events (`.hear`),
and no public coins (`.own (.coin _) (_ :: _)`). -/
def Process.ClosedEffects {M : Model V} {H A : Type} : Process (RSig M) H A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k =>
      (match op with
       | .own (.coin _) [] _ _ _ _ => True
       | .own (.request _) _ _ _ _ _ => True
       | .begin _ => True
       | .settle _ => True
       | _ => False) ∧
      ∀ reply, Process.ClosedEffects (k reply)

/-- Every online role of a non-interactive deployment under its stack asks the world only its own
private coins, service requests, and local attempt marks. -/
def Deployed.Covered (d : Deployed V) : Prop :=
  ∀ (M : Model V) (prover verifier : Role), d.roles = some (prover, verifier) →
    ∀ r, (r = prover ∨ r = verifier) →
      ∀ (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))),
        ins.All (RV.Valid M r) → taken.All M.Valid →
        Process.ClosedEffects (d.run M r ins taken)

/-- A deployment's declared retry site (if any) does not nest inside itself.
Vacuously satisfied whenever `d.retry = none`. -/
def Deployed.WellNestedRetry (d : Deployed V) : Prop :=
  ∀ bound site, d.retry = some (bound, site) → Shape.noNestedAttempt site [] d.entry.shape = true

/-- The Fiat-Shamir suite of a deployment satisfies its semantic laws in model `M`:
1. Every derived coin emitted by a `SuiteSlot.derive` function on valid inputs lies in the support
   of the drawn coin's law (`Allows M (.coin law)`).
2. Every `SuiteSlot.encode` function is injective on valid values (collision-free message framing).
Determinism, validity preservation, and non-halting already follow from admission. -/
def Deployed.SuiteLawful (M : Model V) (d : Deployed V) : Prop :=
  match d.declaration.construction with
  | .derived suite _ =>
      (∀ defKey, (SuiteSlot.derive, defKey) ∈ suite.members →
        ∀ (hdr : FnHeader V) (f : Member d.admitted.program.headers.fns hdr),
          d.admitted.program.find defKey = some (.fn f) →
          ∀ (stateTy : V.Ty) (drawIns : List V.Ty) (e : ShapeEvent V)
            (law : V.LawKey) (owner : Role) (h0 : Role) (hs : List Role),
            e ∈ d.entry.shape.events [] id →
            e.cls = .given (.coin law) owner (h0 :: hs) →
            V.law law = some ⟨drawIns, e.τ⟩ →
            ∀ (hins : hdr.ins = stateTy :: .seq (.fin 256) none :: drawIns)
              (houts : hdr.outs = [e.τ, stateTy])
              (st : M.Val stateTy) (label : List (M.Val (.fin 256)))
              (payload : HList M.Val drawIns) (coin : M.Val e.τ) (st' : M.Val stateTy),
              M.Valid stateTy st →
              (∀ b, b ∈ label → b < 256) →
              payload.All M.Valid →
              Defs.fnTable M d.admitted.program.defs hdr f
                (cast (congrArg (HList M.Val) hins.symm) (.cons st (.cons label payload))) =
                .done (cast (congrArg (HList M.Val) houts.symm) (.cons coin (.cons st' .nil))) →
              Allows M (.coin law) drawIns payload e.τ coin) ∧
      (∀ eKey, (SuiteSlot.encode, eKey) ∈ suite.members →
        ∀ (hdr : FnHeader V) (f : Member d.admitted.program.headers.fns hdr),
          d.admitted.program.find eKey = some (.fn f) →
          ∀ (unitTy τ : V.Ty) (hIn : hdr.ins = [τ]) (hOut : hdr.outs = [.seq unitTy none])
            (v₁ v₂ : M.Val τ) (u : List (M.Val unitTy)),
            M.Valid τ v₁ → M.Valid τ v₂ →
            Defs.fnTable M d.admitted.program.defs hdr f
              (cast (congrArg (HList M.Val) hIn.symm) (.cons v₁ .nil)) =
              .done (cast (congrArg (HList M.Val) hOut.symm) (.cons u .nil)) →
            Defs.fnTable M d.admitted.program.defs hdr f
              (cast (congrArg (HList M.Val) hIn.symm) (.cons v₂ .nil)) =
              .done (cast (congrArg (HList M.Val) hOut.symm) (.cons u .nil)) →
            v₁ = v₂)
  | _ => True

/-- The proof layout of a deployment satisfies its canonical codec laws (round-trip, non-malleable
canonical decoding, and exact equality) in model `M`:
1. `reads`: every `(LayoutSlot.write, LayoutSlot.read)` pair round-trips on any valid value `v`
   embedded between valid unit sequences `pre` and `post`.
2. `written`: every successful `LayoutSlot.read (buf, off) = .done (v, nextOff)` on valid `buf`
   with `off ≤ buf.length` returns a valid value `v` and cursor `off ≤ nextOff ≤ buf.length` whose
   consumed slice equals `LayoutSlot.write v` (canonicality / non-malleability).
3. `equal_iff`: every `LayoutSlot.equal` decides equality on valid values (`true ↔ v₁ = v₂`). -/
def Deployed.LayoutLawful (M : Model V) (d : Deployed V) : Prop :=
  match d.declaration.layout with
  | none => True
  | some layout =>
      (∀ wKey rKey,
        (LayoutSlot.write, wKey) ∈ layout.module.members →
        (LayoutSlot.read, rKey) ∈ layout.module.members →
        ∀ (wHdr rHdr : FnHeader V)
          (fW : Member d.admitted.program.headers.fns wHdr)
          (fR : Member d.admitted.program.headers.fns rHdr),
          d.admitted.program.find wKey = some (.fn fW) →
          d.admitted.program.find rKey = some (.fn fR) →
          ∀ (unitTy τ : V.Ty)
            (hwIn : wHdr.ins = [τ]) (hwOut : wHdr.outs = [.seq unitTy none])
            (hrIn : rHdr.ins = [.seq unitTy none, .nat]) (hrOut : rHdr.outs = [τ, .nat])
            (v : M.Val τ) (chunk pre post : List (M.Val unitTy)),
            M.Valid τ v →
            (∀ u, u ∈ pre → M.Valid unitTy u) →
            (∀ u, u ∈ post → M.Valid unitTy u) →
            Defs.fnTable M d.admitted.program.defs wHdr fW
              (cast (congrArg (HList M.Val) hwIn.symm) (.cons v .nil)) =
              .done (cast (congrArg (HList M.Val) hwOut.symm) (.cons chunk .nil)) →
            Defs.fnTable M d.admitted.program.defs rHdr fR
              (cast (congrArg (HList M.Val) hrIn.symm)
                (.cons (pre ++ chunk ++ post) (.cons pre.length .nil))) =
              .done (cast (congrArg (HList M.Val) hrOut.symm)
                (.cons v (.cons (pre.length + chunk.length) .nil)))) ∧
      (∀ wKey rKey,
        (LayoutSlot.write, wKey) ∈ layout.module.members →
        (LayoutSlot.read, rKey) ∈ layout.module.members →
        ∀ (wHdr rHdr : FnHeader V)
          (fW : Member d.admitted.program.headers.fns wHdr)
          (fR : Member d.admitted.program.headers.fns rHdr),
          d.admitted.program.find wKey = some (.fn fW) →
          d.admitted.program.find rKey = some (.fn fR) →
          ∀ (unitTy τ : V.Ty)
            (hwIn : wHdr.ins = [τ]) (hwOut : wHdr.outs = [.seq unitTy none])
            (hrIn : rHdr.ins = [.seq unitTy none, .nat]) (hrOut : rHdr.outs = [τ, .nat])
            (buf : List (M.Val unitTy)) (off : Nat) (v : M.Val τ) (nextOff : Nat),
            (∀ u, u ∈ buf → M.Valid unitTy u) →
            off ≤ buf.length →
            Defs.fnTable M d.admitted.program.defs rHdr fR
              (cast (congrArg (HList M.Val) hrIn.symm) (.cons buf (.cons off .nil))) =
              .done (cast (congrArg (HList M.Val) hrOut.symm) (.cons v (.cons nextOff .nil))) →
            M.Valid τ v ∧ off ≤ nextOff ∧ nextOff ≤ buf.length ∧
            ∃ chunk,
              Defs.fnTable M d.admitted.program.defs wHdr fW
                (cast (congrArg (HList M.Val) hwIn.symm) (.cons v .nil)) =
                .done (cast (congrArg (HList M.Val) hwOut.symm) (.cons chunk .nil)) ∧
              buf = buf.take off ++ chunk ++ buf.drop nextOff) ∧
      (∀ eqKey,
        (LayoutSlot.equal, eqKey) ∈ layout.module.members →
        ∀ (eqHdr : FnHeader V) (fEq : Member d.admitted.program.headers.fns eqHdr),
          d.admitted.program.find eqKey = some (.fn fEq) →
          ∀ (τ : V.Ty) (hIn : eqHdr.ins = [τ, τ]) (hOut : eqHdr.outs = [.bool])
            (v₁ v₂ : M.Val τ) (b : Bool),
            M.Valid τ v₁ → M.Valid τ v₂ →
            Defs.fnTable M d.admitted.program.defs eqHdr fEq
              (cast (congrArg (HList M.Val) hIn.symm) (.cons v₁ (.cons v₂ .nil))) =
              .done (cast (congrArg (HList M.Val) hOut.symm) (.cons b .nil)) →
            (b = true ↔ v₁ = v₂))

/-- Answer every `.own (.request service)` effect of a role process using `oracle`, leaving all
other effects untouched. Used to evaluate a deployed ideal verifier against an abstract random
oracle. -/
def Process.answerService {M : Model V} {H A : Type} (service : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ)) :
    Process (RSig M) H A → Process (RSig M) H A
  | .done a => .done a
  | .halt h => .halt h
  | .call (.own (.request svc) hearers at_ ins payload τ) k =>
      if svc = service then
        match oracle ins payload τ with
        | some v => Process.answerService service oracle (k v)
        | none => .call (.own (.request svc) hearers at_ ins payload τ)
            fun v => Process.answerService service oracle (k v)
      else
        .call (.own (.request svc) hearers at_ ins payload τ)
          fun v => Process.answerService service oracle (k v)
  | .call op k => .call op fun reply => Process.answerService service oracle (k reply)

end

end Zkc.Core
