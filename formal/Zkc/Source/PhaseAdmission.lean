import Zkc.Source.Region
import Zkc.Semantics.Boundary

/-! Source admission through checked abstract phase summaries.

The policy is chosen by the consumer. Its realization law quantifies over all
operation arguments and all interface-typed replies, not an honest execution.
Loop invariants are finite certificate data, checked without unrolling counts.
One checker traverses compact regions; tree programs use their sharing-preserving
embedding. Successful return summaries connect a shared body to its continuation.
This value-insensitive analysis is sufficient, not complete, for conformance.
-/

set_option autoImplicit false

namespace Zkc.Source.PhaseAdmission

variable {language : Language} {Phase : Type}

structure Policy (language : Language) (Phase : Type) where
  step : language.Op → Phase → Option (List Phase)

/-- Shape is checked against the actual source. Only loops carry phase annotations; bind retains continuation sharing. -/
inductive Certificate (Phase : Type) where
  | terminal
  | next (tail : Certificate Phase)
  | branch (yes no : Certificate Phase)
  | loop (invariant : List Phase) (body next : Certificate Phase)
  | bind (body next : Certificate Phase)
  deriving DecidableEq, Repr

variable [DecidableEq Phase]

def merge (left right : List Phase) : List Phase := (left ++ right).eraseDups

@[simp] theorem mem_merge (phase : Phase) (left right : List Phase) :
    phase ∈ merge left right ↔ phase ∈ left ∨ phase ∈ right := by
  simp [merge]

def stepMany (policy : Policy language Phase) (op : language.Op) :
    List Phase → Option (List Phase)
  | [] => some []
  | phase :: rest => do
    let first ← policy.step op phase
    let tail ← stepMany policy op rest
    return merge first tail

def checkRegion (policy : Policy language Phase) {Γ ty} :
    Region language Γ ty → Certificate Phase → List Phase → Option (List Phase)
  | .ret _, .terminal, phases => some phases
  | .stop _, .terminal, _ => some []
  | .letOp op _ next, .next certificate, phases => do
    let exits ← stepMany policy op phases
    checkRegion policy next certificate exits
  | .branch _ yes no, .branch yesCert noCert, phases => do
    let left ← checkRegion policy yes yesCert phases
    let right ← checkRegion policy no noCert phases
    return merge left right
  | .iterate _ _ body next, .loop invariant bodyCert nextCert, phases => do
    if !(phases.all (invariant.contains ·)) then none else do
      let exits ← checkRegion policy body bodyCert invariant
      if !(exits.all (invariant.contains ·)) then none else
        checkRegion policy next nextCert invariant
  | .bind body next, .bind bodyCert nextCert, phases => do
    let exits ← checkRegion policy body bodyCert phases
    checkRegion policy next nextCert exits
  | _, _, _ => none

variable {interface : PIR.Signature}

/-- A semantic obligation on resolved operations, separate from their signatures.
An absent summary is unsupported, not proof that the operation is illegal. -/
structure Realizes (policy : Policy language Phase)
    (meaning : Interpretation language interface) (interaction : PIR.Interaction interface) where
  relates : Phase → interaction.Phase → Prop
  operation : ∀ op before exits, policy.step op before = some exits →
    ∀ args phase, relates before phase →
      PIR.Conforms interaction (meaning.operation op args) phase ∧
      PIR.Boundary.Returns interaction (fun _ finish => ∃ after ∈ exits, relates after finish)
        (meaning.operation op args) phase

def Covered {policy : Policy language Phase} {meaning : Interpretation language interface}
    {interaction : PIR.Interaction interface} (laws : Realizes policy meaning interaction)
    (phases : List Phase) (phase : interaction.Phase) : Prop :=
  ∃ abstract ∈ phases, laws.relates abstract phase

theorem stepMany_sound (policy : Policy language Phase) (op : language.Op)
    (phases exits : List Phase) (accepted : stepMany policy op phases = some exits)
    (before : Phase) (member : before ∈ phases) :
    ∃ after, policy.step op before = some after ∧ ∀ phase ∈ after, phase ∈ exits := by
  induction phases generalizing exits with
  | nil => simp at member
  | cons phase rest ih =>
    cases first : policy.step op phase with
    | none => simp [stepMany, first] at accepted
    | some firstExits =>
      cases tail : stepMany policy op rest with
      | none => simp [stepMany, first, tail] at accepted
      | some tailExits =>
        simp [stepMany, first, tail] at accepted
        subst exits
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨firstExits, first, fun _ h => (mem_merge _ _ _).mpr (.inl h)⟩
        · obtain ⟨after, found, subset⟩ := ih tailExits tail member
          exact ⟨after, found, fun p h => (mem_merge _ _ _).mpr (.inr (subset p h))⟩

omit [DecidableEq Phase] in
theorem covered_mono {policy : Policy language Phase}
    {meaning : Interpretation language interface} {interaction : PIR.Interaction interface}
    (laws : Realizes policy meaning interaction) {left right : List Phase}
    (subset : ∀ p ∈ left, p ∈ right) {phase : interaction.Phase}
    (covered : Covered laws left phase) : Covered laws right phase := by
  obtain ⟨abstract, member, relates⟩ := covered
  exact ⟨abstract, subset abstract member, relates⟩

/-- Accepted certificates establish conformance and returning phase coverage for
every typed input environment. Halts impose no successful-return postcondition. -/
theorem checkRegion_sound (policy : Policy language Phase)
    (meaning : Interpretation language interface) (interaction : PIR.Interaction interface)
    (laws : Realizes policy meaning interaction) {Γ ty} (program : Region language Γ ty)
    (certificate : Certificate Phase) (starts exits : List Phase)
    (accepted : checkRegion policy program certificate starts = some exits)
    (env : Environment meaning.Value Γ) (phase : interaction.Phase)
    (initial : Covered laws starts phase) :
    PIR.Conforms interaction (program.denote meaning env) phase ∧
    PIR.Boundary.Returns interaction (fun _ finish => Covered laws exits finish)
      (program.denote meaning env) phase := by
  induction program generalizing certificate starts exits phase with
  | ret value =>
    cases certificate <;> simp [checkRegion] at accepted
    cases accepted
    exact ⟨trivial, initial⟩
  | stop reason =>
    cases certificate <;> simp [checkRegion] at accepted
    exact ⟨trivial, trivial⟩
  | letOp op arguments next ih =>
    cases certificate with
    | next cert =>
      cases steps : stepMany policy op starts with
      | none => simp [checkRegion, steps] at accepted
      | some after =>
        simp [checkRegion, steps] at accepted
        obtain ⟨before, member, relates⟩ := initial
        obtain ⟨outputs, summary, subset⟩ := stepMany_sound policy op starts after steps before member
        have opLaw := laws.operation op before outputs summary (Operands.eval env arguments) phase relates
        have returns := PIR.Boundary.returns_mono interaction _ _
          (fun _ p => Covered laws after p) phase opLaw.2
          (fun _ _ h => covered_mono laws subset h)
        exact ⟨PIR.Boundary.conforms_bind interaction _ _ _ phase opLaw.1 returns
          (fun value p h => (ih cert after exits accepted (env.push value) p h).1),
          PIR.Boundary.returns_bind interaction _ _ _ _ phase returns
          (fun value p h => (ih cert after exits accepted (env.push value) p h).2)⟩
    | _ => simp [checkRegion] at accepted
  | branch condition yes no yesIH noIH =>
    cases certificate with
    | branch yesCert noCert =>
      cases left : checkRegion policy yes yesCert starts with
      | none => simp [checkRegion, left] at accepted
      | some leftExits =>
        cases right : checkRegion policy no noCert starts with
        | none => simp [checkRegion, left, right] at accepted
        | some rightExits =>
          simp [checkRegion, left, right] at accepted
          subst exits
          simp only [Region.denote]
          split
          · have result := yesIH yesCert starts leftExits left env phase initial
            exact ⟨result.1, PIR.Boundary.returns_mono interaction _ _ _ phase result.2
              (fun _ _ h => covered_mono laws (fun _ h => (mem_merge _ _ _).mpr (.inl h)) h)⟩
          · have result := noIH noCert starts rightExits right env phase initial
            exact ⟨result.1, PIR.Boundary.returns_mono interaction _ _ _ phase result.2
              (fun _ _ h => covered_mono laws (fun _ h => (mem_merge _ _ _).mpr (.inr h)) h)⟩
    | _ => simp [checkRegion] at accepted
  | iterate count initialValue body next bodyIH nextIH =>
    cases certificate with
    | loop invariant bodyCert nextCert =>
      simp only [checkRegion] at accepted
      split at accepted
      · contradiction
      · rename_i entry
        have entrySubset : ∀ p ∈ starts, p ∈ invariant := by simpa using entry
        cases bodyChecked : checkRegion policy body bodyCert invariant with
        | none => simp [bodyChecked] at accepted
        | some bodyExits =>
          simp [bodyChecked] at accepted
          obtain ⟨bodySubset, accepted⟩ := accepted
          have loopLaw := PIR.Boundary.repeat_formed interaction
            (fun value => body.denote meaning (env.push value))
            (fun _ p => Covered laws invariant p)
            (fun value p h => (bodyIH bodyCert invariant bodyExits bodyChecked (env.push value) p h).1)
            (fun value p h => PIR.Boundary.returns_mono interaction _ _ _ p
              (bodyIH bodyCert invariant bodyExits bodyChecked (env.push value) p h).2
              (fun _ _ h => covered_mono laws bodySubset h))
            count (env initialValue) phase (covered_mono laws entrySubset initial)
          exact ⟨PIR.Boundary.conforms_bind interaction _ _ _ phase loopLaw.1 loopLaw.2
            (fun value p h => (nextIH nextCert invariant exits accepted (env.push value) p h).1),
            PIR.Boundary.returns_bind interaction _ _ _ _ phase loopLaw.2
            (fun value p h => (nextIH nextCert invariant exits accepted (env.push value) p h).2)⟩
    | _ => simp [checkRegion] at accepted

  | bind body next bodyIH nextIH =>
    cases certificate with
    | bind bodyCert nextCert =>
      cases bodyChecked : checkRegion policy body bodyCert starts with
      | none => simp [checkRegion, bodyChecked] at accepted
      | some middle =>
        simp [checkRegion, bodyChecked] at accepted
        have first := bodyIH bodyCert starts middle bodyChecked env phase initial
        exact ⟨PIR.Boundary.conforms_bind interaction _ _ _ phase first.1 first.2
          (fun value p h => (nextIH nextCert middle exits accepted (env.push value) p h).1),
          PIR.Boundary.returns_bind interaction _ _ _ _ phase first.2
          (fun value p h => (nextIH nextCert middle exits accepted (env.push value) p h).2)⟩
    | _ => simp [checkRegion] at accepted

/-- Tree admission reuses the compact checker without flattening continuations. -/
def check (policy : Policy language Phase) {Γ ty} (program : Program language Γ ty)
    (certificate : Certificate Phase) (starts : List Phase) : Option (List Phase) :=
  checkRegion policy program.toRegion certificate starts

theorem check_sound (policy : Policy language Phase)
    (meaning : Interpretation language interface) (interaction : PIR.Interaction interface)
    (laws : Realizes policy meaning interaction) {Γ ty} (program : Program language Γ ty)
    (certificate : Certificate Phase) (starts exits : List Phase)
    (accepted : check policy program certificate starts = some exits)
    (env : Environment meaning.Value Γ) (phase : interaction.Phase)
    (initial : Covered laws starts phase) :
    PIR.Conforms interaction (program.denote meaning env) phase ∧
    PIR.Boundary.Returns interaction (fun _ finish => Covered laws exits finish)
      (program.denote meaning env) phase := by
  simpa only [Program.denote_toRegion] using
    checkRegion_sound policy meaning interaction laws program.toRegion certificate starts exits
      accepted env phase initial

end Zkc.Source.PhaseAdmission

namespace Zkc.Source.PhaseAdmission

variable {language : Language} {Phase : Type} [DecidableEq Phase]

/-- Evidence is indexed by the consumer's entry and permitted return phases. -/
structure Admitted (policy : Policy language Phase) {Γ ty}
    (program : Program language Γ ty) (starts allowed : List Phase) where
  certificate : Certificate Phase
  exits : List Phase
  accepted : check policy program certificate starts = some exits
  permitted : ∀ phase ∈ exits, phase ∈ allowed

def admit (policy : Policy language Phase) {Γ ty} (program : Program language Γ ty)
    (certificate : Certificate Phase) (starts allowed : List Phase) :
    Option (Admitted policy program starts allowed) :=
  match accepted : check policy program certificate starts with
  | none => none
  | some exits =>
    if permitted : ∀ phase ∈ exits, phase ∈ allowed then
      some ⟨certificate, exits, accepted, permitted⟩
    else none

theorem Admitted.sound {policy : Policy language Phase} {Γ ty}
    {program : Program language Γ ty} {starts allowed : List Phase}
    (admitted : Admitted policy program starts allowed)
    {interface : PIR.Signature} (meaning : Interpretation language interface)
    (interaction : PIR.Interaction interface) (laws : Realizes policy meaning interaction)
    (env : Environment meaning.Value Γ) (phase : interaction.Phase)
    (initial : Covered laws starts phase) :
    PIR.Conforms interaction (program.denote meaning env) phase ∧
    PIR.Boundary.Returns interaction (fun _ finish => Covered laws allowed finish)
      (program.denote meaning env) phase := by
  have result := check_sound policy meaning interaction laws program admitted.certificate
    starts admitted.exits admitted.accepted env phase initial
  exact ⟨result.1, PIR.Boundary.returns_mono interaction _ _ _ phase result.2
    (fun _ _ h => covered_mono laws admitted.permitted h)⟩

end Zkc.Source.PhaseAdmission
