module

public import Zkc.Core.Facts.Body.AttemptSound
public import Zkc.Core.Facts.Body.LoopSound

@[expose] public section

/-!
The three properties of every term, every instruction and every arms (`WalkGrowsStatement`,
`WalkRunsStatement`, `WalkSoundStatement`), each by one mutual induction over the term in steps
from the statements per kind of instruction; soundness for a prefix (`PrefixSoundStatement`); and a
term as a prefix and an exit (`WalkFillStatement`, `ToPrefixFillStatement`,
`TermFromPrefixStatement`).

The induction of growth comes first: the statements per kind about running the skeleton and
soundness take the growth of the regions as hypotheses, and those are given by it.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## The walk grows the state -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

mutual
  /-- **The walk of every term grows the state.** -/
  theorem termGrows : ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
      (t : Term D Γ outs), TermGrows cfg notes cursor t
    | cursor, _, _, .ret exit => retGrows cfg notes cursor exit
    | cursor, _, _, .step key i results rest =>
        stepGrows cfg notes cursor key i results rest (instrGrows cursor key i)
          (termGrows cursor.next rest)
  /-- **The walk of every instruction grows the state.** -/
  theorem instrGrows : ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
      (i : Instr D Γ mid), InstrGrows cfg notes cursor key i
    | cursor, key, _, _, .op o operands => opGrows cfg notes cursor key o operands
    | cursor, key, _, _, .guard w c ok why => guardGrows cfg notes cursor key w c ok why
    | cursor, key, _, _, .choose w c ok gives onTrue onFalse =>
        chooseGrows cfg notes cursor key w c ok gives onTrue onFalse (termGrows (cursor.region key) onTrue)
          (termGrows (cursor.otherwise key) onFalse)
    | cursor, key, _, _, .cases w x ok gives arms =>
        casesGrows cfg notes cursor key w x ok gives arms (armsGrows (cursor.region key) arms)
    | cursor, key, _, _, .loop w times gives initial inputs body =>
        loopGrows cfg notes cursor key w times gives initial inputs body (termGrows (cursor.region key) body)
    | cursor, key, _, _, .block number body =>
        blockGrows cfg notes cursor key number body (termGrows (cursor.block key number) body)
    | cursor, key, _, _, .attempt w owns inputs body =>
        attemptGrows cfg notes cursor key w owns inputs body (termGrows (cursor.region key) body)
  /-- **The walk of every arms grows the state.** -/
  theorem armsGrows : ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads), ArmsGrows cfg notes cursor arms
    | cursor, _, _, _, .nil => armsNilGrows cfg notes cursor
    | cursor, _, _, _, .cons inputs arm rest =>
        armsConsGrows cfg notes cursor inputs arm rest (termGrows cursor.arm arm) (armsGrows cursor.next rest)
end

/-- **The walk grows the state**, for every term. -/
theorem walkGrows : WalkGrowsStatement cfg notes :=
  termGrows cfg notes

end

/-! ## Every term runs its skeleton -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) (laws : σ.ValueLaws)

set_option linter.unusedSectionVars false in
include laws in
mutual
  /-- **Every term runs its skeleton.** -/
  theorem termRuns : ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
      (t : Term D Γ outs), TermRuns σ cursor t
    | cursor, _, _, .ret exit => retRuns σ laws cursor exit
    | cursor, _, _, .step key i results rest =>
        stepRuns σ laws cursor key i results rest (instrGrows σ.cfg σ.notes cursor key i)
          (termGrows σ.cfg σ.notes cursor.next rest) (instrRuns cursor key i) (termRuns cursor.next rest)
  /-- **What every instruction runs runs its entry of the skeleton.** -/
  theorem instrRuns : ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
      (i : Instr D Γ mid), InstrRuns σ cursor key i
    | cursor, key, _, _, .op o operands => opRuns σ laws cursor key o operands
    | cursor, key, _, _, .guard w c ok why => guardRuns σ cursor key w c ok why
    | cursor, key, _, _, .choose w c ok gives onTrue onFalse =>
        chooseRuns σ laws cursor key w c ok gives onTrue onFalse
          (termGrows σ.cfg σ.notes (cursor.region key) onTrue) (termGrows σ.cfg σ.notes (cursor.otherwise key) onFalse)
          (termRuns (cursor.region key) onTrue) (termRuns (cursor.otherwise key) onFalse)
    | cursor, key, _, _, .cases w x ok gives arms =>
        casesRuns σ cursor key w x ok gives arms (armsGrows σ.cfg σ.notes (cursor.region key) arms)
          (armsRuns (cursor.region key) arms)
    | cursor, key, _, _, .loop w times gives initial inputs body =>
        loopRuns σ laws cursor key w times gives initial inputs body
          (termGrows σ.cfg σ.notes (cursor.region key) body) (termRuns (cursor.region key) body)
    | cursor, key, _, _, .block number body =>
        blockRuns σ cursor key number body (termRuns (cursor.block key number) body)
    | cursor, key, _, _, .attempt w owns inputs body =>
        attemptRuns σ cursor key w owns inputs body (termGrows σ.cfg σ.notes (cursor.region key) body)
          (termRuns (cursor.region key) body)
  /-- **Every arms run their skeletons.** -/
  theorem armsRuns : ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads), ArmsRuns σ cursor arms
    | cursor, _, _, _, .nil => armsNilRuns σ cursor
    | cursor, _, _, _, .cons inputs arm rest =>
        armsConsRuns σ cursor inputs arm rest (termGrows σ.cfg σ.notes cursor.arm arm)
          (armsGrows σ.cfg σ.notes cursor.next rest) (termRuns cursor.arm arm) (armsRuns cursor.next rest)
end

end

/-- **Every term runs its skeleton.** -/
theorem walkRuns {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) :
    WalkRunsStatement σ :=
  fun laws => termRuns σ laws

/-! ## The walk is sound -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) (laws : σ.Lawful)

set_option linter.unusedSectionVars false in
include laws in
mutual
  /-- **The walk of every term is sound.** -/
  theorem termSound : ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
      (t : Term D Γ outs), TermSound σ cursor t
    | cursor, _, _, .ret exit => retSound σ laws cursor exit
    | cursor, _, _, .step key i results rest =>
        stepSound σ laws cursor key i results rest (instrGrows σ.cfg σ.notes cursor key i)
          (termGrows σ.cfg σ.notes cursor.next rest) (instrSound cursor key i) (termSound cursor.next rest)
  /-- **The walk of every instruction is sound.** -/
  theorem instrSound : ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
      (i : Instr D Γ mid), InstrSound σ cursor key i
    | cursor, key, _, _, .op o operands => opSound σ laws laws cursor key o operands
    | cursor, key, _, _, .guard w c ok why => guardSound σ laws cursor key w c ok why
    | cursor, key, _, _, .choose w c ok gives onTrue onFalse =>
        chooseSound σ laws cursor key w c ok gives onTrue onFalse
          (termGrows σ.cfg σ.notes (cursor.region key) onTrue) (termGrows σ.cfg σ.notes (cursor.otherwise key) onFalse)
          (termSound (cursor.region key) onTrue) (termSound (cursor.otherwise key) onFalse)
    | cursor, key, _, _, .cases w x ok gives arms =>
        casesSound σ laws cursor key w x ok gives arms (armsGrows σ.cfg σ.notes (cursor.region key) arms)
          (armsSound (cursor.region key) arms)
    | cursor, key, _, _, .loop w times gives initial inputs body =>
        loopSound σ laws cursor key w times gives initial inputs body
          (termGrows σ.cfg σ.notes (cursor.region key) body) (termSound (cursor.region key) body)
    | cursor, key, _, _, .block number body =>
        blockSound σ laws cursor key number body
          (termGrows σ.cfg σ.notes (cursor.block key number) body)
          (termSound (cursor.block key number) body)
    | cursor, key, _, _, .attempt w owns inputs body =>
        attemptSound σ laws cursor key w owns inputs body (termGrows σ.cfg σ.notes (cursor.region key) body)
          (termSound (cursor.region key) body)
  /-- **The walk of every arms is sound.** -/
  theorem armsSound : ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads), ArmsSound σ cursor arms
    | cursor, _, _, _, .nil => armsNilSound σ cursor
    | cursor, _, _, _, .cons inputs arm rest =>
        armsConsSound σ cursor inputs arm rest (termGrows σ.cfg σ.notes cursor.arm arm)
          (armsGrows σ.cfg σ.notes cursor.next rest) (termSound cursor.arm arm) (armsSound cursor.next rest)
end

end

/-- **The walk is sound**, for every term. -/
theorem walkSound {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) :
    WalkSoundStatement σ :=
  fun laws => termSound σ laws

/-! ## A prefix -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- **The walk of a prefix grows the table**, keeps its values well formed, and only adds refusals
before those that were there. -/
theorem walkPrefix_grew (cursor : StaticCursor) :
    ∀ {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State),
      s.values.WF →
      s.values.table.Le (walkPrefix cfg notes cursor p ids s k).state.values.table ∧
        (walkPrefix cfg notes cursor p ids s k).state.values.WF ∧
        ∃ new, (walkPrefix cfg notes cursor p ids s k).state.refusals = new ++ s.refusals
  | _, _, .nil, _, s, _, wf => ⟨Table.Le.refl _, wf, [], rfl⟩
  | _, _, .step key i results rest, ids, s, k, wf => by
      have one := instrGrows cfg notes cursor key i ids s k wf
      obtain ⟨table, wf', refusals⟩ := walkPrefix_grew cursor.next rest
        (bindIds ids results (walkInstr cfg notes cursor key i ids s k).returned)
        (walkInstr cfg notes cursor key i ids s k).state
        (walkInstr cfg notes cursor key i ids s k).known one.2.1
      exact ⟨one.1.trans table, wf', refusals_trans one.2.2.2.2.1 refusals⟩

end

/-- The process of a prefix of one more step: the instruction's, then the rest's on what it
returns. -/
theorem Prefix.run_step {D : Dialect} (sem : Semantics D) {Γ Δ : Ctx D.Ty} {mid : List D.Ty}
    (key : Key) (i : Instr D Γ mid) (results : Names mid)
    (rest : Prefix D (Γ.extend results) Δ) (path : List Frame) (env : Env sem.Val Γ) :
    (Prefix.step key i results rest).run sem path env =
      (i.denote sem key path env).bind fun values => rest.run sem path (env.extend results values) :=
  rfl

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **Soundness for a prefix**: by induction on the prefix, each instruction sound
(`instrSound`), its results bound to its names (`Scope.bind`), and the rest sound from there. -/
theorem prefixSound : PrefixSoundStatement σ := by
  intro laws cursor Γ Δ p
  induction p generalizing cursor with
  | nil =>
      intro path ρ ids env s k
      dsimp only
      intro inv _ _ _
      exact ⟨ρ, fun _ _ h => h, inv⟩
  | step key i results rest ih =>
      intro path ρ ids env s k
      dsimp only
      intro inv defined facts unchanged
      obtain ⟨steps, definedI, definedR⟩ := defined
      obtain ⟨factsI, everyFactI, factsR⟩ := facts
      simp only [walkPrefix] at unchanged ⊢
      have one := instrGrows σ.cfg σ.notes cursor key i ids s k inv.wf
      have soundOne := instrSound σ laws cursor key i path ρ ids env s k inv steps definedI factsI
        everyFactI
      have restGrew := walkPrefix_grew σ.cfg σ.notes cursor.next rest
        (bindIds ids results (walkInstr σ.cfg σ.notes cursor key i ids s k).returned)
        (walkInstr σ.cfg σ.notes cursor key i ids s k).state
        (walkInstr σ.cfg σ.notes cursor key i ids s k).known one.2.1
      have soundRest := fun ρ₁ env₁ => ih cursor.next path ρ₁
        (bindIds ids results (walkInstr σ.cfg σ.notes cursor key i ids s k).returned) env₁
        (walkInstr σ.cfg σ.notes cursor key i ids s k).state
        (walkInstr σ.cfg σ.notes cursor key i ids s k).known
      generalize walkInstr σ.cfg σ.notes cursor key i ids s k = first
        at one soundOne restGrew soundRest unchanged ⊢
      generalize walkPrefix σ.cfg σ.notes cursor.next rest (bindIds ids results first.returned)
        first.state first.known = after at restGrew soundRest unchanged ⊢
      obtain ⟨firstUnchanged, afterUnchanged⟩ :=
        refusals_split one.2.2.2.2.1 restGrew.2.2 unchanged
      obtain ⟨every, -, -, -⟩ := soundOne firstUnchanged
      rw [Prefix.run_step, Process.every_bind]
      refine Process.every_mono _ _ (fun values both => ?_) (fun _ h => h.1)
        (Process.every_and _ _ every factsR)
      obtain ⟨⟨ρ₁, le, inv₁, reads⟩, factsRest⟩ := both
      refine Process.every_mono _ _ (fun env' found => ?_) (fun _ h => h)
        (soundRest ρ₁ (env.extend results values)
          ⟨inv₁.toScope.bind results first.returned values reads, inv₁.valid, inv₁.means⟩
          definedR factsRest afterUnchanged)
      obtain ⟨ρ₂, le₂, inv₂⟩ := found
      exact ⟨ρ₂, fun n v h => le₂ n v (le n v h), inv₂⟩

/-- Every run from an authorized entry that reaches the end of the prefix satisfies the
invariant of its analysed exit, for any term that fills the place. -/
theorem prefixFact (laws : σ.Lawful) (cursor : StaticCursor) {Γ Δ : Ctx D.Ty}
    {outs : List D.Ty} (p : Prefix D Γ Δ) (filling : Term D Δ outs)
    (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (s : State Raw) (k : σ.cfg.domain.State)
    (defined : Prefix.AnnotationsDefined σ cursor p)
    (accepted : (walkPrefix σ.cfg σ.notes cursor p ids s k).state.refusals = s.refusals) :
    let e := walkPrefix σ.cfg σ.notes cursor p ids s k
    Fact σ.sem σ.permitted p.hole filling
      (fun path env => Inv σ ρ ids env k s ∧ Prefix.EveryFact σ cursor p path env)
      (fun _ env' => ∃ ρ', ρ.Le ρ' ∧ Inv σ ρ' e.ids env' e.known e.state) := by
  dsimp only
  intro path env entry path' env' reached
  have sound := prefixSound σ laws cursor p path ρ ids env s k entry.1 defined entry.2 accepted
  exact sound.canReturn (p.return_of_reaches σ.sem σ.permitted filling path env path' env' reached).2

/-- An instruction's entry of the skeleton before entries, as the entries with that one first. -/
theorem Skel.stepOf_ofEntries {outs : List D.Ty} (key : Key) (entry : Option (Kept D))
    (entries : List (Key × Kept D)) (rest : Skel D outs) :
    Skel.stepOf key entry (Skel.ofEntries entries rest) =
      Skel.ofEntries ((entry.map fun kept => (key, kept)).toList ++ entries) rest := by
  cases entry <;> rfl

/-- **The walk of a prefix filled with a term** is the walk of the prefix, then of the term. -/
theorem walkFill : WalkFillStatement σ := by
  intro cursor Γ Δ outs p t
  induction p generalizing cursor with
  | nil => intro ids s k; rfl
  | step key i results rest ih =>
      intro ids s k
      dsimp only at ih ⊢
      simp only [Prefix.fill, walk, walkPrefix, Prefix.afterCursor, ih, Skel.stepOf_ofEntries]

end

/-- **A term is its prefix filled with its exit.** -/
theorem Term.toPrefix_fill {D : Dialect} : ∀ {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs),
    (Term.toPrefix t).2.1.fill (.ret (Term.toPrefix t).2.2) = t
  | _, _, .ret _ => rfl
  | _, _, .step key i results rest =>
      congrArg (Term.step key i results) (Term.toPrefix_fill rest)

/-- **A term is its prefix filled with its exit.** -/
theorem toPrefixFill {D : Dialect} : ToPrefixFillStatement (D := D) :=
  fun t => Term.toPrefix_fill t

section
variable {D : Dialect} {Raw : Type}

/-- The decided assertions of a prefix filled with a term are defined where those of the prefix
are. -/
theorem Prefix.annotationsDefined_of_fill {σ : Setting D Raw} {cursor : StaticCursor} :
    ∀ {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) {outs : List D.Ty} (t : Term D Δ outs),
      Term.AnnotationsDefined σ cursor (p.fill t) → Prefix.AnnotationsDefined σ cursor p
  | _, _, .nil, _, _, _ => trivial
  | _, _, .step _ _ _ rest, _, t, defined => by
      simp only [Prefix.fill, Term.AnnotationsDefined] at defined
      exact ⟨defined.1, defined.2.1, Prefix.annotationsDefined_of_fill rest t defined.2.2⟩

/-- At every step of a prefix filled with a term that a run reaches, at every step of the
prefix. -/
theorem Prefix.everyStep_of_fill {sem : Semantics D} {permitted : ∀ op, sem.S.Reply op → Prop}
    {P : StepProp sem} {cursor : StaticCursor} :
    ∀ {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) {outs : List D.Ty} (t : Term D Δ outs)
      (path : List Frame) (env : Env sem.Val Γ),
      Term.EveryStep sem permitted P cursor (p.fill t) path env →
        Prefix.EveryStep sem permitted P cursor p path env
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .step _ _ _ rest, _, t, path, _, every => by
      simp only [Prefix.fill, Term.EveryStep] at every
      exact ⟨every.1, every.2.1, Process.every_mono _ _
        (fun _ each => Prefix.everyStep_of_fill rest t path _ each) (fun _ h => h) every.2.2⟩

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **A term is sound as a prefix and an exit**: the term is its prefix filled with its exit
(`toPrefixFill`), whose walk is the prefix's, then the exit's (`walkFill`); the prefix ends, on
every permitted path, where the invariant holds for the names after it, so the exit's identifiers
read what it returns; and the names before the prefix still read their values, the table having
grown (`walkPrefix_grew`). -/
theorem termFromPrefix : TermFromPrefixStatement σ := by
  intro prefixSound laws cursor Γ outs t path ρ ids env s k
  dsimp only
  intro inv defined facts unchanged
  have filled := Term.toPrefix_fill t
  generalize Term.toPrefix t = q at filled
  obtain ⟨Δ, p, exit⟩ := q
  dsimp only at filled
  subst filled
  have definedP := Prefix.annotationsDefined_of_fill p (.ret exit) defined
  have factsP := Prefix.everyStep_of_fill p (.ret exit) path env facts
  have walked := walkFill σ cursor p (.ret exit) ids s k
  dsimp only at walked
  rw [walked] at unchanged ⊢
  simp only [walk] at unchanged ⊢
  have grew := walkPrefix_grew σ.cfg σ.notes cursor p ids s k inv.wf
  have sound := prefixSound laws cursor p path ρ ids env s k inv definedP factsP unchanged
  rw [Prefix.denote_fill_run, Process.every_bind]
  generalize walkPrefix σ.cfg σ.notes cursor p ids s k = e at grew sound ⊢
  refine Process.every_mono _ _ (fun env' found => ?_) (fun _ h => h) sound
  obtain ⟨ρ', le, inv'⟩ := found
  rw [Term.denote_ret]
  refine ⟨ρ', le, ⟨⟨inv'.fresh, fun τ x => ?_, inv.bound, inv'.wf⟩, inv'.valid, inv'.means⟩,
    inv'.toScope.idsOf_reads exit⟩
  obtain ⟨id, found, read⟩ := inv.agree τ x
  exact ⟨id, found, Reads.mono grew.1 le read⟩

end

end Zkc.Core.BodyAnalysis
