module

public import Zkc.Core.Facts.Body.Statements

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {D : Dialect}

section
variable (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop) (P : StepProp sem)

private theorem everyResult {A : Type} (p : Process sem.S sem.H A) {Q : A → Prop} (h : ∀ v, Q v) :
    p.Every permitted Q (fun _ => True) :=
  Process.every_mono p permitted (fun v _ => h v) (fun _ _ => trivial) (Process.every_true permitted p)

mutual
  theorem everyStep_of_all
      (all : ∀ cursor key {Γ mid} (i : Instr D Γ mid) path env, P cursor key i path env)
      (cursor : StaticCursor) : ∀ {Γ outs} (t : Term D Γ outs) path env,
      Term.EveryStep sem permitted P cursor t path env
    | _, _, .ret _, _, _ => trivial
    | _, _, .step key i results rest, path, env =>
      ⟨all cursor key i path env, everyInstr_of_all all cursor key i path env,
        everyResult sem permitted _ (fun vs => everyStep_of_all all cursor.next rest path (env.extend results vs))⟩
  theorem everyInstr_of_all
      (all : ∀ cursor key {Γ mid} (i : Instr D Γ mid) path env, P cursor key i path env)
      (cursor : StaticCursor) (key : Key) : ∀ {Γ mid} (i : Instr D Γ mid) path env,
      Instr.EveryStep sem permitted P cursor key i path env
    | _, _, .op .., _, _ | _, _, .guard .., _, _ => trivial
    | _, _, .choose _ c ok _ t f, path, env => by
      unfold Instr.EveryStep
      cases sem.holds ok (env.get c)
      · exact everyStep_of_all all _ f path env
      · exact everyStep_of_all all _ t path env
    | _, _, .cases _ _ _ _ arms, path, env => everyArms_of_all all _ arms path env _
    | _, _, .loop _ _ _ _ _ body, _, _ => fun _ _ => everyResult sem permitted _ (fun _ => everyStep_of_all all _ body _ _)
    | _, _, .block _ body, _, _ => everyStep_of_all all _ body _ _
    | _, _, .attempt _ _ _ body, _, _ => everyResult sem permitted _ (fun _ => everyStep_of_all all _ body _ _)
  theorem everyArms_of_all
      (all : ∀ cursor key {Γ mid} (i : Instr D Γ mid) path env, P cursor key i path env)
      (cursor : StaticCursor) : ∀ {Γ mid payloads} (arms : Arms D Γ mid payloads) path env pick,
      Arms.EveryStep sem permitted P cursor arms path env pick
    | _, _, _, .cons _ arm _, _, _, .here _ => everyStep_of_all all _ arm _ _
    | _, _, _, .cons _ _ rest, _, _, .there _ => everyArms_of_all all _ rest _ _ _
end
end

theorem everyFact_of_noGiven {Raw : Type} (σ : Setting D Raw)
    (internal : σ.notes.any (fun entry => entry.2.isGiven) = false) {Γ outs}
    (body : Term D Γ outs) path env : Term.EveryFact σ .root body path env := by
  apply everyStep_of_all
  intro cursor key Γ mid i path env names e mem
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp mem
  have inside := (List.mem_filter.mp kept).1
  have no := List.any_eq_false.mp internal entry inside
  rw [same] at no
  contradiction

theorem noGivenFacts {Raw : Type} (σ : Setting D Raw) (empty : σ.notes = []) {Γ outs}
    (body : Term D Γ outs) path env : Term.EveryFact σ .root body path env := by
  apply everyStep_of_all
  intro cursor key Γ mid i path env names e mem
  simp [empty, Annotations.at_] at mem

end Zkc.Core.BodyAnalysis
