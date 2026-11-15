module

public import Zkc.Core.Facts.Soundness
public import Zkc.Core.Meaning.Program

@[expose] public section

/-!
The check of facts of the functions of a program, and the theorem for a program: by induction
over its definitions, when the check accepts each function against the headers before it, every
function is safe and keeps validity on valid inputs, and no loop of a function runs more often
than its bound.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The check of facts of every function of a program, each against the headers before it: the
bounds of all their loops, or the refusals of every function that it refuses, those of earlier
definitions first. -/
def Defs.checkFunctions : {hs : Headers V} → Defs V hs →
    Except (List (Refusal V.Ty (LocalRaw V))) (List (Place × Nat))
  | _, .nil => .ok []
  | _, .fn (hs := hs) hdr body _ rest =>
      match Defs.checkFunctions rest, checkFacts (localFactRules V hs.fns) hdr.key none body with
      | .ok others, .ok mine => .ok (mine ++ others)
      | .ok _, .error refusals => .error refusals
      | .error earlier, .ok _ => .error earlier
      | .error earlier, .error refusals => .error (earlier ++ refusals)
  | _, .protocol _ _ _ rest => Defs.checkFunctions rest

theorem checkFunctions_split {hs : Headers V} {hdr : FnHeader V} {body : Fn V hs.fns hdr}
    {ok : FnConditions body} {rest : Defs V hs} {bounds : List (Place × Nat)}
    (h : Defs.checkFunctions (.fn hdr body ok rest) = .ok bounds) :
    ∃ mine others, checkFacts (localFactRules V hs.fns) hdr.key none body = .ok mine ∧
      Defs.checkFunctions rest = .ok others ∧ bounds = mine ++ others := by
  simp only [Defs.checkFunctions] at h
  split at h
  · next others mine e1 e2 =>
      simp only [Except.ok.injEq] at h
      exact ⟨mine, others, e2, e1, h.symm⟩
  all_goals cases h

/-- The bounds of the functions of a program are at the places of their definitions. -/
theorem checkFunctions_places : ∀ {hs : Headers V} (defs : Defs V hs)
    {bounds : List (Place × Nat)}, Defs.checkFunctions defs = .ok bounds →
    ∀ q, q ∈ bounds → q.1.definition ∈ hs.fns.map (·.key) ∧ q.1.role = none
  | _, .nil, bounds, h, q, m => by
      simp only [Defs.checkFunctions, Except.ok.injEq] at h
      subst h
      cases m
  | _, .fn hdr body ok rest, bounds, h, q, m => by
      obtain ⟨mine, others, e1, e2, rfl⟩ := checkFunctions_split h
      rcases List.mem_append.mp m with m | m
      · obtain ⟨d, r⟩ := FactCheck.checkFacts_places hdr.key body e1 q m
        exact ⟨by rw [d]; exact List.mem_cons_self, r⟩
      · obtain ⟨d, r⟩ := checkFunctions_places rest e2 q m
        exact ⟨List.mem_cons_of_mem _ d, r⟩
  | _, .protocol _ _ _ rest, bounds, h, q, m => checkFunctions_places rest h q m

/-- **The check of facts is sound for the functions of a program.** When the check accepts every
function of a program against the headers before it, and the keys of the functions are distinct:
every function never stops `undefined` on valid inputs, returns valid values, and on valid inputs
none of its loops runs more often than the bound that an annotation gives it, for every
annotation whose entries at the functions' places are among the bounds that the check gives. -/
theorem functions_sound : ∀ {hs : Headers V} (defs : Defs V hs),
    (hs.fns.map (·.key)).Nodup → ∀ {bounds : List (Place × Nat)},
    Defs.checkFunctions defs = .ok bounds → ∀ (M : Model V) (F : List (Place × Nat)),
    (∀ p b, (p, b) ∈ F → p.role = none → p.definition ∈ hs.fns.map (·.key) → (p, b) ∈ bounds) →
    FnTable.Safe (Defs.fnTable M defs) ∧ FnTable.KeepsValidity (Defs.fnTable M defs) ∧
      Defs.FunctionsRespect M ⟨F⟩ defs
  | _, .nil, _, _, _, M, _, _ =>
      ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), trivial⟩
  | _, .fn (hs := hs) hdr body ok rest, distinct, bounds, h, M, F, hF => by
      obtain ⟨mine, others, e1, e2, rfl⟩ := checkFunctions_split h
      have notIn := (List.nodup_cons.mp distinct).1
      have distinct' := (List.nodup_cons.mp distinct).2
      obtain ⟨safeR, keepsR, respR⟩ := functions_sound rest distinct' e2 M F
        (fun p b m r d => by
          rcases List.mem_append.mp (hF p b m r (List.mem_cons_of_mem _ d)) with m' | m'
          · have := (FactCheck.checkFacts_places hdr.key body e1 _ m').1
            simp only at this
            rw [this] at d
            exact absurd d notIn
          · exact m')
      have sound := FactCheck.checkFacts_sound (table := Defs.fnTable M rest) distinct' safeR
        keepsR hdr.key body ok.distinct e1 F (fun p b m d r => by
          rcases List.mem_append.mp (hF p b m r (by rw [d]; exact List.mem_cons_self)) with
            m' | m'
          · exact m'
          · have := (checkFunctions_places rest e2 _ m').1
            simp only at this
            rw [d] at this
            exact absurd this notIn)
      refine ⟨fun hdr' f args valid => ?_, fun hdr' f args results valid e => ?_,
        fun ins valid => (sound ins valid).1, respR⟩
      · cases f with
        | head =>
            simp only [Defs.fnTable]
            exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) (sound args valid).2
        | tail f => exact safeR _ f args valid
      · cases f with
        | head =>
            simp only [Defs.fnTable] at e
            have := (sound args valid).2
            rw [e] at this
            exact this
        | tail f => exact keepsR _ f args results valid e
  | _, .protocol _ _ _ rest, distinct, _, h, M, F, hF => by
      obtain ⟨safeR, keepsR, respR⟩ := functions_sound rest distinct h M F hF
      exact ⟨safeR, keepsR, respR⟩

/-- **The check of facts is sound for a typed program.** When the check accepts every function of
a typed program: every function never stops `undefined` on valid inputs and returns valid values
(what `functionsSafe` and `functionsKeepValidity` ask of an admitted program), and the functions'
part of `Respects` holds of the bounds that the check gives. -/
theorem typed_functions_sound (p : Typed V) {bounds : List (Place × Nat)}
    (accepted : Defs.checkFunctions p.defs = .ok bounds) (M : Model V) :
    (∀ hdr (f : Var p.headers.fns hdr) (ins : HList M.Val hdr.ins), ins.All M.Valid →
      (fnMeaning M p f ins).Stops (· ≠ .undefined)) ∧
    (∀ hdr (f : Var p.headers.fns hdr) (ins : HList M.Val hdr.ins)
      (outs : HList M.Val hdr.outs), ins.All M.Valid → fnMeaning M p f ins = .done outs →
        outs.All M.Valid) ∧
    Defs.FunctionsRespect M ⟨bounds⟩ p.defs := by
  have distinct := (List.nodup_append.mp p.distinct).1
  obtain ⟨safe, keeps, respect⟩ := functions_sound p.defs distinct accepted M bounds
    (fun _ _ m _ _ => m)
  exact ⟨fun hdr f ins valid => safe hdr f ins valid,
    fun hdr f ins outs valid e => keeps hdr f ins outs valid e, respect⟩

end

end Zkc.Core

#print axioms Zkc.Core.functions_sound
#print axioms Zkc.Core.typed_functions_sound
