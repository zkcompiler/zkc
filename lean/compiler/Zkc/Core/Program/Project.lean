module

public import Zkc.Core.Program.Dialects

@[expose] public section

/-!
Projection: the program of a role, from the term of a protocol.

It is a translation from the protocol dialect to the role dialect, in the same contexts: a
total function, by recursion over the one type of terms. Every name that the protocol's term
binds, the role's term binds at the same place, and every variable is the same name with the
same proof. Every proof that the role's term needs is one that the protocol's term carries. A
role that does not perform a guard passes over it; a role that does not perform a choice or a
loop passes over its regions, and has nothing of what they give, under the same names. Every
role runs the body of an attempt; only its owner marks it.
-/

namespace Zkc.Core

/-! ## Projection -/

section
variable {V : Vocabulary} {hs : Headers V}

/-- A role's part of one operation of a protocol, with the names of its results. -/
def ProtocolOp.project (r : Role) (key : Key) {Γ : Ctx (LTy V)} {outs : List (LTy V)}
    {ins res : List (LTy V)} :
    ProtocolOp V hs ins res → HList (Var Γ) ins → (results : Names res) →
      Term (roleDialect V hs r) (Γ.extend results) outs → Term (roleDialect V hs r) Γ outs
  | .compute R o operands types held, args, results, rest =>
      if h : r ∈ R then
        .op key (.compute R o operands types h fun a ha => held a ha r h) args results rest
      else
        .op key (.absent _ fun a ha => by
          obtain ⟨_, _, e⟩ := List.mem_map.mp ha
          subst e
          exact h) .nil results rest
  | .flow (τ := τ) (H := H) kind giver getters holds _, args, results, rest =>
      if hg : r = giver then .op key (.give kind getters (hg ▸ holds)) args results rest
      else if hm : r ∈ getters then .op key (.get τ H kind giver getters hm) .nil results rest
      else .op key (.keep _ (by simp [Holders.mem_ofList, hm])) args results rest
  | .given kind owner hearers operands τ typed held _, args, results, rest =>
      if ho : r = owner then
        .op key (ho ▸ .own kind hearers operands τ typed fun a ha => ho ▸ held a ha) args results
          rest
      else if hh : r ∈ hearers then .op key (.hear kind owner hearers τ hh) .nil results rest
      else
        .op key (.absent _ fun a ha => by
          simp only [List.mem_singleton] at ha
          subst ha
          simp [Holders.mem_ofList, ho, hh]) .nil results rest
  | .narrow R among, args, results, rest =>
      if h : r ∈ R then .op key (.keep R ⟨fun _ => h, fun _ => among r h⟩) args results rest
      else
        .op key (.absent _ fun a ha => by
          simp only [List.mem_singleton] at ha
          subst ha
          exact h) .nil results rest
  | .apply callee roles distinct covers operands fits, args, results, rest =>
      .op key (.apply callee roles distinct covers operands fits) args results rest

/-- A role's loop, for a role that performs it: how often it runs is what the protocol's
loop says, and its region and its results have the protocol's names. -/
def projectLoop (r : Role) (key : Key) (ps : Holders) (h : r ∈ ps) {Γ : Ctx (LTy V)}
    {outs carried each : List (LTy V)} :
    (times : Times (protocolDialect V hs) ps Γ) → HList (Var Γ) carried →
      (inputs : Names (LTy.index ps :: carried)) →
      Term (roleDialect V hs r) (Γ.extend inputs) (carried ++ each) →
      (results : Names (carried ++ each.map (LTy.collected times.size))) →
      Term (roleDialect V hs r) (Γ.extend results) outs →
      Term (roleDialect V hs r) Γ outs
  | .fixed n, init, inputs, body, results, rest =>
      .loop key ps (.fixed n) (fun _ _ => trivial) init inputs body results rest
  | .value count ok, init, inputs, body, results, rest =>
      .loop key ps (.value count ⟨ok.1, ok.2.1 r h, h⟩) (fun _ _ => trivial) init inputs body
        results rest

mutual
  /-- The program of a role: a total function of the protocol's term. -/
  def project (r : Role) :
      {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → Term (protocolDialect V hs) Γ outs →
        Term (roleDialect V hs r) Γ outs
    | _, _, .ret xs => .ret xs
    | _, _, .op key o args results rest => ProtocolOp.project r key o args results (project r rest)
    | _, _, .guard key ps c ok why rest =>
        if h : r ∈ ps then .guard key ps c ⟨ok.1, ok.2.1 r h, h⟩ why (project r rest)
        else project r rest
    | _, _, .choose key ps c ok gives onTrue onFalse results rest =>
        if h : r ∈ ps then
          .choose key ps c ⟨ok.1, ok.2.1 r h, h⟩ (fun _ _ => trivial) (project r onTrue)
            (project r onFalse) results (project r rest)
        else .op key (.absent _ fun a ha hr => h (gives a ha r hr)) .nil results (project r rest)
    | _, _, .cases key ps x ok gives arms results rest =>
        if h : r ∈ ps then
          .cases key ps x
            (by
              obtain ⟨variant, alternatives, e, payloads, held, _⟩ := ok
              exact ⟨variant, alternatives, e, payloads, held r h, h⟩)
            (fun _ _ => trivial) (projectArms r arms) results (project r rest)
        else .op key (.absent _ fun a ha hr => h (gives a ha r hr)) .nil results (project r rest)
    | _, _, .loop key ps times gives init inputs body results rest =>
        if h : r ∈ ps then
          projectLoop r key ps h times init inputs (project r body) results (project r rest)
        else
          .op key (.absent _ fun a ha hr => by
            rcases List.mem_append.mp ha with ha | ha
            · exact h (gives a (List.mem_append.mpr (.inl ha)) r hr)
            · obtain ⟨b, hb, e⟩ := List.mem_map.mp ha
              subst e
              exact h (gives b (List.mem_append.mpr (.inr hb)) r hr)) .nil results
            (project r rest)
    | _, _, .block key number body results rest =>
        .block key number (project r body) results (project r rest)
    | _, _, .attempt key w _ inputs body results rest =>
        .attempt key w trivial inputs (project r body) results (project r rest)
  def projectArms (r : Role) :
      {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
        Arms (protocolDialect V hs) Γ mid payloads → Arms (roleDialect V hs r) Γ mid payloads
    | _, _, _, .nil => .nil
    | _, _, _, .cons inputs arm rest => .cons inputs (project r arm) (projectArms r rest)
end

end

end Zkc.Core
