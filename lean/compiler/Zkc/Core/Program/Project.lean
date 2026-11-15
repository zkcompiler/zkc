module

public import Zkc.Core.Program.Dialects

@[expose] public section

/-!
Projection: the program of a role, from the term of a protocol.

It is a translation from the protocol dialect to the role dialect, in the same contexts: a
total function, by recursion over the one type of terms. Every proof that the role's term
needs is one that the protocol's term carries. A role that does not perform a guard passes
over it; a role that does not perform a choice or a loop passes over its regions, and has
nothing of what they give. Every role runs the body of an attempt; only its owner marks it.
-/

namespace Zkc.Core

/-! ## Projection -/

section
variable {V : Vocabulary} {hs : Headers V}

/-- A role's part of one operation of a protocol. -/
def ProtocolOp.project (r : Role) (key : Key) {Γ outs : List (LTy V)} {ins res : List (LTy V)} :
    ProtocolOp V hs ins res → HList (Var Γ) ins → Term (roleDialect V hs r) (res ++ Γ) outs →
      Term (roleDialect V hs r) Γ outs
  | .compute R o operands types held, args, rest =>
      if h : r ∈ R then .op key (.compute R o operands types h fun a ha => held a ha r h) args rest
      else
        .op key (.absent _ fun a ha => by
          obtain ⟨_, _, e⟩ := List.mem_map.mp ha
          subst e
          exact h) .nil rest
  | .flow (τ := τ) (H := H) kind giver getters holds _, args, rest =>
      if hg : r = giver then .op key (.give kind getters (hg ▸ holds)) args rest
      else if hm : r ∈ getters then .op key (.get τ H kind giver getters hm) .nil rest
      else .op key (.keep _ (by simp [Holders.mem_ofList, hm])) args rest
  | .given kind owner hearers operands τ typed held _, args, rest =>
      if ho : r = owner then
        .op key (ho ▸ .own kind hearers operands τ typed fun a ha => ho ▸ held a ha) args rest
      else if hh : r ∈ hearers then .op key (.hear kind owner hearers τ hh) .nil rest
      else
        .op key (.absent _ fun a ha => by
          simp only [List.mem_singleton] at ha
          subst ha
          simp [Holders.mem_ofList, ho, hh]) .nil rest
  | .narrow R among, args, rest =>
      if h : r ∈ R then .op key (.keep R ⟨fun _ => h, fun _ => among r h⟩) args rest
      else
        .op key (.absent _ fun a ha => by
          simp only [List.mem_singleton] at ha
          subst ha
          exact h) .nil rest
  | .apply callee roles distinct covers operands fits, args, rest =>
      .op key (.apply callee roles distinct covers operands fits) args rest

/-- A role's loop, for a role that performs it: how often it runs is what the protocol's
loop says. -/
def projectLoop (r : Role) (key : Key) (ps : Holders) (h : r ∈ ps) {Γ outs carried each : List (LTy V)} :
    (times : Times (protocolDialect V hs) ps Γ) → HList (Var Γ) carried →
      Term (roleDialect V hs r) (LTy.index ps :: (carried ++ Γ)) (carried ++ each) →
      Term (roleDialect V hs r) ((carried ++ each.map (LTy.collected times.size)) ++ Γ) outs →
      Term (roleDialect V hs r) Γ outs
  | .fixed n, init, body, rest => .loop key ps (.fixed n) (fun _ _ => trivial) init body rest
  | .value count ok, init, body, rest =>
      .loop key ps (.value count ⟨ok.1, ok.2.1 r h, h⟩) (fun _ _ => trivial) init body rest

mutual
  /-- The program of a role: a total function of the protocol's term. -/
  def project (r : Role) :
      {Γ outs : List (LTy V)} → Term (protocolDialect V hs) Γ outs →
        Term (roleDialect V hs r) Γ outs
    | _, _, .ret xs => .ret xs
    | _, _, .op key o args rest => ProtocolOp.project r key o args (project r rest)
    | _, _, .guard key ps c ok why rest =>
        if h : r ∈ ps then .guard key ps c ⟨ok.1, ok.2.1 r h, h⟩ why (project r rest)
        else project r rest
    | _, _, .choose key ps c ok gives onTrue onFalse rest =>
        if h : r ∈ ps then
          .choose key ps c ⟨ok.1, ok.2.1 r h, h⟩ (fun _ _ => trivial) (project r onTrue)
            (project r onFalse) (project r rest)
        else .op key (.absent _ fun a ha hr => h (gives a ha r hr)) .nil (project r rest)
    | _, _, .cases key ps x ok gives arms rest =>
        if h : r ∈ ps then
          .cases key ps x
            (by
              obtain ⟨variant, alternatives, e, payloads, held, _⟩ := ok
              exact ⟨variant, alternatives, e, payloads, held r h, h⟩)
            (fun _ _ => trivial) (projectArms r arms) (project r rest)
        else .op key (.absent _ fun a ha hr => h (gives a ha r hr)) .nil (project r rest)
    | _, _, .loop (carried := carried) (each := each) key ps times gives init body rest =>
        if h : r ∈ ps then projectLoop r key ps h times init (project r body) (project r rest)
        else
          .op key (.absent _ fun a ha hr => by
            rcases List.mem_append.mp ha with ha | ha
            · exact h (gives a (List.mem_append.mpr (.inl ha)) r hr)
            · obtain ⟨b, hb, e⟩ := List.mem_map.mp ha
              subst e
              exact h (gives b (List.mem_append.mpr (.inr hb)) r hr)) .nil (project r rest)
    | _, _, .block key number body rest => .block key number (project r body) (project r rest)
    | _, _, .attempt key w _ body rest => .attempt key w trivial (project r body) (project r rest)
  def projectArms (r : Role) :
      {Γ mid payloads : List (LTy V)} → Arms (protocolDialect V hs) Γ mid payloads →
        Arms (roleDialect V hs r) Γ mid payloads
    | _, _, _, .nil => .nil
    | _, _, _, .cons arm rest => .cons (project r arm) (projectArms r rest)
end

end

end Zkc.Core
