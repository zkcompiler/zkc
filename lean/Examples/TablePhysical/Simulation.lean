import Examples.TablePhysical.Language

/-! Complete table-region correspondence, including old aliases and stopped
provider state. The physical handler calls the selected logical kernel/provider
contracts; this proves the reference realization, not native implementations.
-/

set_option autoImplicit false
namespace TablePhysical
open TableProtocol Zkc.Source Zkc.Realization

variable {S E : Type}

private theorem decodeValues_related {Γ : List Ty} (a : Values TableProtocol.Value Γ)
    (b : Values Value Γ) (s : S) (t : State S)
    (related : representation.Environments a.get s b.get t) :
    decodeValues t.store b = some a := by
  induction a with
  | nil => cases b; rfl
  | cons x rest ih =>
    cases b with
    | cons y tail =>
      have head : decode t.store _ y = some x := related _ .here
      have tailSame := ih tail (fun ty v => related ty (.there v))
      simp [decodeValues, head, tailSame]

private theorem follow_done {S E A : Type} (out : PIR.Execution S E A) :
    out.follow (fun value state => ⟨.returned value, state, []⟩) = out := by
  rcases out with ⟨outcome, state, events⟩
  cases outcome <;> simp [PIR.Execution.follow]

theorem run_operation (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    (op : Operation) (args : Values Value (language.arguments op))
    (state : State S) :
    (meaning.operation op args).run (handler logicalHandler) state = handler logicalHandler ⟨op, args⟩ state := by
  exact follow_done _

private theorem invoke_correct (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    (op : Protocol.Operation) (s : S) (t : State S)
    (a : Values TableProtocol.Value (Protocol.arguments op)) (b : Values Value (Protocol.arguments op))
    (states : s = t.logical) (args : representation.Environments a.get s b.get t) :
    representation.Results (fun event => [event]) (fun event => [event]) s t
      ((Protocol.meaning.operation op a).run logicalHandler s) (invoke logicalHandler op b t) := by
  rw [invoke, decodeValues_related a b s t args]
  dsimp only
  subst s
  generalize evaluated : (Protocol.meaning.operation op a).run logicalHandler t.logical = out
  rcases out with ⟨outcome, final, events⟩
  refine ⟨?_, ⟨rfl, ?_⟩, rfl⟩
  · cases outcome with
    | returned value => exact decode_embed t.store _ value
    | stopped why => rfl
  · intro ty x y related
    exact related

private theorem prepare_correct (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    (mode : Mode) (d : Domain) (n : Nat)
    (view : Zkc.Polynomial.Table.Residual (Field d) n) (tail : List (Field d))
    (s : S) (t : State S) (states : s = t.logical) :
    representation.Results (ty := .scalar d) (fun event => [event]) (fun event => [event]) s t
      ((Protocol.meaning.operation (.base (.evaluate d n)) (.cons view (.cons tail .nil))).run
        logicalHandler s)
      (prepare mode d n view tail t) := by
  by_cases shape : (view.coordinates ++ tail).length = n
  · simp only [prepare, shape, ↓reduceDIte]
    simp only [TableProtocol.checked,
      Zkc.Polynomial.Table.evaluate, shape, ↓reduceDIte, Protocol.lift, PIR.Proc.run]
    refine ⟨?_, ⟨states, ?_⟩, rfl⟩
    · exact (read_publish_new t.store d (cell mode view tail shape)).trans
        (congrArg some (read_cell mode view tail shape))
    · intro ty x y old
      exact decode_publish_old t.store d (cell mode view tail shape) ty x y old
  · simp only [prepare, shape, ↓reduceDIte]
    simp only [TableProtocol.checked,
      Zkc.Polynomial.Table.evaluate, shape, ↓reduceDIte, Protocol.lift, PIR.Proc.run]
    exact ⟨rfl, ⟨states, Representation.Frame.refl representation s t⟩, rfl⟩

theorem simulation (logicalHandler : PIR.Handler Protocol.protocolInterface S E) :
    RegionSimulation logicalMeaning meaning logicalHandler (handler logicalHandler)
    representation (fun event => [event]) (fun event => [event]) where
  condition := by
    intro s t a b _ related
    exact (Option.some.inj related).symm
  operation := by
    intro op s t a b states args
    rw [run_operation]
    cases op with
    | invoke op => exact invoke_correct logicalHandler op s t a b states args
    | prepare mode d n =>
      cases a with
      | cons view a => cases a with
        | cons tail a => cases a with
          | nil =>
            cases b with
            | cons nativeView b => cases b with
              | cons nativeTail b => cases b with
                | nil =>
                  have sameView : nativeView = view := Option.some.inj (args _ .here)
                  have sameTail : nativeTail = tail := Option.some.inj (args _ (.there .here))
                  subst nativeView nativeTail
                  exact prepare_correct logicalHandler mode d n view tail s t states

/-- Actual physical regions refine their logical projection for every related
input, store and provider state. Strategies may differ at each preparation site. -/
theorem correct (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    {Γ : List Ty} {ty : Ty} (program : Region language Γ ty)
    (a : Environment TableProtocol.Value Γ) (b : Environment Value Γ)
    (s : S) (t : State S) (states : representation.states s t)
    (inputs : representation.Environments a s b t) :
    representation.Results (fun event => [event]) (fun event => [event]) s t
      (((erase program).denote Protocol.meaning a).run logicalHandler s)
      ((program.denote meaning b).run (handler logicalHandler) t) := by
  rw [denote_erase]
  exact (simulation logicalHandler).run program a b s t states inputs

end TablePhysical
