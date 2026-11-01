import Tests.Companions
import ZkcTools.Companions.Assembly

set_option autoImplicit false
open Lean Elab Command Term Meta ZkcTools.Companions

@[zkc "Assembly.registered"] theorem companionShadowTarget : True := True.intro

/- A registered declaration keeps its identity even when local notation would
resolve the same spelling to a proof of a different proposition. -/
run_elab do
  let selection : Array Selection := #[⟨"Assembly.registered", #[]⟩]
  withLocalDeclD `companionShadowTarget (Lean.mkConst ``False) fun shadow => do
    let wanted := Lean.mkConst ``True
    let matched ← resolve selection wanted
    match matched with
    | .matched _ declaration value =>
        unless declaration == ``companionShadowTarget &&
            value.isConstOf ``companionShadowTarget do
          throwError "registered companion identity was captured by a local name"
    | _ => throwError "a local name refused a valid registered companion"
    let direct ← resolve selection (Lean.mkConst ``False)
    unless (match direct with | .refused _ _ => true | _ => false) do
      throwError "a local proof replaced the registered declaration"
    let fallback : DefaultMethod := ⟨"local-proof", ← exprToSyntax shadow⟩
    let result ← assemble selection (Lean.mkConst ``False) #[fallback]
    unless (match result with | .refused _ _ => true | _ => false) do
      throwError "fallback hid a captured registered companion"
    let accepted ← assemble selection wanted #[]
    unless (match accepted with
      | .discharged value method _ => value.isConstOf ``companionShadowTarget &&
          method == "companion:Assembly.registered"
      | _ => false) do
      throwError "assembly did not use the selected registered declaration"

run_elab do
  let expected := Lean.mkConst ``True
  let good : DefaultMethod := ⟨"truth", ← `(term| True.intro)⟩
  let bad : DefaultMethod := ⟨"wrong-type", ← `(term| (0 : Nat))⟩
  let result ← assemble #[] expected #[bad, good]
  match result with
  | .discharged value method attempts =>
      unless method == "truth" && attempts.size == 1 do
        throwError "default methods did not retain their ordered refusals"
      unless ← isDefEq (← inferType value) expected do throwError "default changed the meaning"
  | _ => throwError "a valid default was not selected"
  let unresolved ← assemble #[] expected #[bad]
  unless (match unresolved with | .openObligation _ attempts => attempts.size == 1 | _ => false) do
    throwError "an unavailable default was not left open"
  let target ← elabTerm (← `(term| 3 + 0 = (3 : Nat))) none
  let pending ← assemble #[⟨"Counter.pending", #[← `(term| 3)]⟩] target #[⟨"rfl", ← `(term| rfl)⟩]
  unless (match pending with | .openObligation _ _ => true | _ => false) do
    throwError "a default silently replaced an explicit unfinished companion"
  let overridden ← assemble #[⟨"Counter.base", #[← `(term| 3)]⟩] target #[bad]
  unless (match overridden with
    | .discharged _ method attempts => method == "companion:Counter.base" && attempts.isEmpty
    | _ => false) do
    throwError "an imported companion did not override defaults"
  let wrong ← assemble #[⟨"Counter.base", #[← `(term| 3)]⟩] expected #[good]
  unless (match wrong with | .refused _ _ => true | _ => false) do
    throwError "a default hid an ill-typed explicit companion"
  let unknown ← mkFreshExprMVar (mkSort .zero)
  let refused ← try
    let _ ← assemble #[] unknown #[good]
    pure false
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    pure ((← error.toMessageData.toString).contains
      "requires the complete expected type before proof selection")
  unless refused && !(← unknown.mvarId!.isAssigned) do
    throwError "proof selection chose the requested proposition"

elab "companion_internal_failure%" : term =>
  throw (.internal Tests.Companions.proposalFailureId)

/- An implementation failure is not a missing mathematical method. Neither
ordered defaults nor an explicit companion may turn it into fallback/open. -/
run_elab do
  let expected := Lean.mkConst ``True
  let good : DefaultMethod := ⟨"truth", ← `(term| True.intro)⟩
  let broken : DefaultMethod := ⟨"internal-failure", ← `(term| companion_internal_failure%)⟩
  for explicit in [false, true] do
    let propagated ← try
      if explicit then
        let target ← elabTerm (← `(term| 3 + 0 = (3 : Nat))) none
        let _ ← assemble #[⟨"Counter.base", #[← `(term| companion_internal_failure%)]⟩]
          target #[good]
        pure false
      else
        let _ ← assemble #[] expected #[broken, good]
        pure false
    catch error =>
      match error with
      | .internal id _ =>
          if id == Tests.Companions.proposalFailureId then pure true else throw error
      | _ => throw error
    unless propagated do throwError "internal proposal failure was converted into a method result"
