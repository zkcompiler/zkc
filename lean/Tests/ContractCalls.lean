import Zkc.Source.Structured.ContractCalls

set_option autoImplicit false
namespace Tests.ContractCalls
open Zkc.Source Zkc.Source.Structured

/-- A callee with no source contract is still an executable call. -/
def signature : ProtocolSignature :=
  { name := "unannotated", roles := ["P", "V"], inputs := [.index], outputs := [.index],
    inputScopes := [[0, 1]], outputScopes := [[0, 1]] }

def leaf (site : String) : Region protocolDialect [.index] [.index] :=
  .letOp (.protocolApply signature [1, 0] site) (.cons .here .nil) .nil
    (.ret (.cons .here .nil))

def repeatSpec : RepeatSpec := ⟨[.index], [], [0, 1], [[0, 1]], 4⟩

def repeatedBody : Region protocolDialect [.index, .index] [.index] :=
  .bind
    (.letOp (.protocolApply signature [0, 1] "inner") (.cons (.there .here) .nil) .nil
      (.ret (.cons .here .nil)))
    (.letOp (.protocolApply signature [1, 0] "after-inner") (.cons .here .nil) .nil
      (.ret (.cons .here .nil)))

def nested : Region protocolDialect [.index] [.index] :=
  .bind (leaf "first")
    (.letOp (.repeat repeatSpec "loop") (.cons .here (.cons (.there .here) .nil))
      (.cons repeatedBody .nil)
      (.letOp (.protocolApply signature [0, 1] "last") (.cons .here .nil) .nil
        (.ret (.cons .here .nil))))

/-- The complete lexical inventory includes both bind branches and the repeat
callback. Its order is deterministic: head, suffix, then nested callbacks. -/
example : (callSites nested).map (·.site) = ["first", "last", "inner", "after-inner"] := rfl
example : (callInventory nested).length = 4 := rfl
example : (callInventory nested).map (·.position) = [[0], [1, 1], [1, 0, 0], [1, 0, 1]] := rfl
example : (callInventory nested).map (·.repeats) = [[], [], [([1], 4)], [([1], 4)]] := rfl
example : (callSites nested).map (·.roles) = [[1, 0], [0, 1], [0, 1], [1, 0]] := rfl
example : (callSites nested).map (fun call => call.operands.indices) = [[0], [0], [1], [0]] := rfl

/-- Independently authored occurrence evidence is necessarily in the inventory. -/
def inner : ApplicationOccurrence signature [0, 1] "inner"
    (.cons (.there .here) .nil : Operands [Ty.index, Ty.index] [Ty.index]) nested :=
  .bindNext _ _ (.repeatBody _ _ _ _ _ (.bindBody _ _ (.here _)))

example : CallOccurrence.mk ⟨[.index, .index], signature, [0, 1], "inner", .cons (.there .here) .nil⟩
    inner ∈ callInventory nested := callInventory_complete _

/-- Site, callee signature and role-map substitutions do not match the source. -/
example : "invented" ∉ (callSites nested).map (·.site) := by decide
example : "other" ∉ (callSites nested).map (·.signature.name) := by decide
example : [0, 0] ∉ (callSites nested).map (·.roles) := by decide

example : ¬ Nonempty (CallObligations (leaf "unannotated") (fun _ => False)) := by
  rintro ⟨resolved⟩
  exact resolved.resolve (CallOccurrence.here signature [1, 0] "unannotated" _ _)

/-- A lexical call after a stop is still inventoried; inventory is not a trace. -/
def unreachable : Region protocolDialect [.index] [.index] :=
  .bind (.stop (out := []) .refused) (leaf "after-stop")

example : (callSites unreachable).map (·.site) = ["after-stop"] := rfl

#eval do
  let calls := callInventory nested
  unless calls.length == 4 do throw (IO.userError "incomplete lexical call inventory")
  unless (calls.map CallOccurrence.position) == [[0], [1, 1], [1, 0, 0], [1, 0, 1]] do
    throw (IO.userError "incorrect lexical call positions")
  unless ((callSites nested).map CallSite.site) == ["first", "last", "inner", "after-inner"] do
    throw (IO.userError "incorrect lexical call sites")
  IO.println "ContractCalls: computable lexical inventory controls passed"

#print axioms Zkc.Source.Structured.callInventory_complete
#print axioms Zkc.Source.Structured.mem_locatedCallSites_iff
end Tests.ContractCalls
