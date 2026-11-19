module

public import Zkc.Formal.Written.TableSession
public import Zkc.Tools.Formal.TableCertificate
public import Zkc.Formal.Written.StandardDefaults

@[expose] public section
namespace Zkc.Tests.Formal.TableRuntime
open Zkc.Core Zkc.Formal.Written Frontend.Emit TableVerifier TableService StandardDefaults

/-- Distinguishable handles and scalars. Unused algebraic rows return valid defaults.
The equality used in the real verifier guard compares its two inputs. -/
abbrev carriers : Carriers Standard where
  Carrier _ := Nat
  valid _ _ := True
  literal _ n := some n

def nominal (k : Standard.TypeKey) : Sample carriers (.nominal k) := ⟨0,trivial⟩

def outputs : (k : Standard.RowKey) → (sig : RowSignature Standard.TypeKey Standard.RowKey) →
    Standard.row k = some sig → HList (Ty.Val carriers) sig.ins → Samples carriers sig.outs
  | .inl (.field .equal .koalaBear .all), _, known, args => by
    cases known; cases args; rename_i x tail; cases tail; rename_i y tail; cases tail
    exact single ⟨Nat.beq x y,trivial⟩
  | k, sig, known, _ => rowSamples nominal k sig known

def model : Model Standard := { carriers with
  apply := fun k sig known args => some (outputs k sig known args).values
  inDomain := fun _ _ _ _ => true
  defined := by intros; rfl
  total := by intros; rfl
  decides := by
    intro k s h d hk args
    obtain ⟨f,rfl,rfl⟩ := restricted h hk
    cases f <;> cases h <;> cases args with | cons x tail => cases tail; rfl
  keeps := by intro k sig known args values _ ran; cases ran; exact (outputs k sig known args).valid
  literals := by intros; exact ⟨_,rfl,trivial⟩
  support := fun _ s _ _ v => s.out.Valid carriers v
  supported := by intros; assumption }

instance (tag : Standard.TypeKey) : DecidableEq (model.Val (.nominal tag)) := Nat.decEq

instance : DecidableEq (model.Val (scalar {})) := Nat.decEq

def controls {b : Bindings} (p : Typed b.vocabulary) (key : Key) (domain handle : b.vocabulary.Ty)
    (shape : Shape b.vocabulary) (root : Member p.headers.protocols ⟨key,2,ports domain,[],shape⟩) :
    Except String Unit := by
  rcases b with ⟨bindings,distinct⟩
  cases bindings with
  | cons => exact .error "unexpected project rows"
  | nil =>
    cases handle with
    | nominal tag =>
      exact do
        let some (dom,[]) := Ty.read model domain [1] | throw "invalid test domain"
        let coeffs : List Nat := [0,0,0,0]
        let reader := roleMeaning model p root 1 [] (.cons coeffs (.cons dom .nil))
        let joint := protocolMeaning model p root [] (.cons coeffs (.cons dom .nil))
        let offer : Offer Nat Nat := ⟨17,fun _ => 0⟩
        let tape : Draw := fun j => ⟨j.val+3,by have := j.isLt; omega⟩
        let reply (h : Nat) (ix : List Nat) := (h,ix.map fun _ => 0)
        let cases : List (String × Opener Nat Nat × Bool) :=
          [("honest",reply,true),
           ("wrong handle",fun h ix => reply (h+1) ix,false),
           ("forged row",fun h ix => (h,(reply h ix).2.set 11 1),false)]
        for (name,opener,expected) in cases do
          unless accepted model (.nominal tag) offer opener tape reader == expected do
            throw s!"projected verifier disagreed on {name}"
          let projected := outcome (answer (b := {}) model (.nominal tag) offer opener tape) reader State.empty
          let both := outcome (jointAnswer model (.nominal tag) offer.handle (fun _ => opener) tape) joint .empty
          unless returned both == expected do throw s!"joint execution disagreed on {name}"
          unless expected do
            let .halted (.declared .reject ⟨[],⟨7⟩⟩) := projected.1 | throw s!"{name} missed the opening guard"
            let .halted ([1],.declared .reject ⟨[],⟨7⟩⟩) := both.1 | throw s!"joint {name} missed the opening guard"
            pure ()
        let data (i : Fin 1024) := i.val + 5
        let tableRows := List.ofFn data
        let sent := GOp.given (M := model) (.request ⟨0⟩) 0 [1] ⟨[],⟨1⟩⟩ [table {}] (.cons tableRows .nil) (.nominal tag)
        let read := jointAnswer model (.nominal tag) (17 : Nat) (fun fixed => honest fixed.data) tape
        let (some received,registered) := (read sent .empty : Option Nat × Session model (.nominal tag)) | throw "registration did not consume the submitted table"
        unless Nat.beq received 17 do throw "registered handle changed"
        let (_,drawn) := read (.given (.coin (.uniform (.seq (.fin 1024) (some 40)))) 1 [0] ⟨[],⟨2⟩⟩ [] .nil (positions {})) registered
        let query (h : Nat) (ix : List Nat) := GOp.given (M := model) (.request ⟨1⟩) 0 [1] ⟨[],⟨4⟩⟩
          [.tuple (pair (.nominal tag))] (.cons (h,ix,()) .nil) (rows {})
        unless (show Option (List Nat) from (read (query 17 (request tape)) drawn).1) == some (values data tape) do
          throw "query did not look up the registered values at the requested indices"
        unless (read (query 18 (request tape)) drawn).1.isNone do throw "query accepted a swapped handle"
        unless (read (query 17 (request tape).reverse) drawn).1.isNone do throw "query accepted reordered indices"
        let altered : Offer Nat Nat := ⟨17,fun i => if i.val = 14 then 1 else 0⟩
        let accurate : Opener Nat Nat := fun h ix => (h,ix.map fun i => if i = 14 then 1 else 0)
        let result := outcome (answer (b := {}) model (.nominal tag) altered accurate tape) reader State.empty
        let .halted (.declared .reject ⟨[],⟨17⟩⟩) := result.1 | throw "wrong polynomial row missed the final written guard"
        pure ()
    | _ => exact .error "expected a nominal handle"

end Zkc.Tests.Formal.TableRuntime
