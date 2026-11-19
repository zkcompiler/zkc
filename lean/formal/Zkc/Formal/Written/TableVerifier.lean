module

public import Zkc.Core.Evidence.ProtocolReadback
public import Zkc.Core.Evidence.FunctionReadback
public import Zkc.Frontend.Emit.Bindings

@[expose] public section
namespace Zkc.Formal.Written.TableVerifier
open Core Frontend.Emit

variable (b : Bindings)
abbrev scalar : b.vocabulary.Ty := .nominal (.inl (.field .koalaBear))
abbrev nonzero : b.vocabulary.Ty := .nominal (.inl (.nonzero .koalaBear))
abbrev polynomial := Core.Ty.seq (scalar b) (some 4)
abbrev positions : b.vocabulary.Ty := .seq (.fin 1024) (some 40)
abbrev rows := Core.Ty.seq (scalar b) (some 40)
abbrev table := Core.Ty.seq (scalar b) (some 1024)

variable {b}
abbrev shared (t : b.vocabulary.Ty) : LTy b.vocabulary := ⟨t,[0,1]⟩
abbrev verifier (t : b.vocabulary.Ty) : LTy b.vocabulary := ⟨t,[1]⟩
abbrev prover (t : b.vocabulary.Ty) : LTy b.vocabulary := ⟨t,[0]⟩
abbrev fn (k : Key) (ins : List b.vocabulary.Ty) (out : b.vocabulary.Ty) :
    FnHeader b.vocabulary := ⟨k,ins,[out],false,none,⟨[],[]⟩⟩

structure Calls (hs : Headers b.vocabulary) (domain : b.vocabulary.Ty) where
  registerKey : Key
  pointKey : Key
  evaluateKey : Key
  tabulate : Member hs.fns (fn registerKey [polynomial b, domain] (table b))
  point : Member hs.fns (fn pointKey [domain,.fin 1024] (nonzero b))
  evaluate : Member hs.fns (fn evaluateKey [polynomial b,scalar b] (scalar b))

abbrev pair (h : b.vocabulary.Ty) := Core.Tys.cons h (.cons (positions b) .nil)
abbrev claim (h : b.vocabulary.Ty) := Core.Tys.cons h (.cons (positions b) (.cons (rows b) .nil))
abbrev ports (domain : b.vocabulary.Ty) := [shared (polynomial b),shared domain]
abbrev names (domain : b.vocabulary.Ty) : Names (ports domain) := .cons 0 (.cons 1 .nil)

variable {hs : Headers b.vocabulary} {domain : b.vocabulary.Ty}
variable (calls : Calls hs domain) (handle : b.vocabulary.Ty)

local macro "v!" n:num : term => `(⟨$n,rfl⟩)
local macro "args!" "[" ns:num,* "]" : term => do
  ns.getElems.foldrM (init := ← `(HList.nil)) fun n tail => `(HList.cons (v! $n) $tail)
local macro "calcAt" rs:term:max op:term:max ts:term:max : term =>
  `(ProtocolOp.compute (V := b.vocabulary) $rs $op $ts rfl (by simp [shared, verifier, prover, *] at *))

abbrev ready (domain handle : b.vocabulary.Ty) :=
  ((((((((Ctx.empty.extend (names domain)).insert 2 (prover (table b))).insert 3 (shared handle)).insert
    4 (shared (positions b))).insert 5 (prover (.tuple (pair handle)))).insert 6 (shared (rows b))).insert
    7 (verifier (.tuple (claim handle)))).insert 8 (verifier .bool)).insert 9 (verifier .bool)

abbrev inputs : Names [verifier (b := b) .nat,verifier .bool] := .cons 10 (.cons 11 .nil)

def iteration : Term (protocolDialect b.vocabulary hs) ((ready domain handle).extend inputs) [verifier .bool] :=
  .op ⟨9⟩ (calcAt [1] (.owned (.seqAt (scalar b) (some 40) rfl)) [shared (rows b),verifier .nat])
    (args![6,10]) (.cons 12 .nil) <|
  .op ⟨10⟩ (calcAt [1] (.owned (.seqAt (.fin 1024) (some 40) rfl)) [shared (positions b),verifier .nat])
    (args![4,10]) (.cons 13 .nil) <|
  .op ⟨11⟩ (calcAt [1] (.call calls.point) [shared domain,verifier (.fin 1024)])
    (args![1,13]) (.cons 14 .nil) <|
  .op ⟨12⟩ (calcAt [1] (.row (V := b.vocabulary) (.inl (.field .fromNonzero .koalaBear .nonzero)) _ rfl) [verifier (nonzero b)])
    (args![14]) (.cons 15 .nil) <|
  .op ⟨13⟩ (calcAt [1] (.call calls.evaluate) [shared (polynomial b),verifier (scalar b)])
    (args![0,15]) (.cons 16 .nil) <|
  .op ⟨14⟩ (calcAt [1] (.row (V := b.vocabulary) (.inl (.field .equal .koalaBear .all)) _ rfl) [verifier (scalar b),verifier (scalar b)])
    (args![12,16]) (.cons 17 .nil) <|
  .op ⟨15⟩ (calcAt [1] (.owned .boolAnd) [verifier .bool,verifier .bool])
    (args![11,17]) (.cons 18 .nil) (.ret (args![18]))

def loopBody : Term (protocolDialect b.vocabulary hs) (ready domain handle) [] :=
  .loop (each := []) (carried := [verifier .bool]) ⟨16⟩ [1] (.fixed 40) (by simp [verifier])
    (args![9]) inputs (iteration calls handle) (.cons 19 .nil) <|
  .guard ⟨17⟩ [1] (v! 19) ⟨rfl,fun _ h => h,by decide⟩ .reject (.ret .nil)

def withTail (tail : Term (protocolDialect b.vocabulary hs) (ready domain handle) []) : Term (protocolDialect b.vocabulary hs) (Ctx.empty.extend (names domain)) [] :=
  .op ⟨0⟩ (calcAt [0] (.call calls.tabulate) [shared (polynomial b),shared domain])
    (args![0,1]) (.cons 2 .nil) <|
  .op ⟨1⟩ (.given (.request ⟨0⟩) 0 [1] [prover (table b)] handle rfl (by simp [prover]) (by decide))
    (args![2]) (.cons 3 .nil) <|
  .op ⟨2⟩ (.given (V := b.vocabulary) (.coin (.uniform (.seq (.fin 1024) (some 40)))) 1 [0] [] (positions b)
    ⟨_,rfl,rfl,rfl⟩ (by simp) (by decide)) .nil (.cons 4 .nil) <|
  .op ⟨3⟩ (calcAt [0] (.owned (.makeTuple (pair handle))) [shared handle,shared (positions b)])
    (args![3,4]) (.cons 5 .nil) <|
  .op ⟨4⟩ (.given (.request ⟨1⟩) 0 [1] [prover (.tuple (pair handle))] (rows b) rfl (by simp [prover]) (by decide))
    (args![5]) (.cons 6 .nil) <|
  .op ⟨5⟩ (calcAt [1] (.owned (.makeTuple (claim handle))) [shared handle,shared (positions b),shared (rows b)])
    (args![3,4,6]) (.cons 7 .nil) <|
  .op ⟨6⟩ (.given (.request ⟨2⟩) 1 [] [verifier (.tuple (claim handle))] .bool rfl (by simp [verifier]) (by decide))
    (args![7]) (.cons 8 .nil) <|
  .guard ⟨7⟩ [1] (v! 8) ⟨rfl,fun _ h => h,by decide⟩ .reject <|
  .op ⟨8⟩ (calcAt [1] (.literal .bool [1] rfl) []) .nil (.cons 9 .nil) tail

def body := withTail calls handle (loopBody calls handle)

end Zkc.Formal.Written.TableVerifier
