module

public import Zkc.Core.Program.Identity

@[expose] public section

/-! Stored Boolean expressions, lemma signatures and annotations at lexical program sites. -/

namespace Zkc.Core.BodyAnalysis

/-! ## Expressions -/

mutual
  /-- An expression over positions: a position, or the result at an index of a written
  operation applied to expressions. -/
  inductive Expr (Raw : Type) where
    | arg (position : Nat)
    | apply (written : Raw) (operands : Exprs Raw) (result : Nat)
    deriving DecidableEq
  /-- Expressions, in order. -/
  inductive Exprs (Raw : Type) where
    | nil
    | cons (first : Expr Raw) (others : Exprs Raw)
    deriving DecidableEq
end

/-! ## Contracts -/

/-- A Boolean condition and any finite upper bound that must be available when deciding it. -/
structure ContractClause (Raw : Type) where
  assertion : Expr Raw
  staticBound : Option (Expr Raw) := none
  deriving DecidableEq

structure Contract (Raw : Type) where
  preconditions : List (ContractClause Raw)
  postconditions : List (ContractClause Raw)
  deriving DecidableEq

/-- A lemma over a declared argument context. Types are part of the theorem, not logical
premises that an analysis must rediscover. -/
structure Lemma (T Raw : Type) where
  parameters : List T
  premises : List (Expr Raw)
  conclusion : Expr Raw

/-- What is stated at an instruction beyond the requirements of its operation. The positions
of its assertions are the names it lists, in order; for an invariant they are followed by the
loop's index and its carried values. -/
inductive Annotation (Raw : Type) where
  /-- Of a loop: it holds of the initial values, the body keeps it, and it is then known in the
  body and after the loop. Decided by the domains. -/
  | invariant (uses : List Name) (assertions : List (Expr Raw))
  /-- An instance of a lemma of the list given to the analysis, on the names given for its
  positions: the premises are decided, the conclusion is learned. It applies at the entry of
  the instruction. -/
  | step (lemma : Nat) (names : List Name)
  /-- A fact that another producer proves: it is learned, and that it holds at the entry of
  the instruction is a hypothesis of the soundness. -/
  | fact (uses : List Name) (assertion : Expr Raw)
  deriving DecidableEq

/-- Only a supplied fact needs a proof about its reached environment. The checker
establishes the premises of steps and the initialization and preservation of invariants. -/
def Annotation.isGiven {Raw : Type} : Annotation Raw → Bool
  | .fact .. => true
  | .step .. | .invariant .. => false

/-- A region is named by its enclosing region, the parent's ordinal, and the selected edge.
Case arms have their own ordinals. A block frame also retains its unrolling number. -/
inductive StaticRegion where
  | root
  | body (parent : StaticRegion) (ordinal : Nat) (key : Key)
  | otherwise (parent : StaticRegion) (ordinal : Nat) (key : Key)
  | arm (parent : StaticRegion) (ordinal : Nat)
  | block (parent : StaticRegion) (ordinal : Nat) (key : Key) (number : Nat)
  deriving DecidableEq

/-- Advancing to a sibling increments one ordinal. The size of its location depends only on
the nesting depth, including for long sequences of instructions. -/
structure StaticCursor where
  enclosing : StaticRegion
  ordinal : Nat
  deriving DecidableEq

namespace StaticCursor

def root : StaticCursor := ⟨.root, 0⟩
def next (c : StaticCursor) : StaticCursor := { c with ordinal := c.ordinal + 1 }
def region (c : StaticCursor) (key : Key) : StaticCursor := ⟨.body c.enclosing c.ordinal key, 0⟩
def otherwise (c : StaticCursor) (key : Key) : StaticCursor :=
  ⟨.otherwise c.enclosing c.ordinal key, 0⟩
def arm (c : StaticCursor) : StaticCursor := ⟨.arm c.enclosing c.ordinal, 0⟩
def block (c : StaticCursor) (key : Key) (number : Nat) : StaticCursor :=
  ⟨.block c.enclosing c.ordinal key number, 0⟩

end StaticCursor

/-- The block projection used by existing bounds and diagnostics. -/
def StaticRegion.blocks : StaticRegion → List (Key × Nat)
  | .root => []
  | .body p .. | .otherwise p .. | .arm p .. => p.blocks
  | .block p _ key n => p.blocks ++ [(key, n)]

def StaticCursor.blocks (c : StaticCursor) : List (Key × Nat) := c.enclosing.blocks

/-- A resolved entry, within one definition and role. A block's own number belongs to its
entry even though its annotations read the incoming environment. -/
inductive AnnotationSite where
  | instruction (cursor : StaticCursor) (key : Key)
  | block (cursor : StaticCursor) (key : Key) (number : Nat)
  deriving DecidableEq

/-- The diagnostic projection retains the entry number of a numbered block. -/
def AnnotationSite.toPlace (site : AnnotationSite) (definition : Key) (role : Option Role) : Place :=
  match site with
  | .instruction cursor key => ⟨definition, cursor.blocks, some key, role⟩
  | .block cursor key number => ⟨definition, (cursor.block key number).blocks, some key, role⟩

/-- Ordered annotations for resolved entries in one definition and role. -/
abbrev Annotations (Raw : Type) := List (AnnotationSite × Annotation Raw)

def Annotations.at_ {Raw : Type} (annotations : Annotations Raw) (site : AnnotationSite) :
    List (Annotation Raw) :=
  (annotations.filter fun entry => entry.1 = site).map (·.2)

end Zkc.Core.BodyAnalysis
