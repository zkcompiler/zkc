module

public import Zkc.Protocols.Sigma.Source

@[expose] public section

/-! Reusable source schedules for randomized module protocols. Nominal types,
role names, statement associations and effect sites are instance data. The
bodies retain actual private draws, ordered messages and complete returns. -/
set_option autoImplicit false
namespace Zkc.Protocols.Sigma.Source
open Zkc.Source Zkc.Source.Structured

structure Metadata where
  name : String
  prover : String
  validator : String
  statement : Option String := none

structure Sites where
  nonce : String
  secondNonce : String
  commitment : String
  secondCommitment : String
  challenge : String
  delivery : String
  response : String
  secondResponse : String

/-- A retained statement is an annotation, with its exact operands and roles.
It is part of body association even though the open execution is silent here. -/
def annotate {inputs outputs : List Ty} (metadata : Metadata) (types : List Ty)
    (selectors : List String) (arguments : Operands inputs types)
    (next : Region protocolDialect inputs outputs) : Region protocolDialect inputs outputs :=
  match metadata.statement with
  | none => next
  | some relation => .letOp (.mark "") .nil .nil <|
      .letOp (.statement relation types selectors 0) arguments .nil next

def singleSignature (d : Domains) (metadata : Metadata) : ProtocolSignature where
  name := metadata.name
  roles := [metadata.prover, metadata.validator]
  inputs := [.group d.group, .group d.group, .field d.scalar, .service ("random." ++ d.scalar ++ "/0"), .service ("random." ++ d.scalar ++ "/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0], [0], [1]]
  outputScopes := [[1]]

def singleBody (d : Domains) (metadata : Metadata) (sites : Sites) :
    Region protocolDialect (singleSignature d metadata).inputs [.boolean] :=
  annotate metadata [.group d.group, .group d.group, .field d.scalar]
    [metadata.validator, metadata.validator, metadata.prover] (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) <|
  .letOp (.mark sites.nonce) .nil .nil <|
  .letOp (.draw 0 d.scalar sites.nonce) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark sites.commitment) .nil .nil <|
  .letOp (.exchange (.group d.group) 0 1 sites.commitment) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group d.group) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark sites.challenge) .nil .nil <|
  .letOp (.draw 1 d.scalar sites.challenge) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil <|
  .letOp (.mark sites.delivery) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 1 0 sites.delivery) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply d.scalar) rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark sites.response) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 0 1 sites.response) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd d.group) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual d.group) rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def independentSignature (d : Domains) (metadata : Metadata) : ProtocolSignature where
  name := metadata.name
  roles := [metadata.prover, metadata.validator]
  inputs := [.group d.group, .group d.group, .group d.group, .group d.group, .field d.scalar, .field d.scalar, .service ("random." ++ d.scalar ++ "/0"), .service ("random." ++ d.scalar ++ "/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0, 1], [0, 1], [0], [0], [0], [1]]
  outputScopes := [[1]]

def independentBody (d : Domains) (metadata : Metadata) (sites : Sites) :
    Region protocolDialect (independentSignature d metadata).inputs [.boolean] :=
  annotate metadata [.group d.group, .group d.group, .group d.group, .group d.group, .field d.scalar, .field d.scalar]
    [metadata.validator, metadata.validator, metadata.validator, metadata.validator, metadata.prover, metadata.prover] (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) <|
  .letOp (.mark sites.nonce) .nil .nil <|
  .letOp (.draw 0 d.scalar sites.nonce) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark sites.secondNonce) .nil .nil <|
  .letOp (.draw 0 d.scalar sites.secondNonce) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there .here)) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark sites.commitment) .nil .nil <|
  .letOp (.exchange (.group d.group) 0 1 sites.commitment) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group d.group) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark sites.secondCommitment) .nil .nil <|
  .letOp (.exchange (.group d.group) 0 1 sites.secondCommitment) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group d.group) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark sites.challenge) .nil .nil <|
  .letOp (.draw 1 d.scalar sites.challenge) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil <|
  .letOp (.mark sites.delivery) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 1 0 sites.delivery) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply d.scalar) rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark sites.response) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 0 1 sites.response) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply d.scalar) rfl) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark sites.secondResponse) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 0 1 sites.secondResponse) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd d.group) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual d.group) rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd d.group) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual d.group) rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanAnd rfl) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def sharedSignature (d : Domains) (metadata : Metadata) : ProtocolSignature where
  name := metadata.name
  roles := [metadata.prover, metadata.validator]
  inputs := [.group d.group, .group d.group, .group d.group, .group d.group, .field d.scalar, .service ("random." ++ d.scalar ++ "/0"), .service ("random." ++ d.scalar ++ "/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0, 1], [0, 1], [0], [0], [1]]
  outputScopes := [[1]]

def sharedBody (d : Domains) (metadata : Metadata) (sites : Sites) :
    Region protocolDialect (sharedSignature d metadata).inputs [.boolean] :=
  annotate metadata [.group d.group, .group d.group, .group d.group, .group d.group, .field d.scalar]
    [metadata.validator, metadata.validator, metadata.validator, metadata.validator, metadata.prover] (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) <|
  .letOp (.mark sites.nonce) .nil .nil <|
  .letOp (.draw 0 d.scalar sites.nonce) (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark sites.commitment) .nil .nil <|
  .letOp (.exchange (.group d.group) 0 1 sites.commitment) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group d.group) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark sites.secondCommitment) .nil .nil <|
  .letOp (.exchange (.group d.group) 0 1 sites.secondCommitment) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group d.group) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark sites.challenge) .nil .nil <|
  .letOp (.draw 1 d.scalar sites.challenge) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil) .nil <|
  .letOp (.mark sites.delivery) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 1 0 sites.delivery) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply d.scalar) rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark sites.response) .nil .nil <|
  .letOp (.exchange (.field d.scalar) 0 1 sites.response) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field d.scalar) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd d.group) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual d.group) rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale d.group d.scalar) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd d.group) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual d.group) rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanAnd rfl) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end Zkc.Protocols.Sigma.Source
