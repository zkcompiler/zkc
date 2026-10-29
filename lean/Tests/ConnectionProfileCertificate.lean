import Tests.ConnectionHelperCertificate
import Zkc.Source.Structured.UnitViews

/-! An admitted straight-line Schnorr-shaped protocol, connected in both
profiles and roles by the common finite proposer. Admission and connection are
separate receipts; no group law, honest reply, or randomness premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
namespace Tests.ConnectionProfileCertificate
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def field : Ty := .field "bls12-381.fr"
def group : Ty := .group "bls12-381.g1"
def service : Ty := .service "random.bls12-381.fr/0"
def inputs : List Ty := [group, group, field, service, service]
def outputs : List Ty := [.boolean, field]

def protocol : Function :=
  ⟨"Schnorr", .protocol, .publicDef, inputs, outputs,
    some ⟨["P", "V"], [["P", "V"], ["P", "V"], ["P"], ["P"], ["V"]], [["V"], ["P", "V"]]⟩,
    [], some (.protocol ⟨"certificateSchnorr", []⟩), .block [
      .instruction (.draw "P" "bls12-381.fr") [3] [field] [] "nonce",
      .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [1, 0] [group] [] "",
      .instruction (.exchange "P" "V") [0] [group] [] "commitment",
      .instruction (.draw "V" "bls12-381.fr") [7] [field] [] "challenge",
      .instruction (.exchange "V" "P") [0] [field] [] "delivery",
      .instruction (.fieldMultiply "bls12-381.fr") [0, 7] [field] [] "",
      .instruction (.fieldAdd "bls12-381.fr") [5, 0] [field] [] "",
      .instruction (.exchange "P" "V") [0] [field] [] "response",
      .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [8, 0] [group] [] "",
      .instruction (.groupScale "bls12-381.g1" "bls12-381.fr") [10, 4] [group] [] "",
      .instruction (.groupAdd "bls12-381.g1") [7, 0] [group] [] "",
      .instruction (.groupEqual "bls12-381.g1") [2, 0] [.boolean] [] "",
      .instruction (.guard "V") [0] [] [] "check"] (.ret [0, 4])⟩

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "Schnorr"
  domains := []
  relations := []
  bindings := []
  definitions := [.function protocol]
  contracts := [⟨"Schnorr", []⟩]
  catalogue := blsCatalogue

def schnorrSignature : ProtocolSignature :=
  ⟨"Schnorr", ["P", "V"], inputs, outputs, [[0, 1], [0, 1], [0], [0], [1]], [[1], [0, 1]]⟩
def schnorrBody : Region protocolDialect inputs outputs :=
  .letOp (.mark "nonce") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "nonce") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "commitment") .nil .nil <|
  .letOp (.exchange group 0 1 "commitment") (.cons .here .nil) .nil <|
  .letOp (.mark "challenge") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "challenge") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil <|
  .letOp (.mark "delivery") .nil .nil <|
  .letOp (.exchange field 1 0 "delivery") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "response") .nil .nil <|
  .letOp (.exchange field 0 1 "response") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual "bls12-381.g1") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "check") .nil .nil <|
  .letOp (.guard 1 "check") (.cons .here .nil) .nil <|
  .ret (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))

structured_views snapshot helpers [] protocols [schnorr]
theorem admitted : check snapshot = .ok program := kernel_admission
def source : CheckedProtocol := schnorrDefinition

def context : Context := .fiatShamir "Schnorr" ["P", "V"] 0 1 4
  "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) "suite" [("challenge", "delivery")]
def message (site sender receiver : String) : Template :=
  ⟨"Schnorr", [], ["message", "Schnorr", site, site, sender, receiver]⟩
def draw : Template := ⟨"Schnorr", [], ["query", "Schnorr", "challenge", "input_4", "random.bls12-381.fr/0", "draw", "V"]⟩
def nonce : Template := ⟨"Schnorr", [], ["query", "Schnorr", "nonce", "input_3", "random.bls12-381.fr/0", "draw", "P"]⟩
def port : ServicePort := ⟨"service_3", "P", 3, 3, "random.bls12-381.fr/0"⟩
def routing (mode : Domain.Mode) : Original.Routing :=
  ⟨snapshot, context, mode, 73,
    [message "commitment" "P" "V", message "delivery" "V" "P", message "response" "P" "V"],
    [draw], [⟨draw, message "delivery" "V" "P"⟩], [⟨99, port, nonce⟩]⟩

def producerPattern : InputPattern inputs :=
  .cons .present (.cons .present (.cons .present (.cons (.capability "random.bls12-381.fr/0" 99) (.cons .absent .nil))))
def validatorPattern : InputPattern inputs :=
  .cons .present (.cons .present (.cons .absent (.cons .absent (.cons (.capability "random.bls12-381.fr/0" 73) .nil))))
def producerLayout : Layout producerPattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))),
    .data (.present (.var (.there (.there .here)))), .history "suite"]
def validatorLayout : Layout validatorPattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))), .history "suite"]

def producerView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.localService context port (.draw "bls12-381.fr") nonce [] [] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.groupScale "bls12-381.g1" "bls12-381.fr") [0, 5] [.data group]) <|
  Domain.View.sequence (Domain.View.send "commitment" "commitment" "V" 6 []) <|
  Domain.View.sequence (Domain.View.observe context "suite" (message "commitment" "P" "V") 3 6 4 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.challenge context "suite" "bls12-381.fr" draw 7 4 [.data field, .transcript "suite"]) <|
  Domain.View.sequence (Domain.View.observe context "suite" (message "delivery" "V" "P") 9 8 4 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.calculation model (.fieldMultiply "bls12-381.fr") [8, 2] [.data field]) <|
  Domain.View.sequence (Domain.View.calculation model (.fieldAdd "bls12-381.fr") [5, 11] [.data field]) <|
  Domain.View.sequence (Domain.View.send "response" "response" "V" 12 []) <|
  Domain.View.sequence (Domain.View.observe context "suite" (message "response" "P" "V") 10 12 4 [.transcript "suite"])
    Domain.View.empty

def validatorView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.receive "commitment" "commitment" "P" group [.data group]) <|
  Domain.View.sequence (Domain.View.observe context "suite" (message "commitment" "P" "V") 2 4 3 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.challenge context "suite" "bls12-381.fr" draw 5 3 [.data field, .transcript "suite"]) <|
  Domain.View.sequence (Domain.View.observe context "suite" (message "delivery" "V" "P") 7 6 3 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.receive "response" "response" "P" field [.data field]) <|
  Domain.View.sequence (Domain.View.observe context "suite" (message "response" "P" "V") 8 9 3 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.calculation model (.groupScale "bls12-381.g1" "bls12-381.fr") [0, 9] [.data group]) <|
  Domain.View.sequence (Domain.View.calculation model (.groupScale "bls12-381.g1" "bls12-381.fr") [1, 6] [.data group]) <|
  Domain.View.sequence (Domain.View.calculation model (.groupAdd "bls12-381.g1") [4, 12] [.data group]) <|
  Domain.View.sequence (Domain.View.calculation model (.groupEqual "bls12-381.g1") [11, 13] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.guard 14 []) Domain.View.empty

def producerAccepted : Certificate (routing .producer) {} [] 0 2 source producerPattern
    [.absent, .data 12] (some 13) [] producerLayout producerView := by derive_connection_alignment

def validatorAccepted : Certificate (routing .validator) {} [] 1 2 source validatorPattern
    [.data 14, .data 9] (some 10) [] validatorLayout validatorView := by derive_connection_alignment

-- The successful comparison cell supplies the normalized true output. It
-- cannot discharge an unrelated residual field, role or profile history.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Certificate (routing .validator) {} [] 1 2 source validatorPattern
    [.data 14, .data 6] (some 10) [] validatorLayout validatorView := by derive_connection_alignment

example : True := by
  fail_if_success
    have : Certificate (routing .producer) {} [] 0 2 source producerPattern
        [.data 14, .data 9] (some 10) [] producerLayout validatorView := by derive_connection_alignment
  trivial

example : True := by
  fail_if_success
    have : Certificate (routing .validator) {} [] 1 2 source validatorPattern
        [.data 14, .data 9] none [] validatorLayout validatorView := by derive_connection_alignment
  trivial

example : True := by
  fail_if_success
    have : Certificate (routing .validator) {} [] 1 2 source validatorPattern
        [.data 14, .data 9] (some 7) [] validatorLayout validatorView := by derive_connection_alignment
  trivial

end Tests.ConnectionProfileCertificate
