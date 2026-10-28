module

public import Zkc.Source.Structured.Participant
public import Zkc.Source.Common.Scalar

@[expose] public section

/-! An explicit effect adapter for existing Common contract consumers. Structured
adds indices and vectors; projection of those extra message sorts refuses. The
Schnorr source equation proves that its verifier uses only the common fragment.
No relation annotation or native execution claim is supplied by this adapter. -/
namespace Zkc.Source.Structured.CommonAdapter

abbrev commonInterface (F G : Type) : PIR.Signature :=
  Participant.interface Nat Common.Native.Ty Common.Native.services (Common.Native.ScalarValue F G)

def embed {F G : Type} : PIR.OperationInterpretation
    (commonInterface F G) (participantInterface F G)
  | .send (ty := .boolean) site receiver value => .call (.send (ty := .boolean) site receiver value) .done
  | .send (ty := .field domain) site receiver value => .call (.send (ty := .field domain) site receiver value) .done
  | .send (ty := .group domain) site receiver value => .call (.send (ty := .group domain) site receiver value) .done
  | .send (ty := .service contract) site receiver value =>
    .call (.send (ty := .service contract) site receiver value) .done
  | .receive .boolean site sender => .call (.receive .boolean site sender) .done
  | .receive (.field domain) site sender => .call (.receive (.field domain) site sender) .done
  | .receive (.group domain) site sender => .call (.receive (.group domain) site sender) .done
  | .receive (.service contract) site sender => .call (.receive (.service contract) site sender) .done
  | .query site field (.cons handle .nil) => .call (.query site field (.cons handle .nil)) .done

def project {F G : Type} : PIR.OperationInterpretation
    (participantInterface F G) (commonInterface F G)
  | .send (ty := .boolean) site receiver value => .call (.send (ty := .boolean) site receiver value) .done
  | .send (ty := .field domain) site receiver value => .call (.send (ty := .field domain) site receiver value) .done
  | .send (ty := .group domain) site receiver value => .call (.send (ty := .group domain) site receiver value) .done
  | .send (ty := .service contract) site receiver value =>
    .call (.send (ty := .service contract) site receiver value) .done
  | .send (ty := .index) .. | .send (ty := .vector _) ..
  | .send (ty := .indices) .. | .send (ty := .groups _) ..
  | .send (ty := .oracle _) .. | .send (ty := .oracleSequence ..) ..
  | .send (ty := .sequence _) .. | .send (ty := .product ..) .. => .halt .refused
  | .receive .boolean site sender => .call (.receive .boolean site sender) .done
  | .receive (.field domain) site sender => .call (.receive (.field domain) site sender) .done
  | .receive (.group domain) site sender => .call (.receive (.group domain) site sender) .done
  | .receive (.service contract) site sender => .call (.receive (.service contract) site sender) .done
  | .receive .index .. | .receive (.vector _) ..
  | .receive .indices .. | .receive (.groups _) ..
  | .receive (.oracle _) .. | .receive (.oracleSequence ..) ..
  | .receive (.sequence _) .. | .receive (.product ..) .. => .halt .refused
  | .query site field (.cons handle .nil) => .call (.query site field (.cons handle .nil)) .done

theorem project_embed_operation {F G : Type} (op : (commonInterface F G).Op) :
    (embed op).interpret project = .call op .done := by
  cases op with
  | send site receiver value =>
    rename_i ty
    cases ty <;> rfl
  | receive ty site sender => cases ty <;> rfl
  | query site field args =>
    cases args with
    | cons handle rest => cases rest; rfl

/-- Embedding and projecting a common process preserves every continuation and
stop, not merely a successful transcript. -/
theorem project_embed {F G A : Type} (process : PIR.Process (commonInterface F G) A) :
    (process.interpret embed).interpret project = process := by
  rw [PIR.Process.interpret_comp]
  have operations : (fun op => (embed op).interpret project) =
      (fun op : (commonInterface F G).Op => PIR.Process.call op PIR.Process.done) := by
    funext op
    exact project_embed_operation op
  rw [operations, PIR.Process.interpret_identity]

end Zkc.Source.Structured.CommonAdapter
