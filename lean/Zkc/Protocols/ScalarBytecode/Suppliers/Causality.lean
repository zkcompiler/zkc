import Zkc.Protocols.ScalarBytecode.Suppliers.Representations

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Suppliers
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint

def afterNotice {S : Type} (supplier : Supplier S) (k : Key) (c : Bool) (s : S) : Bytes :=
  (supplier.read k 2 (supplier.challenge k (if c then 1 else 0) s)).1.val

/-- One bounded reply can always be replayed by a tape. This deliberately weak
    property says nothing about joint calls, causality or pre-notice fixation. -/
theorem one_reply_has_tape {S : Type} (supplier : Supplier S) (k : Key) (c : Bool) (s : S) :
    ∃ bs : Bytes, afterNotice supplier k c s = afterNotice bufferSupplier k c bs := by
  refine ⟨afterNotice supplier k c s,?_⟩
  exact (List.take_of_length_le (supplier.read k 2
    (supplier.challenge k (if c then 1 else 0) s)).1.property).symm

theorem each_notice_has_tape (k : Key) :
    ∀ c : Bool, ∃ bs : Bytes,
      afterNotice adaptive k c ⟨0,false⟩ = afterNotice bufferSupplier k c bs := by
  intro c
  exact one_reply_has_tape adaptive k c ⟨0,false⟩

theorem no_notice_insensitive_match {S : Type} (supplier : Supplier S)
    (insensitive : ∀ k n s, supplier.challenge k n s = s) (k : Key) :
    ¬ ∃ s : S, ∀ c : Bool,
      afterNotice adaptive k c ⟨0,false⟩ = afterNotice supplier k c s := by
  rintro ⟨s,h⟩
  have h0 := h false
  have h1 := h true
  simp only [afterNotice,adaptive,insensitive,Bool.false_eq_true,↓reduceIte] at h0 h1
  exact (by decide : Zkc.Protocols.ScalarBytecode.Codec.enc 0 ≠ Zkc.Protocols.ScalarBytecode.Codec.enc 1) (h0.trans h1.symm)

theorem no_uniform_pre_notice_tape (k : Key) :
    ¬ ∃ bs : Bytes, ∀ c : Bool,
      afterNotice adaptive k c ⟨0,false⟩ = afterNotice bufferSupplier k c bs := by
  exact no_notice_insensitive_match bufferSupplier (by intros; rfl) k

end Zkc.Protocols.ScalarBytecode.Suppliers
