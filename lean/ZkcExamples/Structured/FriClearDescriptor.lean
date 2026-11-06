module

public import Zkc.Executable.DescriptorEvents

@[expose] public section

/-! Generated from the selected proof entry's native descriptor by the subject bridge. -/
namespace ZkcExamples.Structured.FriClearDescriptor

def original : String := "sha256:1d2d1852b3c5d97d1e3b03b9867ec8308cf795576edf7fe31722ea54bb65891c"

def policy : Zkc.Construction.Policy := ⟨"s7h6578616d706c653h467269", "role00000000", "role00000001", 0, "merlin3.koala-bear.ext8-binomial3.rejection31le/0", [4], [1, 2, 3], [("apply_13_apply_2_s0_s0_s54", "apply_13_apply_2_s0_s0_s56_0"), ("apply_31_apply_2_s0_label_71756572696573_s13", "apply_31_apply_2_s0_label_71756572696573_s15_0")], "zkc.framed/0", ""⟩

def events : List Zkc.Executable.Descriptor.Event := [
  ⟨⟨"s7h6578616d706c653h467269", [.apply "s7h6578616d706c653h467269" "s0", .apply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" "s0", .repeat "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404" "s46"], ["message", "zkc.oracle.f5a9aeeed1df4b10a55da025b8aab0fa7afe4817103a0e184be682fba28d1db3", "oracle_0_7_deliver", "oracle_0_7_deliver", "role00000000", "role00000001"]⟩, .message "vector:koala-bear.ext8-binomial3" "zkc.native-data/0"⟩,
  ⟨⟨"s7h6578616d706c653h467269", [.apply "s7h6578616d706c653h467269" "s0", .apply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" "s0", .repeat "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404" "s46"], ["query", "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404", "s54", "input_4", "random.koala-bear.ext8-binomial3/0", "draw", "role00000001"]⟩, .draw⟩,
  ⟨⟨"s7h6578616d706c653h467269", [.apply "s7h6578616d706c653h467269" "s0", .apply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" "s0", .repeat "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404" "s46"], ["message", "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404", "s56_0", "s56_0", "role00000001", "role00000000"]⟩, .message "field:koala-bear.ext8-binomial3" "zkcv.field.koala-bear.ext8-binomial3/0"⟩,
  ⟨⟨"s7h6578616d706c653h467269", [.apply "s7h6578616d706c653h467269" "s0", .apply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" "s0"], ["message", "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404", "s125_0", "s125_0", "role00000000", "role00000001"]⟩, .message "vector:koala-bear.ext8-binomial3" "zkc.native-data/0"⟩,
  ⟨⟨"s7h6578616d706c653h467269", [.apply "s7h6578616d706c653h467269" "s0", .apply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" "label_71756572696573", .repeat "zkl_5bdb55a745abe137c9027bb7f7baa1d02e1dde834266d27198609cdbce18f830" "s12"], ["query", "zkl_5bdb55a745abe137c9027bb7f7baa1d02e1dde834266d27198609cdbce18f830", "s13", "input_1", "random.koala-bear.ext8-binomial3/0", "index", "role00000001"]⟩, .index 32⟩,
  ⟨⟨"s7h6578616d706c653h467269", [.apply "s7h6578616d706c653h467269" "s0", .apply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" "label_71756572696573", .repeat "zkl_5bdb55a745abe137c9027bb7f7baa1d02e1dde834266d27198609cdbce18f830" "s12"], ["message", "zkl_5bdb55a745abe137c9027bb7f7baa1d02e1dde834266d27198609cdbce18f830", "s15_0", "s15_0", "role00000001", "role00000000"]⟩, .message "index" "zkcv.index/0"⟩]

end ZkcExamples.Structured.FriClearDescriptor
