#ifndef EXAMPLE_ENVELOPE_SPECIALIZATION
#define EXAMPLE_ENVELOPE_SPECIALIZATION

// Include from Native.td after EnvelopeDialect. This is deliberately an
// ordinary MLIR operation: no KernelOp, logical contract or source export.
def FieldSumChainOp : Op<EnvelopeDialect, "field_sum_chain"> {
  let summary = "ordered two-add field composite with lossless decomposition";
  let description = [{
    Represents (lhs + middle) + rhs, in that order. The first result must
    originally have had exactly one use, as the second addition's left input.
    The two dictionaries and locations retain the complete admitted operations.
    This temporary abstraction has no executable implementation and grants no
    reassociation, speculation, failure-elision or performance claim.
  }];
  // Keep the generated public header independent of built-in type declarations.
  // The rewrite/decomposition applicability checks require one exact FieldType.
  let arguments = (ins AnyType:$lhs, AnyType:$middle, AnyType:$rhs,
    DictionaryAttr:$first_attributes, DictionaryAttr:$second_attributes,
    LocationAttr:$first_location, LocationAttr:$second_location);
  let results = (outs AnyType:$result);
}

#endif
