// Runtime length is a value property; element identity is static.
def TypeSequence : ZKC_Type<"sequence", [TypeParameter], PrivateImmutable, 1, 1>;
def SequenceElement : ZKC_Root<"T", TypeParameter>;
def SequenceValue : ZKC_Apply<TypeSequence, [SequenceElement]>;
class SequenceOperation<string name, list<ZKC_Term> inputs, list<ZKC_Term> outputs>
    : ZKC_Operation<name, [SequenceElement], inputs, outputs> {
  let stage = Construction;
  let commonGeneric = 0;
}
def OpSequenceEmpty : SequenceOperation<"sequence.empty",
    [], [SequenceValue]>;
def OpSequenceAppend : SequenceOperation<"sequence.append",
    [SequenceValue, SequenceElement], [SequenceValue]>;
def OpSequenceLength : SequenceOperation<"sequence.length",
    [SequenceValue], [ZKC_Apply<TypeIndex, []>]>;
def OpSequenceAt : SequenceOperation<"sequence.at",
    [SequenceValue, ZKC_Apply<TypeIndex, []>], [SequenceElement]>;
