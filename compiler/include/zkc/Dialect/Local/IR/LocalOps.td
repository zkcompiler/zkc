#ifndef ZKC_DIALECT_LOCAL_IR_LOCALOPS_TD
#define ZKC_DIALECT_LOCAL_IR_LOCALOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"
include "mlir/IR/OpAsmInterface.td"
include "mlir/Interfaces/FunctionInterfaces.td"
include "mlir/Interfaces/CallInterfaces.td"

class LocalControlOp<string name> : Op<LocalDialect, name,
    [IsolatedFromAbove, SingleBlock,
     DeclareOpInterfaceMethods<RegionBranchOpInterface,
       ["getEntrySuccessorOperands", "getSuccessorInputs"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site);
  let results = (outs Variadic<AnyType>:$outputs);
  let hasRegionVerifier = 1;
}

def LocalForOp : LocalControlOp<"for"> {
  let description = [{
    Operands are lower, upper, initial carried values (one per result), then
    non-affine captures. Bounds are bound index values (ui64 or plan.data), not
    host MLIR index values. Evaluate bounds once and iterate [lower, upper) by
    one; inverted or equal bounds yield initial values. Runtime bounds and
    iteration limits apply before entering a body; no unsigned subtraction wraps.

    Body arguments are generated induction, carried values, then captures.
    The local_yield carries the next values followed by the unchanged capture
    arguments. Trailing capture forwarding is checked and removed at source
    export; it makes every invariant's entry/backedge mapping explicit to MLIR.
    Alternatively, local.condition takes a leading Boolean continuation flag
    followed by the same yielded values and captures. False returns those values
    without another iteration. An empty range still returns the initial values.
    The operation has no unrolling, speculation, or purity trait.
  }];
  let regions = (region AnyRegion:$body);
}

def LocalIfOp : LocalControlOp<"if"> {
  let description = [{
    Operand zero is a logical bool (i1), or its selected physical wrapper.
    Remaining operands are captures, copied to each isolated region's arguments.
    Both regions are verified; only the selected region executes. Its yield
    supplies every result. Affine captures transfer once at entry, independently
    of which branch is selected. This op is intentionally not speculatable.
  }];
  let regions = (region AnyRegion:$thenRegion, AnyRegion:$elseRegion);
}

def LocalMatchOp : LocalControlOp<"match"> {
  let description = [{
    Operand zero is a local variant; the remaining operands are captures. There
    is one isolated region per declared alternative, in declaration order. Only
    the region of the active alternative executes; its arguments are that
    alternative's payload followed by the captures, so the payload is not a
    successor operand of the variant. A terminal stop inside a region bypasses
    every continuation (docs/spec/ir/variants.md).
  }];
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$site, ArrayAttr:$alternatives);
  let regions = (region VariadicRegion<AnyRegion>:$arms);
}

def LocalYieldOp : Op<LocalDialect, "yield",
    [Terminator, ParentOneOf<["zkc::local::LocalIfOp", "zkc::local::LocalForOp", "zkc::local::LocalMatchOp"]>,
     DeclareOpInterfaceMethods<RegionBranchTerminatorOpInterface,
       ["getMutableSuccessorOperands"]>]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
}

def LocalConditionOp
    : Op<LocalDialect, "condition",
         [Terminator, HasParent<"::zkc::local::LocalForOp">,
          DeclareOpInterfaceMethods<RegionBranchTerminatorOpInterface,
                                    ["getMutableSuccessorOperands"]>]> {
  let arguments = (ins AnyType:$condition, Variadic<AnyType>:$inputs);
}

def OperationBindingOp : Op<LocalDialect, "binding", [Symbol]> {
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$contract,
    ArrayAttr:$arguments, StrAttr:$implementation);
  let hasVerifier = 1;
}

// An endpoint guard remains an ordered occurrence until execution binding.
// The containing closed profile owns placement; Local does not depend on it.
def Local_GuardOp : Op<LocalDialect, "guard", [MemoryEffects<[MemRead, MemWrite]>]> {
  let arguments = (ins I1:$condition, StrAttr:$site);
  let assemblyFormat = "$condition attr-dict";
}

// Executing a literal charges a step and allocates a runtime value.
// It is intentionally neither pure nor speculatable.
def Local_BoolConstantOp : Op<LocalDialect, "bool_constant"> {
  let arguments = (ins BoolAttr:$value, StrAttr:$site);
  let results = (outs I1:$output);
}

def RequireOp : KernelOp<LocalDialect, "exec.require", [OpControlRequire]>;

def ResourceUnitConsumeOp : KernelOp<LocalDialect, "exec.resource_unit_consume", [OpResourceUnitConsume]> {
  let description = [{
    Consumes a resource unit and produces nothing. It must remain even though
    it has no result, since removing it would change the unit's lifetime and the
    observed operation sequence (docs/spec/domains/values.md).
  }];
}

def ResourceUnitCreateOp : KernelOp<LocalDialect, "exec.resource_unit_create", [OpResourceUnitCreate]> {
  let description = [{
    Creates one zero-payload logical resource unit of the slot named by the
    binding. The unit is affine: it can be passed or consumed once and is
    retired with its frame when neither returned nor consumed (docs/spec/domains/values.md).
  }];
}

def ResourceUnitPassOp : KernelOp<LocalDialect, "exec.resource_unit_pass", [OpResourceUnitPass]> {
  let description = [{
    Moves a resource unit into a fresh occurrence of the same slot. The input
    occurrence is consumed; the operation grants no copy (docs/spec/domains/values.md).
  }];
}

def VariantInjectOp : Op<LocalDialect, "variant_inject"> {
  let description = [{
    Builds a local variant value from the payload of one named alternative. Only
    that alternative's payload is stored; no placeholder is created for the
    others, so an affine payload is transferred exactly once
    (docs/spec/ir/variants.md).
  }];
  let arguments = (ins Variadic<AnyType>:$payload, StrAttr:$site, StrAttr:$alternative);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}

// Executable functions deliberately have no inlining, speculation or purity
// contract. Native profiles require bodies.
def Local_FuncOp : Op<LocalDialect, "func",
    [FunctionOpInterface, IsolatedFromAbove, OpAsmOpInterface]> {
  let arguments = (ins SymbolNameAttr:$sym_name,
    TypeAttrOf<FunctionType>:$function_type,
    OptionalAttr<StrAttr>:$sym_visibility,
    OptionalAttr<DictArrayAttr>:$arg_attrs,
    OptionalAttr<DictArrayAttr>:$res_attrs);
  let regions = (region AnyRegion:$body);
  let builders = [OpBuilder<(ins "::llvm::StringRef":$name, "::mlir::FunctionType":$type,
    CArg<"::llvm::ArrayRef<::mlir::NamedAttribute>", "{}">:$attrs)>];
  let extraClassDeclaration = [{
    ::mlir::Region *getCallableRegion() {
      return isExternal() ? nullptr : &getBody();
    }
    ::llvm::ArrayRef<::mlir::Type> getArgumentTypes() {
      return getFunctionType().getInputs();
    }
    ::llvm::ArrayRef<::mlir::Type> getResultTypes() {
      return getFunctionType().getResults();
    }
    static ::llvm::StringRef getDefaultDialect() { return "local"; }
    bool isDeclaration() { return isExternal(); }
  }];
  let hasCustomAssemblyFormat = 1;
  let hasRegionVerifier = 1;
}

def Local_ReturnOp : Op<LocalDialect, "return",
    [Terminator, ReturnLike, HasParent<"::zkc::local::FuncOp">]> {
  let arguments = (ins Variadic<AnyType>:$inputs);
  let assemblyFormat = "attr-dict ($inputs^ `:` type($inputs))?";
  let hasVerifier = 1;
}

class ExecutableCallOp<string name> : Op<LocalDialect, name,
    [CallOpInterface, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs,
    FlatSymbolRefAttr:$callee, StrAttr:$site,
    OptionalAttr<DictArrayAttr>:$arg_attrs, OptionalAttr<DictArrayAttr>:$res_attrs);
  let results = (outs Variadic<AnyType>:$outputs);
  let skipDefaultBuilders = 1;
  let builders = [
    OpBuilder<(ins "::mlir::TypeRange":$outputs, "::mlir::ValueRange":$inputs,
      "::mlir::FlatSymbolRefAttr":$callee, "::mlir::StringAttr":$site), [{
      $_state.addTypes(outputs);
      $_state.addOperands(inputs);
      $_state.addAttribute("callee", callee);
      $_state.addAttribute("site", site);
    }]>,
    OpBuilder<(ins "::mlir::TypeRange":$outputs, "::mlir::ValueRange":$inputs,
      "::llvm::StringRef":$callee, "::llvm::StringRef":$site), [{
      build($_builder, $_state, outputs, inputs,
            ::mlir::FlatSymbolRefAttr::get($_builder.getContext(), callee),
            $_builder.getStringAttr(site));
    }]>
  ];
  let extraClassDeclaration = [{
    operand_range getArgOperands() { return getInputs(); }
    ::mlir::MutableOperandRange getArgOperandsMutable() { return getInputsMutable(); }
    ::mlir::CallInterfaceCallable getCallableForCallee() { return getCalleeAttr(); }
    void setCalleeFromCallable(::mlir::CallInterfaceCallable callee) {
      setCalleeAttr(::llvm::cast<::mlir::FlatSymbolRefAttr>(
          ::llvm::cast<::mlir::SymbolRefAttr>(callee)));
    }
  }];
  let assemblyFormat = "$callee `(` $inputs `)` attr-dict `:` functional-type($inputs, $outputs)";
}

// Preparation realizes this total helper as an ordered, data-only local body.
// The Protocol profile owns helper admission and prohibits executable escape.
def Local_RealizeOp : Op<LocalDialect, "realize",
    [Symbol, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, FlatSymbolRefAttr:$helper,
    TypeAttrOf<FunctionType>:$function_type);
  let assemblyFormat = "$sym_name `=` $helper attr-dict `:` $function_type";
}

// Source-local application is expanded under canonical-expanded-locals/1.
def Local_ApplyOp : ExecutableCallOp<"apply"> { let hasVerifier = 1; }

// One ordered invocation in an endpoint; it retains stop and resource effects.
def Local_CallOp : ExecutableCallOp<"call">;

// Stops the current executable invocation or endpoint. The enclosing profile
// admits its placement; Local IR does not depend on protocol operation classes.
def Local_StopOp : Op<LocalDialect, "stop", [Terminator]> {
  let arguments = (ins StrAttr:$site, StrAttr:$reason);
}

#endif
