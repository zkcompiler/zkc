#ifndef ZKC_DIALECT_KERNEL_IR_KERNELDIALECT_TD
#define ZKC_DIALECT_KERNEL_IR_KERNELDIALECT_TD

include "zkc/Dialect/Base.td"

def KernelDialect : ZKCDialect {
  let name = "kernel";
  let cppNamespace = "::zkc::kernel";
}

#endif
