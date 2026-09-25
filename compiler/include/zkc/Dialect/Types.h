#ifndef ZKC_DIALECT_TYPES_H
#define ZKC_DIALECT_TYPES_H
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Dialect/Algebra/IR/AlgebraDialect.h"
#include "zkc/Dialect/Claim/IR/ClaimDialect.h"
#include "zkc/Dialect/Oracle/IR/OracleDialect.h"
#include "zkc/Dialect/PCS/IR/PCSDialect.h"
#include "zkc/Dialect/PIR/IR/PIRDialect.h"
#include "zkc/Dialect/Plan/IR/PlanDialect.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "zkc/Dialect/Relation/IR/RelationDialect.h"

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/PIR/IR/pirTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Algebra/IR/algebraTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Polynomial/IR/polyTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Plan/IR/planTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/PCS/IR/pcsTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Oracle/IR/oracleTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Claim/IR/claimTypes.h.inc"
#endif
