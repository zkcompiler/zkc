import Zkc.Algebra.RingExpression
import Zkc.Algebra.RingExpression.Sharing
import Zkc.Algebra.RingExpression.Pointwise
import Zkc.Relation.AIR.RingExpression
import Tools.DeclarationAudit

set_option autoImplicit false

-- Each theorem is checked transitively, including private/generated helpers.
-- This audit does not connect native arrays, packed lanes, vectors or JSON to
-- the model.
run_cmd Tools.DeclarationAudit.check [
  `Zkc.Algebra.RingExpression, `Zkc.Algebra.RingExpression.Sharing,
  `Zkc.Algebra.RingExpression.Pointwise, `Zkc.Relation.AIR.RingExpression] "RING-EXPRESSION-AUDIT-PASS" true

#print axioms Zkc.Algebra.RingExpression.Expr.eval_substitute
#print axioms Zkc.Algebra.RingExpression.Expr.eval_lanes
#print axioms Zkc.Algebra.RingExpression.Expr.polynomial_eval
#print axioms Zkc.Algebra.RingExpression.Expr.polynomial_degree
#print axioms Zkc.Algebra.RingExpression.Arena.unfold_hom
#print axioms Zkc.Algebra.RingExpression.Arena.unfold_stable
#print axioms Zkc.Algebra.RingExpression.Arena.outputs_hom
#print axioms Zkc.Algebra.RingExpression.Arena.unfold_homOn
#print axioms Zkc.Algebra.RingExpression.map_coordinate
#print axioms Zkc.Algebra.RingExpression.map_shape
#print axioms Zkc.Algebra.RingExpression.map_substitute
#print axioms Zkc.Algebra.RingExpression.map_hoist
#print axioms Zkc.Algebra.RingExpression.map_polynomial
#print axioms Zkc.Algebra.RingExpression.interpolate_polynomial
#print axioms Zkc.Algebra.RingExpression.interpolate_ne_polynomial
#print axioms Zkc.Relation.AIR.Expr.toRing_eval
#print axioms Zkc.Relation.AIR.Expr.toRing_polynomial
