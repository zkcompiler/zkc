// Arithmetic consumers of two distinct rank-one relations and a finite AIR.
// This diagnostic example checks composition; it is not a proof protocol.
module {
  relation Circuit = r1cs("multiply.r1cs.json");
  relation Scaled = r1cs("scaled.r1cs.json");
  relation Trace = air("squaring.air.json");
  derive Rows = rank_one(Circuit, public_matrices);
  derive Fixed = rank_one(Scaled, specialized);
  derive Steps = arithmetic(Trace, specialized, 3);

  protocol RankOne {
    roles (P);
    inputs (P a: Matrix<bn254.fr::Element>, P b: Matrix<bn254.fr::Element>,
            P c: Matrix<bn254.fr::Element>, P statement: Vector<bn254.fr::Element>,
            P witness: Vector<bn254.fr::Element>);
    outputs (P Vector<bn254.fr::Element>);
    local P: let assignment = Rows_Assemble(statement, witness);
    local P: let (az, bz, cz) = Rows_Products(a, b, c, assignment);
    local P: let residuals = Rows_Residuals(az, bz, cz);
    return residuals;
  }

  protocol FixedRankOne {
    roles (P);
    inputs (P statement: Vector<bn254.fr::Element>, P witness: Vector<bn254.fr::Element>);
    outputs (P Vector<bn254.fr::Element>);
    local P: let assignment = Fixed_Assemble(statement, witness);
    local P: let (az, bz, cz) = Fixed_Products(assignment);
    local P: let residuals = Fixed_Residuals(az, bz, cz);
    return residuals;
  }

  protocol ArithmeticTrace {
    roles (P);
    inputs (P statement: Vector<bn254.fr::Element>, P trace: Vector<bn254.fr::Element>);
    outputs (P Vector<bn254.fr::Element>);
    local P: let residuals = Steps_Evaluate(statement, trace);
    return residuals;
  }

  protocol Compare {
    roles (P);
    inputs (P a: Matrix<bn254.fr::Element>, P b: Matrix<bn254.fr::Element>,
            P c: Matrix<bn254.fr::Element>, P first: Vector<bn254.fr::Element>,
            P second: Vector<bn254.fr::Element>, P witness: Vector<bn254.fr::Element>,
            P initial: Vector<bn254.fr::Element>, P trace: Vector<bn254.fr::Element>);
    outputs (P Vector<bn254.fr::Element>, P Vector<bn254.fr::Element>,
             P Vector<bn254.fr::Element>);
    dependencies (first_check: RankOne(), second_check: FixedRankOne(), trace_check: ArithmeticTrace());
    invoke first_check(a, b, c, first, witness) -> (first_residuals);
    invoke second_check(second, witness) -> (second_residuals);
    invoke trace_check(initial, trace) -> (trace_residuals);
    return (first_residuals, second_residuals, trace_residuals);
  }

  instance first: RankOne { roles (P = P); }
  instance second: FixedRankOne { roles (P = P); }
  instance trace: ArithmeticTrace { roles (P = P); }
  instance root: Compare {
    dependencies (first_check = first, second_check = second, trace_check = trace);
    roles (P = P);
  }
  entry main = root;
}
