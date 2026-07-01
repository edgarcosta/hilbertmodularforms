// test-time: ~40s
//
// Regression test: cubic trace-formula dimensions must be integers and agree
// with the builtin backend.
//
// The Eichler-Selberg trace formula in ModFrmHilD/Trace/Trace.m was only ever
// validated for real quadratic fields (see Tests/dimensions.m, Tests/traces.m,
// and pos_elts_of_trace.m which asserts Degree(F) eq 2). For the cyclic cubic
// field F = Q(zeta_7)^+ (disc 49) it returns non-integer "dimensions": the CM
// extension Q(zeta_7)/F contributes elliptic points of order 7 whose 1/7 weight
// (via ClassNumberOverUnitIndex, from the 14th roots of unity) is not cancelled.
//
// Concretely HilbertSeries(F, 2*ZF) has coefficients 20/7 at weight 2 and 36/7
// at weight 4, so on the broken backend:
//   * CuspDimension(: version := "trace") throws (Integers()!<rational>), and
//   * ComputePrecisionFromHilbertSeries(2*ZF, k) throws for k in {2,4}.
// The builtin backend gives the correct dim M_2 = 2 and dim M_4 = 6.
//
// The fix routes degree != 2 through the builtin dimension, so the trace path
// no longer throws and agrees with builtin.

Qx<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1); // Q(zeta_7)^+, disc 49
ZF := Integers(F);
NN := 2*ZF;

assert Degree(F) eq 3;
assert Discriminant(ZF) eq 49;
assert NarrowClassNumber(F) eq 1; // rules out class-group-character effects

R := GradedRingOfHMFs(F, 1);

// Known-correct dimensions (Magma builtin, cross-checked against arXiv:2501.15719
// Table tab:positive-kod for the D=49 level-(2) target).
expected_cusp := AssociativeArray();
expected_cusp[2] := 0;
expected_cusp[4] := 4;
expected_total := AssociativeArray();
expected_total[2] := 2;
expected_total[4] := 6;

for k in [2, 4] do
    Mk := HMFSpace(R, NN, [k, k, k]);

    // Default CuspDimension path uses version := "trace"; on the broken backend
    // this throws for the cubic field. After the fix it must return the builtin value.
    cusp_trace := CuspDimension(Mk : version := "trace");
    delete Mk`CuspDimension;
    cusp_builtin := CuspDimension(Mk : version := "builtin");
    assert cusp_trace eq cusp_builtin;
    assert cusp_trace eq expected_cusp[k];

    delete Mk`CuspDimension;
    assert Dimension(Mk) eq expected_total[k];

    // Precision helper must return an integer consistent with dim M_k.
    prec := ComputePrecisionFromHilbertSeries(NN, k);
    assert Type(prec) eq RngIntElt;
    assert prec eq 10 * expected_total[k] + 10;
end for;
