// Regression test for hilbertmodularforms-1ba.10.
//
// The trace-formula Hilbert series is only implemented for real quadratic
// base fields; for cubic fields it returns non-integral (wrong) dimensions.
// For K = Q(zeta_7)^+ (disc 49) at level (2) the trace series has coefficients
// such as <2, 20/7> and <4, 36/7>, so on the broken code both
//   ComputePrecisionFromHilbertSeries(NN, .)   [CanonicalRing.m: Integers()!Coefficient(...)]
//   CuspDimension(Mk : version := "trace")     [Space.m:        Integers()!Trace(Mk, .)]
// throw "Rational argument is not a whole integer" / "Illegal coercion".
//
// The fix routes degree-not-2 base fields through the built-in dimension, which
// is correct: dim M_2 = 2 (Eis 2, cusp 0) and dim M_4 = 6 (Eis 2, cusp 4),
// matching the arXiv:2501.15719 D=49 level-(2) target.

printf "Testing cubic trace/dimension bypass (Q(zeta_7)^+, level (2))... ";

Q := Rationals();
P<x> := PolynomialRing(Q);
F := NumberField(x^3 - x^2 - 2*x + 1); // Q(zeta_7)^+
ZF := Integers(F);
NN := 2*ZF;
assert Discriminant(ZF) eq 49;

M := GradedRingOfHMFs(F, 1);
M2 := HMFSpace(M, NN, [2, 2, 2]);
M4 := HMFSpace(M, NN, [4, 4, 4]);

// Total dimensions must match the built-in (correct) values.
assert Dimension(M2) eq 2;
assert Dimension(M4) eq 6;

// The trace-version CuspDimension must agree with the built-in one (it now
// falls back to built-in for cubic fields instead of coercing a fraction).
assert CuspDimension(M2 : version := "trace") eq CuspDimension(M2 : version := "builtin");
assert CuspDimension(M4 : version := "trace") eq CuspDimension(M4 : version := "builtin");
assert CuspDimension(M2 : version := "trace") eq 0;
assert CuspDimension(M4 : version := "trace") eq 4;

// Precision must come back as an integer consistent with dim M_B = 10*dim + 10.
assert ComputePrecisionFromHilbertSeries(NN, 2) eq 10*Dimension(M2) + 10;
assert ComputePrecisionFromHilbertSeries(NN, 4) eq 10*Dimension(M4) + 10;
assert ComputePrecisionFromHilbertSeries(NN, 4) eq 70;

printf "Success!\n";
