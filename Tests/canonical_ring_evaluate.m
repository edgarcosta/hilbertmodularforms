// Regression: Evaluate(F, v) for v::List and v::SeqEnum must substitute the
// supplied forms into F, not the polynomial F itself
// (bug was EvaluateMonomials([* F *], mons) instead of EvaluateMonomials(v, mons)).
printf "Testing Evaluate of a polynomial at HMFs (List/SeqEnum overloads)...";

F<nu> := QuadraticField(5);
ZF := Integers(F);
prec := 60;
R := GradedRingOfHMFs(F, prec);

// Two independent forms in the same weight-[6,6] space.
M6 := HMFSpace(R, [6, 6]);
B6 := Basis(M6);
assert #B6 ge 2;
f := B6[1];
g := B6[2];

// Weighted polynomial ring in x, y matching the weights of f, g.
P := ConstructWeightedPolynomialRing([* f, g *]);
x := P.1;
y := P.2;

// List overload: the result must use f and g, hence equal f + g.
// On the buggy code this substitutes into [* F *] and returns a polynomial,
// so the comparison against the HMF f + g errors.
assert Evaluate(x + y, [* f, g *]) eq f + g;

// SeqEnum overload delegates to the List overload, so it must behave the same.
assert Evaluate(x + y, [f, g]) eq f + g;

// Coefficients and variable order must be honoured (f, g are independent).
assert Evaluate(2*x + y, [* f, g *]) eq 2*f + g;

return true;
