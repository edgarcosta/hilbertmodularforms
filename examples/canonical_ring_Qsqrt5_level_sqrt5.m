// Certifies the Q(sqrt5) level (sqrt5) ring against the D5 invariants of
// Hirzebruch, LNM 627 (1977), pp.305-310, using c^2 = 5*C.
// This rational model becomes the printed c^2 = C model after scaling c by sqrt(5).

J := LoadStoredCanonicalRing("2.2.5.1-5.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 2, 6, 10, 10];

// Keep eval at top level: nesting it inside a procedure crashes the test runner.
litfile := "Verification/LiteratureEquations/2.2.5.1-5.1-Hirzebruch.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
S := PolynomialRing(Rationals(), VariableWeights(R));
I, PhiImages, PsiImages, citation := LitData(S, R);
assert HilbertSeries(I) eq HilbertSeries(J);
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt5) level (sqrt5): our canonical ring is graded-isomorphic over Q to %o.\n", citation;
