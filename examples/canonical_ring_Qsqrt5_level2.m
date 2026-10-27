// Certifies that the Q(sqrt5) level (2) canonical ring is graded-isomorphic
// over Q to the A4 invariants of Hirzebruch's Gamma(2) ring.
// Stored ring: Verification/CanonicalRingEquations/2.2.5.1-4.1-gl-0.m.
//
// Literature equations and stored witness maps:
// Verification/LiteratureEquations/2.2.5.1-4.1-Hirzebruch.m.
//
// Keep eval at top level: nesting it inside a procedure crashes the test runner.
J := LoadStoredCanonicalRing("2.2.5.1-4.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 2, 6, 12];

litfile := "Verification/LiteratureEquations/2.2.5.1-4.1-Hirzebruch.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
S := PolynomialRing(Rationals(), VariableWeights(R));
I, PhiImages, PsiImages, citation := LitData(S, R);
assert HilbertSeries(I) eq HilbertSeries(J);
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt5) level (2): our canonical ring is graded-isomorphic over Q to %o.\n", citation;
