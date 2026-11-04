// Certifies the stored Q(sqrt17) level-1 ring against the even, trivial-multiplier
// subring of Mayer's literal Thm 6.5.1 presentation over Q. The equations and
// forward and inverse witness maps are stored in:
// Verification/LiteratureEquations/2.2.17.1-1.1-Mayer.m
//
// Keep eval at top level: nesting it inside a procedure crashes the test runner.
t0 := Cputime();
J := LoadStoredCanonicalRing("2.2.17.1-1.1");
R := Generic(J);
assert VariableWeights(R) eq [2,4,4,6,6,6,8];

litfile := "Verification/LiteratureEquations/2.2.17.1-1.1-Mayer.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
S := PolynomialRing(Rationals(), VariableWeights(R));
I, PhiImages, PsiImages, citation := LitData(S, R);
HI := HilbertSeries(I);
HJ := HilbertSeries(J);
assert HI eq HJ;
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt17) level 1: graded-isomorphic over Q to the even, trivial-multiplier subring of %o. [%o s]\n",
  citation, Cputime(t0);
